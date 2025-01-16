from __future__ import annotations
from typing import List, Dict, Union, cast
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import State
from returns.result import Result
from abc import abstractmethod
from returns.pipeline import is_successful
from returns.functions import not_
from bpmncwpverify.core.error import (
    BpmnStructureError,
    Error,
)
import bpmncwpverify.visitors.bpmnvisitor as bpmnvisitor
import bpmncwpverify.builder.process_builder as pb
import bpmncwpverify.builder.bpmn_builder as bb
import bpmncwpverify.visitors.bpmn_graph_visitor as gv
import bpmncwpverify.visitors.bpmn_promela_visitor as bpv

BPMN_XML_NAMESPACE = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}


###################
# Base class for all BPMN elements
###################
class BpmnElement:
    __slots__ = ["element", "name", "id"]

    def __init__(self, element: Element) -> None:
        self.element = element
        id = element.attrib.get("id")
        if not id:
            raise Exception("Id cannot be None")

        self.id = id

        self.name: str = element.attrib.get("name", self.id)


###################
# Base class for nodes that can have incoming and outgoing flows
###################
class Node(BpmnElement):
    __slots__ = [
        "out_flows",
        "in_flows",
        "in_msgs",
        "out_msgs",
        "message_event_definition",
        "message_timer_definition",
    ]

    def __init__(self, element: Element) -> None:
        super().__init__(element)

        message_event_def = element.find(
            "bpmn:messageEventDefinition", BPMN_XML_NAMESPACE
        )
        self.message_event_definition: str = (
            message_event_def.attrib.get("id", "")
            if message_event_def is not None
            else ""
        )

        timer_event_def = element.find("bpmn:timerEventDefinition", BPMN_XML_NAMESPACE)
        self.message_timer_definition: str = (
            timer_event_def.attrib.get("id", "") if timer_event_def is not None else ""
        )

        self.out_flows: List[SequenceFlow] = []
        self.in_flows: List[SequenceFlow] = []
        self.in_msgs: List[MessageFlow] = []
        self.out_msgs: List[MessageFlow] = []

    def add_out_flow(self, flow: "SequenceFlow") -> None:
        self.out_flows.append(flow)

    def add_in_flow(self, flow: "SequenceFlow") -> None:
        self.in_flows.append(flow)

    def add_out_msg(self, flow: "MessageFlow") -> None:
        self.out_msgs.append(flow)

    def add_in_msg(self, flow: "MessageFlow") -> None:
        self.in_msgs.append(flow)

    def traverse_outflows_if_result(
        self, visitor: "bpmnvisitor.BpmnVisitor", result: bool
    ) -> None:
        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        pass

    @staticmethod
    @abstractmethod
    def from_xml(element: Element) -> "Node":
        pass


###################
# Event classes
###################
class Event(Node):
    pass


class StartEvent(Event):
    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        result = visitor.visit_start_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_start_event(self)

    @staticmethod
    def from_xml(element: Element) -> "StartEvent":
        return StartEvent(element)


class EndEvent(Event):
    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        result = visitor.visit_end_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_end_event(self)

    @staticmethod
    def from_xml(element: Element) -> "EndEvent":
        return EndEvent(element)


class IntermediateEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)
        tag = element.tag.partition("}")[2]
        self.type = "catch" if "Catch" in tag else "throw" if "Throw" in tag else "send"

    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        result = visitor.visit_intermediate_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_intermediate_event(self)

    @staticmethod
    def from_xml(element: Element) -> "IntermediateEvent":
        return IntermediateEvent(element)


###################
# Activity classes
###################
class Task(Node):
    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        result = visitor.visit_task(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_task(self)

    @staticmethod
    def from_xml(element: Element) -> "Task":
        return Task(element)


###################
# Gateway classes
###################
class GatewayNode(Node):
    pass


class ExclusiveGatewayNode(GatewayNode):
    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        result = visitor.visit_exclusive_gateway(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_exclusive_gateway(self)

    @staticmethod
    def from_xml(element: Element) -> "ExclusiveGatewayNode":
        return ExclusiveGatewayNode(element)


class ParallelGatewayNode(GatewayNode):
    def __init__(self, element: Element, is_fork: bool = False):
        super().__init__(element)
        self.is_fork = is_fork

    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        result = visitor.visit_parallel_gateway(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_parallel_gateway(self)

    def add_out_flow(self, flow: "SequenceFlow") -> None:
        super().add_out_flow(flow)
        if len(self.out_flows) > 1:
            self.is_fork = True

    @staticmethod
    def from_xml(element: Element) -> "ParallelGatewayNode":
        return ParallelGatewayNode(element)


###################
# Flow classes
###################
class Flow(BpmnElement):
    __slots__ = ["source_node", "target_node", "is_leaf"]

    def __init__(
        self,
        element: Element,
    ) -> None:
        super().__init__(element)
        self.source_node: Node
        self.target_node: Node
        self.is_leaf: bool = False

    @staticmethod
    @abstractmethod
    def from_xml(element: Element) -> "Flow":
        pass


class SequenceFlow(Flow):
    __slots__ = ["expression"]

    def __init__(self, element: Element):
        super().__init__(element)
        self.expression: str = ""

    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        if visitor.visit_sequence_flow(self) and not self.is_leaf:
            self.target_node.accept(visitor)
        visitor.end_visit_sequence_flow(self)

    @staticmethod
    def from_xml(element: Element) -> "SequenceFlow":
        return SequenceFlow(element)


class MessageFlow(Flow):
    @staticmethod
    def from_xml(element: Element) -> "MessageFlow":
        return MessageFlow(element)


###################
# Process class
###################
class Process(BpmnElement):
    def __init__(self, element: Element):
        super().__init__(element)
        self._flows: Dict[str, SequenceFlow] = {}
        self._elements: Dict[str, Node] = {}
        self._start_states: Dict[str, StartEvent] = {}

    def __setitem__(self, key: str, item: BpmnElement) -> None:
        if isinstance(item, StartEvent):
            self._start_states[key] = item
        elif isinstance(item, SequenceFlow):
            self._flows[key] = item
        elif isinstance(item, Node):
            self._elements[key] = item

    def __getitem__(self, key: str) -> Union[Node, Flow]:
        if key in self._elements:
            return self._elements[key]
        elif key in self._start_states:
            return self._start_states[key]
        elif key in self._flows:
            return self._flows[key]
        raise Exception(
            BpmnStructureError(key, "Key not found in any of the processe's elements")
        )

    def get_flows(self) -> Dict[str, SequenceFlow]:
        return self._flows

    def all_items(self) -> Dict[str, Node]:
        return self._elements | self._start_states

    def get_start_states(self) -> Dict[str, StartEvent]:
        return self._start_states

    @staticmethod
    def from_xml(
        element: Element,
        symbol_table: State,
    ) -> Result["Process", Error]:
        builder = pb.ProcessBuilder(element, symbol_table)

        for sub_element in element:
            tag = sub_element.tag.partition("}")[2]

            result = get_element_type(tag)

            class_object = result.from_xml(sub_element)
            builder = builder.with_element(class_object)

        for seq_flow in element.findall("bpmn:sequenceFlow", BPMN_XML_NAMESPACE):
            builder = builder.with_process_flow(
                seq_flow.attrib["id"],
                seq_flow.attrib["sourceRef"],
                seq_flow.attrib["targetRef"],
                seq_flow.attrib.get("name", ""),
            )

        return cast(Result[Process, Error], builder.build())

    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        visitor.visit_process(self)
        for start_event in self.get_start_states().values():
            start_event.accept(visitor)
        visitor.end_visit_process(self)


###################
# Function that maps tag name to its respective builder function
###################
def get_element_type(tag: str) -> Union[type[SequenceFlow], type[Node]]:
    mapping: Dict[str, Union[type[SequenceFlow], type[Node]]] = {
        "task": Task,
        "startEvent": StartEvent,
        "endEvent": EndEvent,
        "exclusiveGateway": ExclusiveGatewayNode,
        "parallelGateway": ParallelGatewayNode,
        "sendTask": IntermediateEvent,
        "intermediateCatchEvent": IntermediateEvent,
        "intermediateThrowEvent": IntermediateEvent,
        "sequenceFlow": SequenceFlow,
    }

    result = mapping.get(tag) or (
        mapping.get("task") if "task" in tag.lower() else None
    )

    assert result

    return result


###################
# Bpmn class (building graph from xml happens here)
###################
class Bpmn:
    def __init__(self) -> None:
        self.processes: Dict[str, Process] = {}
        self.id_to_element: Dict[str, BpmnElement] = {}  # Maps ids to elements
        self.inter_process_msgs: Dict[str, MessageFlow] = {}

    def store_element(self, element: BpmnElement) -> None:
        self.id_to_element[element.id] = element

    def get_element_from_id_mapping(self, key: str) -> BpmnElement:
        return self.id_to_element[key]

    def add_inter_process_msg(self, msg: MessageFlow) -> None:
        self.inter_process_msgs[msg.id] = msg

    def accept(self, visitor: "bpmnvisitor.BpmnVisitor") -> None:
        visitor.visit_bpmn(self)
        for process in self.processes.values():
            process.accept(visitor)
        visitor.end_visit_bpmn(self)

    def generate_graph_viz(self) -> None:
        for process in range(len(self.processes)):
            graph_viz_visitor = gv.GraphVizVisitor(process + 1)

            self.accept(graph_viz_visitor)

            graph_viz_visitor.dot.render("graphs/bpmn_graph.gv", format="png")  # type: ignore[unused-ignore]

    def generate_promela(self) -> str:
        promela_visitor = bpv.PromelaGenVisitor()

        self.accept(promela_visitor)

        return str(promela_visitor)

    @staticmethod
    def from_xml(root: Element, symbol_table: State) -> Result["Bpmn", Error]:
        ##############
        # Build and add processes
        ##############
        processes = root.findall("bpmn:process", BPMN_XML_NAMESPACE)
        bpmn_builder = bb.BpmnBuilder()
        for process_element in processes:
            process = Process.from_xml(process_element, symbol_table)
            if not_(is_successful)(process):
                return cast(Result[Bpmn, Error], process)
            bpmn_builder = bpmn_builder.with_process(process.unwrap())

        ##############
        # Build and add messages
        ##############
        collab = root.find("bpmn:collaboration", BPMN_XML_NAMESPACE)
        if collab is not None:
            # TODO: write test for messages in the bpmn diagram
            bpmn_builder = bpmn_builder.with_process_elements()
            for msg_flow in collab.findall("bpmn:messageFlow", BPMN_XML_NAMESPACE):
                source_ref, target_ref = (
                    msg_flow.get("sourceRef"),
                    msg_flow.get("targetRef"),
                )

                message = MessageFlow.from_xml(msg_flow)

                assert source_ref and target_ref

                bpmn_builder = bpmn_builder.with_message(
                    message, source_ref, target_ref
                )

        return cast(Result[Bpmn, Error], bpmn_builder.build())
