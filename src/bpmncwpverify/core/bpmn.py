from typing import List, Dict, Union
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import SymbolTable
from returns.result import Failure, Result
from defusedxml.ElementTree import parse
from bpmncwpverify.constants import NAMESPACES
from bpmncwpverify.error import (
    Error,
    BpmnNodeNotFound,
)


###################
# Base class for all BPMN elements
###################
class BpmnElement:
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
    def __init__(self, element: Element) -> None:
        super().__init__(element)

        message_event_def = element.find("bpmn:messageEventDefinition", NAMESPACES)
        self.message_event_definition: str = (
            message_event_def.attrib.get("id", "")
            if message_event_def is not None
            else ""
        )

        timer_event_def = element.find("bpmn:timerEventDefinition", NAMESPACES)
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

    def traverse_outflows_if_result(self, visitor: "BpmnVisitor", result: bool) -> None:
        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

    def accept(self, visitor: "BpmnVisitor") -> None:
        pass


###################
# Event classes
###################
class Event(Node):
    def __init__(self, element: Element):
        super().__init__(element)


class StartEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_start_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_start_event(self)


class EndEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_end_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_end_event(self)


class IntermediateEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)
        tag = element.tag.partition("}")[2]
        self.type = "catch" if "Catch" in tag else "throw" if "Throw" in tag else "send"

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_intermediate_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_intermediate_event(self)


###################
# Activity classes
###################
class Activity(Node):
    def __init__(self, element: Element):
        super().__init__(element)


class Task(Activity):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_task(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_task(self)


class SubProcess(Activity):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_sub_process(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_sub_process(self)


###################
# Gateway classes
###################
class GatewayNode(Node):
    def __init__(self, element: Element):
        super().__init__(element)


class ExclusiveGatewayNode(GatewayNode):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_exclusive_gateway(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_exclusive_gateway(self)


class ParallelGatewayNode(GatewayNode):
    def __init__(self, element: Element, is_fork: bool = False):
        super().__init__(element)
        self.is_fork = is_fork

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_parallel_gateway(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_parallel_gateway(self)

    def add_out_flow(self, flow: "SequenceFlow") -> None:
        super().add_out_flow(flow)
        if len(self.out_flows) > 1:
            self.is_fork = True


###################
# Flow classes
###################
class Flow(BpmnElement):
    def __init__(
        self,
        element: Element,
    ) -> None:
        super().__init__(element)
        self.source_node: Node
        self.target_node: Node
        self.is_leaf: bool = False


class SequenceFlow(Flow):
    def __init__(self, element: Element):
        super().__init__(element)
        self.expression: str = ""

    def accept(self, visitor: "BpmnVisitor") -> None:
        if visitor.visit_sequence_flow(self):
            self.target_node.accept(visitor)
        visitor.end_visit_sequence_flow(self)


class MessageFlow(Flow):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        if visitor.visit_message_flow(self):
            self.target_node.accept(visitor)
        visitor.end_visit_message_flow(self)


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
        # TODO: Make a custom error here:
        raise Exception(BpmnNodeNotFound(key))

    def get_flows(self) -> Dict[str, SequenceFlow]:
        return self._flows

    def all_items(self) -> Dict[str, Node]:
        return self._elements | self._start_states

    def get_start_states(self) -> Dict[str, StartEvent]:
        return self._start_states

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_process(self)
        for start_event in self.get_start_states().values():
            start_event.accept(visitor)
        visitor.end_visit_process(self)


###################
# Bpmn class (building graph from xml happens here)
###################
class Bpmn:
    _MSG_MAPPING = {"messageFlow": MessageFlow}

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

    def __str__(self) -> str:
        build_arr: List[str] = []
        for process in self.processes.values():
            build_arr.append(f"Process ID: {process.id}, Name: {process.name}")
            for element_id, element in process.all_items().items():
                build_arr.append(f"  Element ID: {element_id}, Name: {element.name}")
                build_arr.append("    Outgoing to:")
                for flow in element.out_flows:
                    target_element = process.all_items().get(flow.target_node.id)
                    target_name = target_element.name if target_element else "Unknown"
                    build_arr.append(
                        f"      Element ID: {flow.target_node.id}, Name: {target_name}"
                    )
            build_arr.append("\n")

        return "\n".join(build_arr)

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_bpmn(self)
        for process in self.processes.values():
            process.accept(visitor)
        visitor.end_visit_bpmn(self)

    def generate_graph_viz(self) -> None:
        from bpmncwpverify.visitors.bpmn_graph_visitor import GraphVizVisitor

        for process in range(len(self.processes)):
            graph_viz_visitor = GraphVizVisitor(process + 1)

            self.accept(graph_viz_visitor)

            graph_viz_visitor.dot.render("graphs/bpmn_graph.gv", format="png")

    def generate_promela(self) -> str:
        from bpmncwpverify.visitors.bpmn_promela_visitor import PromelaGenVisitor

        promela_visitor = PromelaGenVisitor()

        self.accept(promela_visitor)

        return str(promela_visitor)

    @staticmethod
    def from_xml(xml_file: str, symbol_table: SymbolTable) -> Result["Bpmn", Error]:
        from bpmncwpverify.builder.bpmn_builder import BpmnBuilder

        try:
            tree = parse(xml_file)
            root = tree.getroot()
            builder = BpmnBuilder()
            processes = root.findall("bpmn:process", NAMESPACES)
            for process_element in processes:
                builder.add_process(process_element, symbol_table)

            collab = root.find("bpmn:collaboration", NAMESPACES)
            if collab is not None:
                for msg_flow in collab.findall("bpmn:messageFlow", NAMESPACES):
                    builder.add_message(msg_flow)

            return builder.build()
        except Exception as e:
            return Failure(e)


###################
# Bpmn Visitor interface
###################
class BpmnVisitor:
    def visit_start_event(self, event: StartEvent) -> bool:
        return True

    def end_visit_start_event(self, event: StartEvent) -> None:
        pass

    def visit_end_event(self, event: EndEvent) -> bool:
        return True

    def end_visit_end_event(self, event: EndEvent) -> None:
        pass

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        return True

    def end_visit_intermediate_event(self, event: IntermediateEvent) -> None:
        pass

    def visit_task(self, task: Task) -> bool:
        return True

    def end_visit_task(self, task: Task) -> None:
        pass

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        return True

    def end_visit_sub_process(self, subprocess: SubProcess) -> None:
        pass

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def end_visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return True

    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return True

    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def visit_process(self, process: Process) -> bool:
        return True

    def end_visit_process(self, process: Process) -> None:
        pass

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        pass
