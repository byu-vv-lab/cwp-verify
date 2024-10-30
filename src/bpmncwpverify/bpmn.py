from typing import List, Dict
from abc import ABC, abstractmethod
from xml.etree.ElementTree import Element
from returns.result import Failure, Result, Success
from defusedxml.ElementTree import parse
from bpmncwpverify.constants import NAMESPACES

from bpmncwpverify.error import (
    Error,
    NotImplementedError as NoImplemntation,
    BpmnNodeNotFound,
)


###################
# Base class for all BPMN elements
###################
class BpmnElement(ABC):
    def __init__(self, element: Element) -> None:
        self.element = element
        self.id = element.attrib["id"]
        self.name = element.attrib.get("name")


###################
# Base class for nodes that can have incoming and outgoing flows
###################
class Node(BpmnElement):
    def __init__(self, element: Element) -> None:
        super().__init__(element)
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

    def visit_out_flows(self, visitor: "BpmnVisitor", result: bool) -> None:
        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

    @abstractmethod
    def accept(self, visitor: "BpmnVisitor") -> None:
        raise NoImplemntation(self.accept.__name__)


###################
# Event classes
###################
class Event(Node):
    def __init__(self, element: Element):
        super().__init__(element)


class StartEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)
        # TODO: add in_msgs attribute

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_start_event(self)
        self.visit_out_flows(visitor, result)
        visitor.end_visit_start_event(self)


class EndEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_end_event(self)
        self.visit_out_flows(visitor, result)
        visitor.end_visit_end_event(self)


class IntermediateEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_intermediate_event(self)
        self.visit_out_flows(visitor, result)
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
        self.visit_out_flows(visitor, result)
        visitor.end_visit_task(self)


class SubProcess(Activity):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_sub_process(self)
        self.visit_out_flows(visitor, result)
        visitor.end_visit_sub_process(self)


###################
# Gateway classes
###################
class GatewayNode(Node, ABC):
    def __init__(self, element: Element):
        super().__init__(element)


class ExclusiveGatewayNode(GatewayNode):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_exclusive_gateway(self)
        self.visit_out_flows(visitor, result)
        visitor.end_visit_exclusive_gateway(self)


class ParallelGatewayNode(GatewayNode):
    def __init__(self, element: Element, is_fork: bool = False):
        super().__init__(element)
        self.is_fork = is_fork

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_parallel_gateway(self)
        self.visit_out_flows(visitor, result)
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

    @abstractmethod
    def accept(self, visitor: "BpmnVisitor") -> None:
        pass


class SequenceFlow(Flow):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_sequence_flow(self)
        if not self.is_leaf:
            self.target_node.accept(visitor)
        visitor.end_visit_sequence_flow(self)


class MessageFlow(Flow):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_message_flow(self)
        if not self.is_leaf:
            self.target_node.accept(visitor)
        visitor.end_visit_message_flow(self)


###################
# Process class
###################
class Process(BpmnElement):
    def __init__(self, element: Element):
        super().__init__(element)
        self.flows: Dict[str, SequenceFlow] = {}
        self._elements: Dict[str, Node] = {}
        self._start_states: Dict[str, StartEvent] = {}

    def __setitem__(self, key: str, node: Node) -> None:
        if isinstance(node, StartEvent):
            self._start_states[key] = node
        else:
            self._elements[key] = node

    def __getitem__(self, key: str) -> Node:
        if key in self._elements:
            return self._elements[key]
        elif key in self._start_states:
            return self._start_states[key]
        raise BpmnNodeNotFound(key)

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
    _TAG_CLASS_MAPPING = {
        "task": Task,
        "startEvent": StartEvent,
        "endEvent": EndEvent,
        "exclusiveGateway": ExclusiveGatewayNode,
        "parallelGateway": ParallelGatewayNode,
    }

    _FLOW_MAPPING = {"sequenceFlow": SequenceFlow}

    def __init__(self) -> None:
        self.processes: List[Process] = []

    def _set_leaf_flows(self) -> None:
        visited = set()

        def dfs(node: Node) -> None:
            nonlocal visited

            visited.add(node)
            for flow in node.out_flows:
                if flow.target_node in visited:
                    flow.is_leaf = True
                else:
                    dfs(flow.target_node)

        for process in self.processes:
            for node in process.get_start_states().values():
                dfs(node)

    def __str__(self) -> str:
        build_arr: List[str] = []
        for process in self.processes:
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

    def _build_graph(self, process: Process) -> None:
        for element_id, element_instance in process.all_items().items():
            for outgoing in element_instance.element.findall(
                "bpmn:outgoing", NAMESPACES
            ):
                flow_id = outgoing.text
                if not flow_id:
                    raise Exception("flow id is None")
                flow = process.flows.get(flow_id.strip())
                if flow is not None:
                    source_ref = flow.element.attrib["sourceRef"]
                    target_ref = flow.element.attrib["targetRef"]

                    # update flow's source_node
                    flow.source_node = process[source_ref]
                    # update flow's target_node
                    flow.target_node = process[target_ref]

                    # update source node's out flows array
                    process[source_ref].add_out_flow(flow)
                    # update target node's in flows array
                    process[target_ref].add_in_flow(flow)

    def _traverse_messages(self, root: Element) -> None:
        all_elements = {
            id: element
            for process in self.processes
            for id, element in process.all_items().items()
        }
        self.collab = root.find("bpmn:collaboration", NAMESPACES)
        if self.collab is not None:
            for msg in self.collab.findall("bpmn:messageFlow", NAMESPACES):
                id = msg.get("id")
                name = msg.get("name")
                if name is None:
                    name = id
                message = MessageFlow(msg)
                sourceRef = msg.get("sourceRef")
                targetRef = msg.get("targetRef")
                if not (sourceRef and targetRef):
                    raise Exception(
                        "source ref or target ref not included with message"
                    )
                fromNode = all_elements[sourceRef]
                toNode = all_elements[targetRef]
                message.target_node = toNode
                message.source_node = fromNode
                fromNode.add_out_msg(message)
                toNode.add_in_msg(message)

    def _traverse_process(self, process_element: Element) -> Process:
        process = Process(process_element)

        def get_tag_name(element: Element) -> str:
            return element.tag.partition("}")[2]

        for element in process_element:
            tag_name = get_tag_name(element)
            if tag_name in Bpmn._TAG_CLASS_MAPPING:
                element_class = Bpmn._TAG_CLASS_MAPPING[tag_name]
                element_instance = element_class(element)
                element_id = element_instance.id
                process[element_id] = element_instance

            elif tag_name in Bpmn._FLOW_MAPPING:
                flow_id = element.attrib["id"]
                element_class = Bpmn._FLOW_MAPPING[tag_name]
                element_instance = element_class(element)
                process.flows[flow_id] = element_instance

        self._build_graph(process)

        return process

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_bpmn(self)
        for process in self.processes:
            process.accept(visitor)
        visitor.end_visit_bpmn(self)

    def generate_graph_viz(self) -> None:
        from bpmncwpverify.graph_viz_visitor import GraphVizVisitor

        for process in range(len(self.processes)):
            graph_viz_visitor = GraphVizVisitor(process + 1)

            self.accept(graph_viz_visitor)

            graph_viz_visitor.dot.render("graphs/bpmn_graph.gv", format="png")

    def generate_promela(self) -> None:
        from bpmncwpverify.promela_gen_visitor import PromelaGenVisitor

        visitor = PromelaGenVisitor()
        self.accept(visitor)

    @staticmethod
    def from_xml(xml_file: str) -> Result["Bpmn", Error]:
        try:
            tree = parse(xml_file)
            root = tree.getroot()
            bpmn = Bpmn()
            processes = root.findall("bpmn:process", NAMESPACES)
            for process_element in processes:
                process = bpmn._traverse_process(process_element)
                bpmn.processes.append(process)

            bpmn._traverse_messages(root)
            bpmn._set_leaf_flows()
            return Success(bpmn)
        except Exception as e:
            return Failure(e)


###################
# Bpmn Visitor interface
###################
class BpmnVisitor(ABC):
    @abstractmethod
    def visit_start_event(self, event: StartEvent) -> bool:
        pass

    @abstractmethod
    def end_visit_start_event(self, event: StartEvent) -> None:
        pass

    @abstractmethod
    def visit_end_event(self, event: EndEvent) -> bool:
        pass

    @abstractmethod
    def end_visit_end_event(self, event: EndEvent) -> None:
        pass

    @abstractmethod
    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        pass

    @abstractmethod
    def end_visit_intermediate_event(self, event: IntermediateEvent) -> None:
        pass

    @abstractmethod
    def visit_task(self, task: Task) -> bool:
        pass

    @abstractmethod
    def end_visit_task(self, task: Task) -> None:
        pass

    @abstractmethod
    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        pass

    @abstractmethod
    def end_visit_sub_process(self, subprocess: SubProcess) -> None:
        pass

    @abstractmethod
    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        pass

    @abstractmethod
    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        pass

    @abstractmethod
    def end_visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    @abstractmethod
    def visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    @abstractmethod
    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    @abstractmethod
    def visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    @abstractmethod
    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    @abstractmethod
    def visit_process(self, process: Process) -> None:
        pass

    @abstractmethod
    def end_visit_process(self, process: Process) -> None:
        pass

    @abstractmethod
    def visit_bpmn(self, bpmn: Bpmn) -> None:
        pass

    @abstractmethod
    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        pass
