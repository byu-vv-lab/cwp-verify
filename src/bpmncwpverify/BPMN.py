from typing import List, Dict
from abc import ABC, abstractmethod
from xml.etree.ElementTree import Element
from defusedxml.ElementTree import parse
from bpmncwpverify.constants import NAMESPACES


###################
# Base class for all BPMN elements
###################
class BpmnElement(ABC):
    def __init__(self, element: Element) -> None:
        self.element = element
        self.id = element.attrib["id"]
        self.name = element.attrib.get("name")

    @abstractmethod
    def accept(self, visitor: "BpmnVisitor") -> None:
        pass


###################
# Base class for nodes that can have incoming and outgoing flows
###################
class Node(BpmnElement):
    def __init__(self, element: Element) -> None:
        super().__init__(element)
        self.in_flows: List[Flow] = []
        self.out_flows: List[Flow] = []


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
        result = visitor.visitStartEvent(self)

        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

        visitor.endVisitStartEvent(self)


class EndEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visitEndEvent(self)

        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

        visitor.endVisitEndEvent(self)


class IntermediateEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visitIntermediateEvent(self)

        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

        visitor.endVisitIntermediateEvent(self)


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
        result = visitor.visitTask(self)

        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

        visitor.endVisitTask(self)


class SubProcess(Activity):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visitSubProcess(self)

        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

        visitor.endVisitSubProcess(self)


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
        result = visitor.visitExclusiveGateway(self)

        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

        visitor.endVisitExclusiveGateway(self)


class ParallelGatewayNode(GatewayNode):
    def __init__(self, element: Element, is_fork: bool = False):
        super().__init__(element)
        self.is_fork = is_fork

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visitParallelGateway(self)

        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

        visitor.endVisitParallelGateway(self)


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


class SequenceFlow(Flow):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visitSequenceFlow(self)
        visitor.endVisitSequenceFlow(self)


class MessageFlow(Flow):
    def __init__(self, element: Element):
        super().__init__(element)

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visitMessageFlow(self)
        visitor.endVisitMessageFlow(self)


###################
# Process class
###################
class Process(BpmnElement):
    def __init__(self, element: Element):
        super().__init__(element)
        self.flows: Dict[str, Flow] = {}
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
        raise ValueError("key not found in either elements or start states")

    def all_items(self) -> Dict[str, Node]:
        return self._elements | self._start_states

    def get_start_states(self) -> Dict[str, StartEvent]:
        return self._start_states

    def accept(self, visitor: "BpmnVisitor") -> None:
        pass


###################
# Bpmn class (building graph from xml happens here)
###################
class Bpmn:
    _TAG_CLASS_MAPPING = {
        "task": Node,
        "startEvent": StartEvent,
        "endEvent": EndEvent,
        "exclusiveGateway": ExclusiveGatewayNode,
        "parallelGateway": ParallelGatewayNode,
    }

    _FLOW_MAPPING = {"sequenceFlow": SequenceFlow}

    def __init__(self) -> None:
        self.processes: List[Process] = []

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
                    process[source_ref].out_flows.append(flow)
                    # update target node's in flows array
                    process[target_ref].in_flows.append(flow)

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

    @staticmethod
    def from_xml(xml_file: str) -> "Bpmn":
        tree = parse(xml_file)
        root = tree.getroot()
        bpmn = Bpmn()
        processes = root.findall("bpmn:process", NAMESPACES)
        for process_element in processes:
            process = bpmn._traverse_process(process_element)
            bpmn.processes.append(process)

        return bpmn


###################
# Bpmn Visitor interface
###################
class BpmnVisitor(ABC):
    @abstractmethod
    def visitStartEvent(self, event: StartEvent) -> bool:
        pass

    @abstractmethod
    def endVisitStartEvent(self, event: StartEvent) -> None:
        pass

    @abstractmethod
    def visitEndEvent(self, event: EndEvent) -> bool:
        pass

    @abstractmethod
    def endVisitEndEvent(self, event: EndEvent) -> None:
        pass

    @abstractmethod
    def visitIntermediateEvent(self, event: IntermediateEvent) -> bool:
        pass

    @abstractmethod
    def endVisitIntermediateEvent(self, event: IntermediateEvent) -> None:
        pass

    @abstractmethod
    def visitTask(self, task: Task) -> bool:
        pass

    @abstractmethod
    def endVisitTask(self, task: Task) -> None:
        pass

    @abstractmethod
    def visitSubProcess(self, subprocess: SubProcess) -> bool:
        pass

    @abstractmethod
    def endVisitSubProcess(self, subprocess: SubProcess) -> None:
        pass

    @abstractmethod
    def visitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> bool:
        pass

    @abstractmethod
    def endVisitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    @abstractmethod
    def visitParallelGateway(self, gateway: ParallelGatewayNode) -> bool:
        pass

    @abstractmethod
    def endVisitParallelGateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    @abstractmethod
    def visitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    @abstractmethod
    def endVisitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    @abstractmethod
    def visitMessageFlow(self, flow: MessageFlow) -> None:
        pass

    @abstractmethod
    def endVisitMessageFlow(self, flow: MessageFlow) -> None:
        pass
