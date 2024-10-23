from typing import List, Dict
from xml.etree.ElementTree import Element
from defusedxml.ElementTree import parse

################
# Constants
################
from bpmncwpverify.constants import NAMESPACES

################


# Base class for all BPMN elements
class BpmnElement:
    def __init__(self, element: Element) -> None:
        self.element = element
        self.id = element.attrib["id"]
        self.name = element.attrib.get("name")


# Base class for nodes that can have incoming and outgoing flows
class Node(BpmnElement):
    def __init__(self, element: Element) -> None:
        super().__init__(element)
        self.in_flows: List[Flow] = []
        self.out_flows: List[Flow] = []


# Event classes
class Event(Node):
    def __init__(self, element: Element):
        super().__init__(element)


class StartEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)


class EndEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)


class IntermediateEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)


# Activity classes
class Activity(Node):
    def __init__(self, element: Element):
        super().__init__(element)


class Task(Activity):
    def __init__(self, element: Element):
        super().__init__(element)


class SubProcess(Activity):
    def __init__(self, element: Element):
        super().__init__(element)


# Gateway classes
class GatewayNode(Node):
    def __init__(self, element: Element):
        super().__init__(element)


class ExclusiveGatewayNode(GatewayNode):
    def __init__(self, element: Element):
        super().__init__(element)


class ParallelGatewayNode(GatewayNode):
    def __init__(self, element: Element, is_fork: bool = False):
        super().__init__(element)
        self.is_fork = is_fork


# Flow classes
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


class MessageFlow(Flow):
    def __init__(self, element: Element):
        super().__init__(element)


# Process class
class Process(BpmnElement):
    def __init__(self, element: Element):
        super().__init__(element)
        self.elements: Dict[str, Node] = {}
        self.flows: Dict[str, Flow] = {}


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

    def __repr__(self) -> str:
        build_arr: List[str] = []
        for process in self.processes:
            build_arr.append(f"Process ID: {process.id}, Name: {process.name}")
            for element_id, element in process.elements.items():
                build_arr.append(f"  Element ID: {element_id}, Name: {element.name}")
                build_arr.append("    Outgoing to:")
                for flow in element.out_flows:
                    target_element = process.elements.get(flow.target_node.id)
                    target_name = target_element.name if target_element else "Unknown"
                    build_arr.append(
                        f"      Element ID: {flow.target_node.id}, Name: {target_name}"
                    )
            build_arr.append("\n")

        return "\n".join(build_arr)

    def _build_graph(self, process: Process) -> None:
        for element_id, element_instance in process.elements.items():
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
                    flow.source_node = process.elements[source_ref]
                    # update flow's target_node
                    flow.target_node = process.elements[target_ref]

                    # update source node's out flows array
                    process.elements[source_ref].out_flows.append(flow)
                    # update target node's in flows array
                    process.elements[target_ref].in_flows.append(flow)

    def _traverse_process(self, process_element: Element) -> Process:
        process = Process(process_element)

        for element in process_element:
            tag_local = element.tag.partition("}")[2]
            if tag_local in Bpmn._TAG_CLASS_MAPPING:
                element_class = Bpmn._TAG_CLASS_MAPPING[tag_local]
                element_instance = element_class(element)
                element_id = element_instance.id
                process.elements[element_id] = element_instance

            elif tag_local in Bpmn._FLOW_MAPPING:
                flow_id = element.attrib["id"]
                element_class = Bpmn._FLOW_MAPPING[tag_local]
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
