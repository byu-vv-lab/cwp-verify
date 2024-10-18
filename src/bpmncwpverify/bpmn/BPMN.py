from typing import Optional, List, Dict
from abc import ABC
from xml.etree.ElementTree import Element


# Base class for all BPMN elements
class BpmnElement:
    def __init__(self, element: Element) -> None:
        self.element = element
        self.id = element.attrib["id"]
        self.name = element.attrib.get("name")


# Base class for nodes that can have incoming and outgoing flows
class Node(BpmnElement, ABC):
    def __init__(self, element: Element) -> None:
        super().__init__(element)
        self.in_flows: List[Flow] = []
        self.out_flows: List[Flow] = []


# Event classes
class Event(Node, ABC):
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
class Activity(Node, ABC):
    def __init__(self, element: Element):
        super().__init__(element)


class Task(Activity):
    def __init__(self, element: Element):
        super().__init__(element)


class SubProcess(Activity):
    def __init__(self, element: Element):
        super().__init__(element)


# Gateway classes
class GatewayNode(Node, ABC):
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
class Flow(BpmnElement, ABC):
    def __init__(
        self,
        element: Element,
    ) -> None:
        super().__init__(element)
        self.source_node: Optional[Node] = None
        self.target_node: Optional[Node] = None
        self.seen = False


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
        self.graph: Dict[str, List[str]] = {}


class Bpmn:
    def __init__(self) -> None:
        self.processes: List[Process] = []
