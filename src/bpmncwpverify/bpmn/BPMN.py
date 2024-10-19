from typing import Optional, List, Dict, Tuple
from xml.etree.ElementTree import Element


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
        self.in_flows: List[SequenceFlow] = []
        self.out_flows: List[SequenceFlow] = []


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
        self._elements: Dict[str, Node] = {}
        self._start_states: Dict[str, StartEvent] = {}
        self.flows: Dict[str, SequenceFlow] = {}
        self.adj_list: Dict[str, List[str]] = {}

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

    def items(self) -> List[Tuple[str, Node]]:
        return list(self._elements.items()) + list(self._start_states.items())


class Bpmn:
    def __init__(self) -> None:
        self.processes: List[Process] = []
