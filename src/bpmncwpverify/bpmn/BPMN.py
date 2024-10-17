from typing import Optional, List
from abc import ABC


# Base class for all BPMN elements
class BpmnElement:
    def __init__(self, id: str, label: str = "") -> None:
        self.id = id
        self.label = label


# Base class for nodes that can have incoming and outgoing flows
class Node(BpmnElement, ABC):
    def __init__(self, id: str, label: str = "") -> None:
        super().__init__(id, label)
        self.in_flows: List["SequenceFlow"] = []
        self.out_flows: List["SequenceFlow"] = []


# Event classes
class Event(Node, ABC):
    pass


class StartEvent(Event):
    pass


class EndEvent(Event):
    pass


class IntermediateEvent(Event):
    pass


# Activity classes
class Activity(Node, ABC):
    pass


class Task(Activity):
    pass


class SubProcess(Activity):
    pass


# Gateway classes
class GatewayNode(Node, ABC):
    pass


class ExclusiveGatewayNode(GatewayNode):
    pass


class ParallelGatewayNode(GatewayNode):
    def __init__(self, id: str, label: str = "", is_fork: bool = False) -> None:
        super().__init__(id, label)
        self.is_fork = is_fork  # True for fork, False for join


# Flow classes
class Flow(BpmnElement, ABC):
    def __init__(
        self,
        id: str,
        label: str = "",
        from_node: Optional["Node"] = None,
        to_node: Optional["Node"] = None,
    ) -> None:
        super().__init__(id, label)
        self.from_node = from_node
        self.to_node = to_node
        self.seen = False


class SequenceFlow(Flow):
    pass


class MessageFlow(Flow):
    pass


# Process class
class Process(BpmnElement):
    def __init__(self, id: str, label: str = "") -> None:
        super().__init__(id, label)
        self.elements: List[BpmnElement] = []
        self.flows: List[Flow] = []

    def add_element(self, element: BpmnElement) -> None:
        self.elements.append(element)

    def add_flow(self, flow: Flow) -> None:
        self.flows.append(flow)


# BPMN diagram class
class Bpmn:
    def __init__(self) -> None:
        self.process_list: List[Process] = []

    def add_process(self, process: Process) -> None:
        self.process_list.append(process)
