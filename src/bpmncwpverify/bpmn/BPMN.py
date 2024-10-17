from typing import Optional, List


class BpmnElement:
    def __init__(self, id: str) -> None:
        self.id = id


class Node(BpmnElement):
    def __init__(self, label: str, id: str) -> None:
        super().__init__(id)
        self.label = label
        self.in_flows: List["SequenceFlow"] = []
        self.out_flows: List["SequenceFlow"] = []


# Gateway Node
class GatewayNode(Node):
    pass


class ExclusiveGatewayNode(GatewayNode):
    pass


class ParallelGatewayJoinNode(GatewayNode):
    pass


class ParallelGatewayForkNode(GatewayNode):
    pass


# Activity Node
class Activity(Node):
    pass


class Task(Activity):
    pass


class SubProcess(Activity):
    pass


# Event Node
class Event(Node):
    pass


class StartEvent(Event):
    pass


class EndEvent(Event):
    pass


class IntermediateEvent(Event):
    pass


# Flow
class Flow(BpmnElement):
    def __init__(
        self,
        label: str,
        id: str,
        to_node: Optional["Node"] = None,
        from_node: Optional["Node"] = None,
    ):
        super().__init__(id)
        self.label = label
        self.to_node = to_node
        self.from_node = from_node
        self.seen = False

    def set_to_node(self, to_node: "Node") -> None:
        self.to_node = to_node

    def set_from_node(self, from_node: "Node") -> None:
        self.from_node = from_node


# Specific Flow types
class SequenceFlow(Flow):
    pass


class MessageFlow(Flow):
    pass


class Process(BpmnElement):
    def __init__(self) -> None:
        self.start_event_list: List[StartEvent] = []


class Bpmn:
    def __init__(self) -> None:
        self.bpmn_element_list: List[BpmnElement] = []
        self.flow_list: List[Flow] = []
