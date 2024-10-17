from typing import Optional, List
from abc import ABC


class BpmnElement:
    def __init__(self) -> None:
        pass


class Flow(BpmnElement):
    def __init__(
        self,
        label: str,
        to_node: Optional["Node"] = None,
        from_node: Optional["Node"] = None,
        id: Optional[str] = None,
    ):
        self.id = id
        self.label = label
        self.to_node = to_node
        self.from_node = from_node
        self.seen = False

    def set_to_node(self, to_node: "Node") -> None:
        self.to_node = to_node

    def set_from_node(self, from_node: "Node") -> None:
        self.from_node = from_node


class Msg(BpmnElement):
    def __init__(
        self,
        label: str,
        id: Optional[str],
        to_node: Optional["Node"] = None,
        from_node: Optional["Node"] = None,
    ):
        self.id = id
        self.label = label
        self.to_node = to_node
        self.from_node = from_node
        self.seen = False

    def set_to_node(self, to_node: "Node") -> None:
        self.to_node = to_node

    def set_from_node(self, from_node: "Node") -> None:
        self.from_node = from_node


class Node(BpmnElement):
    def __init__(self, label: str, id: str) -> None:
        self.label = label
        self.id = id
        self.in_flows: List[Flow] = []
        self.out_flows: List[Flow] = []
        self.in_msgs: List[Msg] = []
        self.out_msgs: List[Msg] = []

    def add_out_flow(self, flow: Flow) -> None:
        self.out_flows.append(flow)


class EventNode(Node):
    pass


class ActivityNode(Node):
    pass


class StartNode(Node):
    pass


class GatewayNode(Node):
    pass


class XorGatewayNode(GatewayNode):
    pass


class ParallelGatewayJoinNode(GatewayNode):
    pass


class ParallelGatewayForkNode(GatewayNode):
    pass


class EndNode(Node):
    pass


class IntermediateNode(Node, ABC):
    pass


class MsgIntermediateNode(IntermediateNode):
    pass


class TimerIntermediateNode(IntermediateNode):
    pass


class Process(BpmnElement):
    def __init__(self) -> None:
        self.start_state_list: List[StartNode] = []


class Bpmn(BpmnElement):
    def __init__(self) -> None:
        self.process_list: List[Process] = []

    def add_process(self, process: Process) -> None:
        self.process_list.append(process)
