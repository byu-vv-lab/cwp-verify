from typing import Optional, List
from abc import ABC, abstractmethod
import xml.etree.ElementTree as ET


class BpmnVisitor(ABC):
    @abstractmethod
    def visit_process(self, element: "Process") -> None:
        pass

    @abstractmethod
    def visit_flow(self, element: "Flow") -> None:
        pass

    @abstractmethod
    def visit_msg(self, element: "Msg") -> None:
        pass

    @abstractmethod
    def visit_activity_node(self, element: "ActivityNode") -> None:
        pass

    @abstractmethod
    def visit_start_node(self, element: "StartNode") -> None:
        pass

    @abstractmethod
    def visit_xor_gateway_node(self, element: "XorGatewayNode") -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway_join_node(
        self, element: "ParallelGatewayJoinNode"
    ) -> None:
        pass

    @abstractmethod
    def visit_gateway_node(self, element: "GatewayNode") -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway_fork_node(
        self, element: "ParallelGatewayForkNode"
    ) -> None:
        pass

    @abstractmethod
    def visit_end_node(self, element: "EndNode") -> None:
        pass

    @abstractmethod
    def visit_event_node(self, element: "EventNode") -> None:
        pass

    @abstractmethod
    def visit_msg_intermediate_node(self, element: "MsgIntermediateNode") -> None:
        pass

    @abstractmethod
    def visit_timer_intermediate_node(self, element: "TimerIntermediateNode") -> None:
        pass

    @abstractmethod
    def visit_model(self, element: "Model") -> None:
        pass


class BpmnElement:
    def __init__(self) -> None:
        pass


class Label(BpmnElement):
    def __init__(self, text: str):
        self.text = text

    def __repr__(self) -> str:
        return self.text


class Flow(BpmnElement):
    def __init__(
        self,
        label: str,
        to_node: Optional["Node"] = None,
        from_node: Optional["Node"] = None,
        id: Optional[str] = None,
    ):
        self.label = label
        self.to_node = to_node
        self.from_node = from_node
        self.id = id
        self.seen = False

    def set_to_node(self, to_node: "Node") -> None:
        self.to_node = to_node

    def set_from_node(self, from_node: "Node") -> None:
        self.from_node = from_node

    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_flow(self)


class Msg(BpmnElement):
    def __init__(
        self,
        label: str,
        to_node: Optional["Node"] = None,
        from_node: Optional["Node"] = None,
        id: Optional[str] = None,
    ):
        self.label = label
        self.to_node = to_node
        self.from_node = from_node
        self.id = id
        self.seen = False

    def set_to_node(self, to_node: "Node") -> None:
        self.to_node = to_node

    def set_from_node(self, from_node: "Node") -> None:
        self.from_node = from_node

    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_msg(self)


class Node(BpmnElement):
    def __init__(
        self,
        label: Label = Label("Empty"),
        in_flows: Optional[List[Flow]] = None,
        out_flows: Optional[List[Flow]] = None,
        in_msgs: Optional[List[Msg]] = None,
        out_msgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        self.in_flows = in_flows if in_flows is not None else []
        self.out_flows = out_flows if out_flows is not None else []
        self.in_msgs = in_msgs if in_msgs is not None else []
        self.out_msgs = out_msgs if out_msgs is not None else []
        self.label = label
        self.seen = False
        self.id = id

    def set_out_flows(self, out_flows: List[Flow]) -> None:
        self.out_flows = out_flows

    def add_out_flow(self, flow: Flow) -> None:
        self.out_flows.append(flow)

    def add_out_msg(self, msg: Msg) -> None:
        self.out_msgs.append(msg)

    def add_in_flow(self, flow: Flow) -> None:
        self.in_flows.append(flow)

    def add_in_msg(self, msg: Msg) -> None:
        self.in_msgs.append(msg)

    def accept(self, visitor: BpmnVisitor) -> None:
        pass

    def __repr__(self) -> str:
        return "Name: %s \n\tInFlows: %s \n\tOutFlows: %s\n\tID: %s" % (
            str(self.label),
            str(self.in_flows),
            str(self.out_flows),
            str(self.id),
        )


class EventNode(Node):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_event_node(self)


class ActivityNode(Node):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_activity_node(self)


class StartNode(Node):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_start_node(self)


class GatewayNode(Node):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_gateway_node(self)


class XorGatewayNode(GatewayNode):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_xor_gateway_node(self)


class ParallelGatewayJoinNode(GatewayNode):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_parallel_gateway_join_node(self)


class ParallelGatewayForkNode(GatewayNode):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_parallel_gateway_fork_node(self)


class EndNode(Node):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_end_node(self)


class IntermediateNode(Node, ABC):
    pass


class MsgIntermediateNode(IntermediateNode):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_msg_intermediate_node(self)


class TimerIntermediateNode(IntermediateNode):
    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_timer_intermediate_node(self)


class Process(BpmnElement):
    def __init__(self, name: str, start_state_list: Optional[List[StartNode]] = None):
        self.start_state_list = start_state_list if start_state_list is not None else []
        self.name = name

    def add_start_state(self, start_state: StartNode) -> None:
        self.start_state_list.append(start_state)

    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_process(self)


class Model(BpmnElement):
    def __init__(
        self,
        process_list: List[Process] = [],
        raw_ingest_ref: Optional[ET.ElementTree] = None,
    ):
        self.process_list = process_list
        self.raw_ingest_ref = raw_ingest_ref

    def add_process(self, process: Process) -> None:
        self.process_list.append(process)

    def accept(self, visitor: BpmnVisitor) -> None:
        visitor.visit_model(self)

    def export_xml(self, output_file: str) -> None:
        if isinstance(self.raw_ingest_ref, ET.ElementTree):
            self.raw_ingest_ref.write(
                output_file, encoding="UTF-8", xml_declaration=True
            )
