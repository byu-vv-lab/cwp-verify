from abc import ABC, abstractmethod
from .BPMN import (
    Flow,
    Process,
    Msg,
    EventNode,
    ActivityNode,
    GatewayNode,
    StartNode,
    XorGatewayNode,
    ParallelGatewayJoinNode,
    ParallelGatewayForkNode,
    EndNode,
    MsgIntermediateNode,
    TimerIntermediateNode,
    Model,
)


class BPMN_Visitor(ABC):
    @abstractmethod
    def visit_process(self, element: Process) -> None:
        pass

    @abstractmethod
    def visit_flow(self, element: Flow) -> None:
        pass

    @abstractmethod
    def visit_msg(self, element: Msg) -> None:
        pass

    @abstractmethod
    def visit_activity_node(self, element: ActivityNode) -> None:
        pass

    @abstractmethod
    def visit_start_node(self, element: StartNode) -> None:
        pass

    @abstractmethod
    def visit_xor_gateway_node(self, element: XorGatewayNode) -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway_join_node(
        self, element: ParallelGatewayJoinNode
    ) -> None:
        pass

    @abstractmethod
    def visit_gateway_node(self, element: GatewayNode) -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway_fork_node(
        self, element: ParallelGatewayForkNode
    ) -> None:
        pass

    @abstractmethod
    def visit_end_node(self, element: EndNode) -> None:
        pass

    @abstractmethod
    def visit_event_node(self, element: EventNode) -> None:
        pass

    @abstractmethod
    def visit_msg_intermediate_node(self, element: MsgIntermediateNode) -> None:
        pass

    @abstractmethod
    def visit_timer_intermediate_node(self, element: TimerIntermediateNode) -> None:
        pass

    @abstractmethod
    def visit_model(self, element: Model) -> None:
        pass
