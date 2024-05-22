from abc import ABC, abstractmethod

from bpmn.BPMN import (
    Flow,
    Msg,
    ActivityNode,
    StartNode,
    XorGatewayNode,
    ParallelGatewayJoinNode,
    ParallelGatewayForkNode,
    EndNode,
    MsgIntermediateNode,
    TimerIntermediateNode,
    Model,
)


class BPMN_visitor(ABC):
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
    def visit_parallel_gateway_join_node(self, element: ParallelGatewayJoinNode) -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway_fork_node(self, element: ParallelGatewayForkNode) -> None:
        pass

    @abstractmethod
    def visit_end_node(self, element: EndNode) -> None:
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


if __name__ == "__main__":
    pass
