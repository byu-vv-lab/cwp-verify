from bpmncwpverify.bpmn import (
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    SubProcess,
    SequenceFlow,
    MessageFlow,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
    BpmnVisitor,
)


class PromelaGenVisitor(BpmnVisitor):  # type: ignore
    def visitStartEvent(self, event: StartEvent) -> bool:
        return True

    def endVisitStartEvent(self, event: StartEvent) -> None:
        pass

    def visitEndEvent(self, event: EndEvent) -> bool:
        return True

    def endVisitEndEvent(self, event: EndEvent) -> None:
        pass

    def visitIntermediateEvent(self, event: IntermediateEvent) -> bool:
        return True

    def endVisitIntermediateEvent(self, event: IntermediateEvent) -> None:
        pass

    def visitTask(self, task: Task) -> bool:
        return True

    def endVisitTask(self, task: Task) -> None:
        pass

    def visitSubProcess(self, subprocess: SubProcess) -> bool:
        return True

    def endVisitSubProcess(self, subprocess: SubProcess) -> None:
        pass

    def visitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def endVisitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visitParallelGateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def endVisitParallelGateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    def endVisitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    def visitMessageFlow(self, flow: MessageFlow) -> None:
        pass

    def endVisitMessageFlow(self, flow: MessageFlow) -> None:
        pass
