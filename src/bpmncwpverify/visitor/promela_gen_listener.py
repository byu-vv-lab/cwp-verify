from bpmncwpverify.visitor.bpmn_listener import BpmnListener

from bpmncwpverify.bpmn.BPMN import (
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    SubProcess,
    SequenceFlow,
    MessageFlow,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
)


class PromelaGenListener(BpmnListener):
    def enterStartEvent(self, event: StartEvent) -> bool:
        return True

    def exitStartEvent(self, event: StartEvent) -> None:
        pass

    def enterEndEvent(self, event: EndEvent) -> bool:
        return True

    def exitEndEvent(self, event: EndEvent) -> None:
        pass

    def enterIntermediateEvent(self, event: IntermediateEvent) -> bool:
        return True

    def exitIntermediateEvent(self, event: IntermediateEvent) -> None:
        pass

    def enterTask(self, task: Task) -> bool:
        return True

    def exitTask(self, task: Task) -> None:
        pass

    def enterSubProcess(self, subprocess: SubProcess) -> bool:
        return True

    def exitSubProcess(self, subprocess: SubProcess) -> None:
        pass

    def enterExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def exitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def enterParallelGateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def exitParallelGateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def enterSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    def exitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    def enterMessageFlow(self, flow: MessageFlow) -> None:
        pass

    def exitMessageFlow(self, flow: MessageFlow) -> None:
        pass
