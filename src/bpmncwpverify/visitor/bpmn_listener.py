from abc import ABC, abstractmethod
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


class BpmnListener(ABC):
    @abstractmethod
    def enterStartEvent(self, event: StartEvent) -> bool:
        pass

    @abstractmethod
    def exitStartEvent(self, event: StartEvent) -> None:
        pass

    @abstractmethod
    def enterEndEvent(self, event: EndEvent) -> bool:
        pass

    @abstractmethod
    def exitEndEvent(self, event: EndEvent) -> None:
        pass

    @abstractmethod
    def enterIntermediateEvent(self, event: IntermediateEvent) -> bool:
        pass

    @abstractmethod
    def exitIntermediateEvent(self, event: IntermediateEvent) -> None:
        pass

    @abstractmethod
    def enterTask(self, task: Task) -> bool:
        pass

    @abstractmethod
    def exitTask(self, task: Task) -> None:
        pass

    @abstractmethod
    def enterSubProcess(self, subprocess: SubProcess) -> bool:
        pass

    @abstractmethod
    def exitSubProcess(self, subprocess: SubProcess) -> None:
        pass

    @abstractmethod
    def enterExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> bool:
        pass

    @abstractmethod
    def exitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    @abstractmethod
    def enterParallelGateway(self, gateway: ParallelGatewayNode) -> bool:
        pass

    @abstractmethod
    def exitParallelGateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    @abstractmethod
    def enterSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    @abstractmethod
    def exitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    @abstractmethod
    def enterMessageFlow(self, flow: MessageFlow) -> None:
        pass

    @abstractmethod
    def exitMessageFlow(self, flow: MessageFlow) -> None:
        pass
