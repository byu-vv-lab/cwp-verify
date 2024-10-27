import graphviz
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


class GraphVizVisitor(BpmnVisitor):  # type: ignore
    def __init__(self, process_number: int) -> None:
        self.dot = graphviz.Digraph(comment="Process graph {}".format(process_number))

    def visitStartEvent(self, event: StartEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def endVisitStartEvent(self, event: StartEvent) -> None:
        pass

    def visitEndEvent(self, event: EndEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def endVisitEndEvent(self, event: EndEvent) -> None:
        pass

    def visitIntermediateEvent(self, event: IntermediateEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def endVisitIntermediateEvent(self, event: IntermediateEvent) -> None:
        pass

    def visitTask(self, task: Task) -> bool:
        self.dot.node(task.id, task.name)
        return True

    def endVisitTask(self, task: Task) -> None:
        pass

    def visitSubProcess(self, subprocess: SubProcess) -> bool:
        self.dot.node(subprocess.id, subprocess.name)
        return True

    def endVisitSubProcess(self, subprocess: SubProcess) -> None:
        pass

    def visitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self.dot.node(gateway.id, gateway.name)
        return True

    def endVisitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visitParallelGateway(self, gateway: ParallelGatewayNode) -> bool:
        self.dot.node(gateway.id, gateway.name)
        return True

    def endVisitParallelGateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    def endVisitSequenceFlow(self, flow: SequenceFlow) -> None:
        self.dot.edge(flow.source_node.id, flow.target_node.id)
        pass

    def visitMessageFlow(self, flow: MessageFlow) -> None:
        pass

    def endVisitMessageFlow(self, flow: MessageFlow) -> None:
        self.dot.edge(flow.source_node.id, flow.target_node.id)
        pass
