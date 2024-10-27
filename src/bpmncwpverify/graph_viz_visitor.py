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
        return True

    def endVisitStartEvent(self, event: StartEvent) -> None:
        self.dot.node(event.id, event.name)
        pass

    def visitEndEvent(self, event: EndEvent) -> bool:
        return True

    def endVisitEndEvent(self, event: EndEvent) -> None:
        self.dot.node(event.id, event.name)
        pass

    def visitIntermediateEvent(self, event: IntermediateEvent) -> bool:
        return True

    def endVisitIntermediateEvent(self, event: IntermediateEvent) -> None:
        self.dot.node(event.id, event.name)
        pass

    def visitTask(self, task: Task) -> bool:
        return True

    def endVisitTask(self, task: Task) -> None:
        self.dot.node(task.id, task.name)
        pass

    def visitSubProcess(self, subprocess: SubProcess) -> bool:
        return True

    def endVisitSubProcess(self, subprocess: SubProcess) -> None:
        self.dot.node(subprocess.id, subprocess.name)
        pass

    def visitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def endVisitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> None:
        self.dot.node(gateway.id, gateway.name)
        pass

    def visitParallelGateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def endVisitParallelGateway(self, gateway: ParallelGatewayNode) -> None:
        self.dot.node(gateway.id, gateway.name)
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
