from bpmncwpverify.visitor.bpmn_listener import BpmnListener
from bpmncwpverify.bpmn.BPMN import (
    Node,
    StartEvent,
    Task,
    EndEvent,
    IntermediateEvent,
    SubProcess,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
)


class BpmnTraverser:
    def __init__(self, listener: BpmnListener):
        self.listener = listener

    def walk(self, node: Node) -> None:
        if isinstance(node, StartEvent):
            self.listener.enterStartEvent(node)
        elif isinstance(node, Task):
            self.listener.enterTask(node)
        elif isinstance(node, EndEvent):
            self.listener.enterEndEvent(node)
        elif isinstance(node, IntermediateEvent):
            self.listener.enterIntermediateEvent(node)
        elif isinstance(node, SubProcess):
            self.listener.enterSubProcess(node)
        elif isinstance(node, ExclusiveGatewayNode):
            self.listener.enterExclusiveGateway(node)
        elif isinstance(node, ParallelGatewayNode):
            self.listener.enterParallelGateway(node)

        for flow in node.out_flows:
            self.listener.enterSequenceFlow(flow)
            if flow.target_node is not None:
                self.walk(flow.target_node)
            self.listener.exitSequenceFlow(flow)

        if isinstance(node, StartEvent):
            self.listener.exitStartEvent(node)
        elif isinstance(node, Task):
            self.listener.exitTask(node)
        elif isinstance(node, EndEvent):
            self.listener.exitEndEvent(node)
        elif isinstance(node, IntermediateEvent):
            self.listener.exitIntermediateEvent(node)
        elif isinstance(node, SubProcess):
            self.listener.exitSubProcess(node)
        elif isinstance(node, ExclusiveGatewayNode):
            self.listener.exitExclusiveGateway(node)
        elif isinstance(node, ParallelGatewayNode):
            self.listener.exitParallelGateway(node)
