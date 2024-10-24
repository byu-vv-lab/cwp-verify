from bpmncwpverify.BPMN import (
    Bpmn,
    Node,
    StartEvent,
    Task,
    EndEvent,
    IntermediateEvent,
    SubProcess,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
    BpmnVisitor,
)


class BpmnTraverser:
    def __init__(self, listener: BpmnVisitor):
        self.listener = listener

    def _walk_helper(self, node: Node) -> None:
        if isinstance(node, StartEvent):
            result = self.listener.enterStartEvent(node)
        elif isinstance(node, Task):
            result = self.listener.enterTask(node)
        elif isinstance(node, EndEvent):
            result = self.listener.enterEndEvent(node)
        elif isinstance(node, IntermediateEvent):
            result = self.listener.enterIntermediateEvent(node)
        elif isinstance(node, SubProcess):
            result = self.listener.enterSubProcess(node)
        elif isinstance(node, ExclusiveGatewayNode):
            result = self.listener.enterExclusiveGateway(node)
        elif isinstance(node, ParallelGatewayNode):
            result = self.listener.enterParallelGateway(node)
        else:
            raise Exception("node not recognized")

        if result:
            for flow in node.out_flows:
                self.listener.enterSequenceFlow(flow)
                if flow.target_node and not flow.cycle_flow:
                    self._walk_helper(flow.target_node)
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
        else:
            raise Exception("node not recognized")

    def walk(self, bpmn: Bpmn) -> None:
        for process in bpmn.processes:
            for start_event in process.get_start_states().values():
                self._walk_helper(start_event)
