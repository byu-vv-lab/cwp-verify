from typing import Set
import bpmncwpverify.core.bpmn as bpmn
import bpmncwpverify.visitors.bpmnvisitor as bpmnvisitor


class SetFlowLeafs(bpmnvisitor.BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[bpmn.BpmnElement] = set()

    def visit_start_event(self, event: "bpmn.StartEvent") -> bool:
        self.visited.add(event)
        return True

    def visit_end_event(self, event: "bpmn.EndEvent") -> bool:
        self.visited.add(event)
        return True

    def visit_intermediate_event(self, event: "bpmn.IntermediateEvent") -> bool:
        self.visited.add(event)
        return True

    def visit_task(self, task: "bpmn.Task") -> bool:
        self.visited.add(task)
        return True

    def visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> bool:
        self.visited.add(gateway)
        return True

    def visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> bool:
        self.visited.add(gateway)
        return True

    def process_flow(self, flow: "bpmn.Flow") -> bool:
        if flow.target_node in self.visited:
            flow.is_leaf = True
            return False
        return True

    def visit_sequence_flow(self, flow: "bpmn.SequenceFlow") -> bool:
        return self.process_flow(flow)
