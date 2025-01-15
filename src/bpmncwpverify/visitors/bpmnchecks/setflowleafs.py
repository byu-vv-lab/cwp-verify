from typing import Set
from bpmncwpverify.core.bpmn import (
    BpmnElement,
    BpmnVisitor,
    Flow,
    SequenceFlow,
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    ExclusiveGatewayNode,
    ParallelGatewayNode,
)


class SetFlowLeafs(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[BpmnElement] = set()

    def visit_start_event(self, event: StartEvent) -> bool:
        self.visited.add(event)
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        self.visited.add(event)
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self.visited.add(event)
        return True

    def visit_task(self, task: Task) -> bool:
        self.visited.add(task)
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self.visited.add(gateway)
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self.visited.add(gateway)
        return True

    def process_flow(self, flow: Flow) -> bool:
        if flow.target_node in self.visited:
            flow.is_leaf = True
            return False
        return True

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return self.process_flow(flow)
