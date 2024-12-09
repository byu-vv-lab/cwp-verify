from typing import Set
from bpmncwpverify.core.bpmn import (
    BpmnElement,
    BpmnVisitor,
    Flow,
    GatewayNode,
    Process,
    SequenceFlow,
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    SubProcess,
    ExclusiveGatewayNode,
    ParallelGatewayNode,
)
from bpmncwpverify.error import (
    BpmnGraphConnError,
    BpmnMissingEventsError,
    BpmnSeqFlowEndEventError,
    BpmnSeqFlowNoExprError,
    BpmnTaskFlowError,
)


class ProcessConnectivityVisitor(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[BpmnElement] = set()
        self.last_visited_set: Set[BpmnElement] = set()

    def visit_start_event(self, event: StartEvent) -> bool:
        self.visited.add(event)
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        if event.out_flows:
            raise Exception(BpmnSeqFlowEndEventError(event.id))
        self.visited.add(event)
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self.visited.add(event)
        return True

    def visit_task(self, task: Task) -> bool:
        if not (task.in_flows and task.out_flows):
            raise Exception(BpmnTaskFlowError(task.id))
        self.visited.add(task)
        return True

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        self.visited.add(subprocess)
        return True

    def _validate_out_flows(self, gateway: GatewayNode) -> None:
        for out_flow in gateway.out_flows:
            if not out_flow.expression:
                raise Exception(BpmnSeqFlowNoExprError(gateway.id, out_flow.id))

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self._validate_out_flows(gateway)
        self.visited.add(gateway)
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self._validate_out_flows(gateway)
        self.visited.add(gateway)
        return True

    def process_flow(self, flow: Flow) -> bool:
        if flow.target_node in self.visited:
            flow.is_leaf = True
            return False
        return True

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return self.process_flow(flow)

    def end_visit_process(self, process: Process) -> None:
        start_events = sum(
            isinstance(itm, StartEvent) for itm in process.all_items().values()
        )
        end_events = sum(
            isinstance(itm, EndEvent) for itm in process.all_items().values()
        )

        # Determine if there is a valid starting point
        starting_point = start_events > 0 or any(
            itm.in_msgs for itm in process.all_items().values()
        )

        if not starting_point or end_events == 0:
            raise Exception(BpmnMissingEventsError(start_events, end_events))

        # Ensure all items in the process graph are visited
        if set(process.all_items().values()) != self.visited:
            raise Exception(BpmnGraphConnError())

        # Ensure all items in the process graph are visited
        if set(process.all_items().values()) != self.visited:
            raise Exception("Process graph is not fully connected")

        # Testing and cleanup
        self.last_visited_set = self.visited
        self.visited = set()
