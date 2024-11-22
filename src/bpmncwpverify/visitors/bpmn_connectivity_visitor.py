from typing import Set
from bpmncwpverify.core.bpmn import (
    Bpmn,
    BpmnElement,
    BpmnVisitor,
    Flow,
    MessageFlow,
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


class BpmnConnectivityVisitor(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[BpmnElement] = set()
        self.last_visited_set: Set[BpmnElement] = set()

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

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        self.visited.add(subprocess)
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self.visited.add(gateway)
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self.visited.add(gateway)
        return True

    def process_node(self, flow: Flow) -> bool:
        if flow.target_node in self.visited:
            flow.is_leaf = True
            return False
        return True

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return self.process_node(flow)

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return self.process_node(flow)

    def end_visit_process(self, process: Process) -> None:
        if set(process.all_items().values()) != self.visited:
            raise Exception("Process graph is not fully connected")
        start_events = 0
        end_events = 0
        for itm in process.all_items().values():
            if isinstance(itm, StartEvent):
                start_events += 1
            elif isinstance(itm, EndEvent):
                end_events += 1

        if start_events == 0 or end_events == 0:
            raise Exception(
                f"Error with end events or start events: # end states = {end_events}, # start states = {start_events}"
            )

        # This line of code is for testing purposes
        self.last_visited_set = self.visited

        # Reset visited after processing each process to ensure connectivity of each process
        self.visited = set()

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        if len(bpmn.processes) > 1:
            if len(bpmn.inter_process_msgs) == 0:
                raise Exception("No inter process messages exist in this bpmn model.")
