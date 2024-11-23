from typing import Set
from bpmncwpverify.core.bpmn import (
    BpmnElement,
    BpmnVisitor,
    Flow,
    MessageFlow,
    Node,
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


class ProcessConnectivityVisitor(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[BpmnElement] = set()
        self.last_visited_set: Set[BpmnElement] = set()

    def _ensure_in_messages(self, node: Node, obj_type: str) -> None:
        if node.in_msgs:
            if not node.message_event_definition:
                raise Exception(
                    f"Exception occurred while visiting {obj_type}:{node.id}. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool."
                )

    def visit_start_event(self, event: StartEvent) -> bool:
        self._ensure_in_messages(event, "start event")
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
        for out_flow in gateway.out_flows:
            if not out_flow.expression:
                raise Exception(
                    f"Flow: `{out_flow.id}` from gateway: `{gateway.id}` does not have an expression. All flows coming out of gateways must have expressions."
                )
        self.visited.add(gateway)
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        for out_flow in gateway.out_flows:
            if not out_flow.expression:
                raise Exception(
                    f"Flow: `{out_flow.id}` from gateway: `{gateway.id}` does not have an expression. All flows coming out of gateways must have expressions."
                )
        self.visited.add(gateway)
        return True

    def process_flow(self, flow: Flow) -> bool:
        if flow.target_node in self.visited:
            flow.is_leaf = True
            return False
        return True

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return self.process_flow(flow)

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return self.process_flow(flow)

    def end_visit_process(self, process: Process) -> None:
        # Ensure all items in the process graph are visited
        if set(process.all_items().values()) != self.visited:
            raise Exception("Process graph is not fully connected")

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
            raise Exception(
                f"Error with end events or start events: # end states = {end_events}, # start states = {start_events}"
            )

        # Testing and cleanup
        self.last_visited_set = self.visited
        self.visited = set()
