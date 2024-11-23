from bpmncwpverify.core.bpmn import (
    BpmnVisitor,
    Flow,
    Node,
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
    def _ensure_in_messages(self, node: Node, obj_type: str) -> None:
        if node.in_msgs:
            if not node.message_event_definition:
                raise Exception(
                    f"Exception occurred while visiting {obj_type}:{node.id}. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool."
                )

    def visit_start_event(self, event: StartEvent) -> bool:
        self._ensure_in_messages(event, "start event")
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        if event.in_msgs:
            raise Exception(
                f"Exception occurred while visiting end event: {event.id}. End events cannot have incoming messages."
            )
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self._ensure_in_messages(event, "intermediate event")
        return True

    def visit_task(self, task: Task) -> bool:
        return True

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def process_flow(self, flow: Flow) -> bool:
        if flow.is_leaf:
            return False
        return True

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return self.process_flow(flow)
