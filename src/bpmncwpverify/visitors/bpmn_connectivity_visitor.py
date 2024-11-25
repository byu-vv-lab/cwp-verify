from bpmncwpverify.core.bpmn import (
    BpmnVisitor,
    Flow,
    Node,
    SequenceFlow,
    StartEvent,
    EndEvent,
    IntermediateEvent,
)


class BpmnConnectivityVisitor(BpmnVisitor):  # type: ignore
    def _ensure_in_messages(self, node: Node, obj_type: str) -> None:
        if node.in_msgs:
            if not node.message_event_definition:
                raise Exception(
                    f"Exception occurred while visiting {obj_type}:{node.id}. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool."
                )

    def _ensure_out_messages(self, node: Node, obj_type: str) -> None:
        if node.out_msgs:
            if not node.message_event_definition:
                raise Exception(
                    f"Exception occurred while visiting {obj_type}:{node.id}. A message flow can only come from a Messege end or intermediate event; Send, User, or Service task; Subprocess; or black box pool."
                )

    def visit_start_event(self, event: StartEvent) -> bool:
        self._ensure_in_messages(event, "start event")
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        if event.in_msgs:
            raise Exception(
                f"Exception occurred while visiting end event: {event.id}. End events cannot have incoming messages."
            )
        self._ensure_out_messages(event, "end event")
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self._ensure_in_messages(event, "intermediate event")
        self._ensure_out_messages(event, "intermediate event")
        return True

    def process_flow(self, flow: Flow) -> bool:
        # For this is_leaf to work, this model would have already needed to been visited by a visitor that sets this attribute
        if flow.is_leaf:
            return False
        return True

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return self.process_flow(flow)
