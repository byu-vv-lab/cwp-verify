from bpmncwpverify.core.bpmn import (
    BpmnVisitor,
    ExclusiveGatewayNode,
    Flow,
    GatewayNode,
    Node,
    ParallelGatewayNode,
    SequenceFlow,
    StartEvent,
    EndEvent,
    IntermediateEvent,
)
from bpmncwpverify.error import MessageError


class BpmnConnectivityVisitor(BpmnVisitor):  # type: ignore
    def _ensure_in_messages(self, node: Node, obj_type: str) -> None:
        if node.in_msgs:
            if not node.message_event_definition:
                raise Exception(
                    MessageError(
                        node.id,
                        f"Error while visiting a {obj_type}. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool.",
                    )
                )

    def _ensure_out_messages(self, node: Node, obj_type: str) -> None:
        if node.out_msgs:
            if not node.message_event_definition:
                raise Exception(
                    MessageError(
                        node.id,
                        f"Error while visiting a {obj_type}. A message flow can only come from a Messege end or intermediate event; Send, User, or Service task; Subprocess; or black box pool.",
                    )
                )

    def visit_start_event(self, event: StartEvent) -> bool:
        self._ensure_in_messages(event, "start event")
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        if event.in_msgs:
            raise Exception(
                MessageError(
                    event.id,
                    "Error while visiting an end_event. End events cannot have incoming messages.",
                )
            )
        self._ensure_out_messages(event, "end event")
        return True

    def _validate_gateway_no_msgs(
        self, gateway: GatewayNode, gateway_type: str
    ) -> bool:
        if gateway.in_msgs or gateway.out_msgs:
            raise Exception(
                MessageError(
                    gateway.id,
                    f"Error while visiting a {gateway_type}. Gateways cannot have incoming or outgoing messages.",
                )
            )
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return self._validate_gateway_no_msgs(gateway, "ParallelGatewayNode")

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return self._validate_gateway_no_msgs(gateway, "ExclusiveGatewayNode")

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
