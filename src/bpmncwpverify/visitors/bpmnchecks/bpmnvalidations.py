from typing import Set
from bpmncwpverify.core.bpmn import (
    BpmnElement,
    BpmnVisitor,
    GatewayNode,
    Node,
    Process,
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
    BpmnMsgEndEventError,
    BpmnMsgGatewayError,
    BpmnMsgSrcError,
    BpmnMsgTargetError,
    BpmnSeqFlowEndEventError,
    BpmnSeqFlowNoExprError,
    BpmnTaskFlowError,
)


class ProcessConnectivityVisitor(BpmnVisitor):  # type: ignore
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

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        self.visited.add(subprocess)
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self.visited.add(gateway)
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self.visited.add(gateway)
        return True

    def end_visit_process(self, process: Process) -> None:
        # Ensure all items in the process graph are visited
        if set(process.all_items().values()) != self.visited:
            raise Exception(BpmnGraphConnError())


class ValidateSeqFlowVisitor(BpmnVisitor):  # type: ignore
    def _validate_out_flows(self, gateway: GatewayNode) -> None:
        for out_flow in gateway.out_flows:
            if not out_flow.expression:
                raise Exception(BpmnSeqFlowNoExprError(gateway.id, out_flow.id))

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self._validate_out_flows(gateway)
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self._validate_out_flows(gateway)
        return True

    def visit_task(self, task: Task) -> bool:
        if not (task.in_flows and task.out_flows):
            raise Exception(BpmnTaskFlowError(task.id))
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        if event.out_flows:
            raise Exception(BpmnSeqFlowEndEventError(event.id))
        return True


class ValidateMsgsVisitor(BpmnVisitor):  # type: ignore
    def _ensure_in_messages(self, node: Node, obj_type: str) -> None:
        if node.in_msgs:
            if not node.message_event_definition:
                raise Exception(BpmnMsgTargetError(obj_type, node.id))

    def _ensure_out_messages(self, node: Node, obj_type: str) -> None:
        if node.out_msgs:
            if not node.message_event_definition:
                raise Exception(BpmnMsgSrcError(obj_type, node.id))

    def visit_start_event(self, event: StartEvent) -> bool:
        self._ensure_in_messages(event, "start event")
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        if event.in_msgs:
            raise Exception(BpmnMsgEndEventError(event.id))
        self._ensure_out_messages(event, "end event")
        return True

    def _validate_gateway_no_msgs(
        self, gateway: GatewayNode, gateway_type: str
    ) -> bool:
        if gateway.in_msgs or gateway.out_msgs:
            raise Exception(BpmnMsgGatewayError(gateway_type, gateway.id))
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return self._validate_gateway_no_msgs(gateway, "ParallelGatewayNode")

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return self._validate_gateway_no_msgs(gateway, "ExclusiveGatewayNode")

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self._ensure_in_messages(event, "intermediate event")
        self._ensure_out_messages(event, "intermediate event")
        return True


##########################
# validation functions
##########################
def validate_start_end_events(process: Process) -> None:
    start_events = sum(
        isinstance(itm, StartEvent) for itm in process.all_items().values()
    )
    end_events = sum(isinstance(itm, EndEvent) for itm in process.all_items().values())

    # Determine if there is a valid starting point
    starting_point = start_events > 0 or any(
        itm.in_msgs for itm in process.all_items().values()
    )

    if not starting_point or end_events == 0:
        raise Exception(BpmnMissingEventsError(start_events, end_events))
