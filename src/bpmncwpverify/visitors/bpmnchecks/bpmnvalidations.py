from typing import Set
import bpmncwpverify.core.bpmn as bpmn
from bpmncwpverify.core.error import (
    BpmnFlowIncomingError,
    BpmnFlowOutgoingError,
    BpmnFlowStartEventError,
    BpmnGraphConnError,
    BpmnMissingEventsError,
    BpmnMsgEndEventError,
    BpmnMsgGatewayError,
    BpmnMsgSrcError,
    BpmnMsgStartEventError,
    BpmnMsgTargetError,
    BpmnSeqFlowEndEventError,
    BpmnSeqFlowNoExprError,
    BpmnTaskFlowError,
)
from bpmncwpverify.visitors import bpmnvisitor


class ProcessConnectivityVisitor(bpmnvisitor.BpmnVisitor):  # type: ignore
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

    def end_visit_process(self, process: "bpmn.Process") -> None:
        # Ensure all items in the process graph are visited
        if set(process.all_items().values()) != self.visited:
            raise Exception(BpmnGraphConnError())


class ValidateSeqFlowVisitor(bpmnvisitor.BpmnVisitor):  # type: ignore
    def _validate_out_flows(self, gateway: "bpmn.GatewayNode") -> None:
        for out_flow in gateway.out_flows:
            if not out_flow.expression:
                raise Exception(BpmnSeqFlowNoExprError(gateway.id, out_flow.id))

    def visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> bool:
        self._validate_out_flows(gateway)
        return True

    def visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> bool:
        self._validate_out_flows(gateway)
        return True

    def visit_task(self, task: "bpmn.Task") -> bool:
        if not (task.in_flows and task.out_flows):
            raise Exception(BpmnTaskFlowError(task.id))
        return True

    def visit_end_event(self, event: "bpmn.EndEvent") -> bool:
        if event.out_flows:
            raise Exception(BpmnSeqFlowEndEventError(event.id))
        return True


class ValidateMsgsVisitor(bpmnvisitor.BpmnVisitor):  # type: ignore
    def _ensure_in_messages(self, node: "bpmn.Node", obj_type: str) -> None:
        if node.in_msgs:
            if not node.message_event_definition:
                raise Exception(BpmnMsgTargetError(obj_type, node.id))

    def _ensure_out_messages(self, node: "bpmn.Node", obj_type: str) -> None:
        if node.out_msgs:
            if not node.message_event_definition:
                raise Exception(BpmnMsgSrcError(obj_type, node.id))

    def visit_start_event(self, event: "bpmn.StartEvent") -> bool:
        self._ensure_in_messages(event, "start event")
        return True

    def visit_end_event(self, event: "bpmn.EndEvent") -> bool:
        if event.in_msgs:
            raise Exception(BpmnMsgEndEventError(event.id))
        self._ensure_out_messages(event, "end event")
        return True

    def _validate_gateway_no_msgs(
        self, gateway: "bpmn.GatewayNode", gateway_type: str
    ) -> bool:
        if gateway.in_msgs or gateway.out_msgs:
            raise Exception(BpmnMsgGatewayError(gateway_type, gateway.id))
        return True

    def visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> bool:
        return self._validate_gateway_no_msgs(gateway, "ParallelGatewayNode")

    def visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> bool:
        return self._validate_gateway_no_msgs(gateway, "ExclusiveGatewayNode")

    def visit_intermediate_event(self, event: "bpmn.IntermediateEvent") -> bool:
        self._ensure_in_messages(event, "intermediate event")
        self._ensure_out_messages(event, "intermediate event")
        return True


class ValidateBpmnIncomingFlows(bpmnvisitor.BpmnVisitor):  # type: ignore
    def _check_in_flows(self, element: "bpmn.Node") -> bool:
        if not element.in_flows:
            raise Exception(BpmnFlowIncomingError(element.id))
        return True

    def visit_end_event(self, event: "bpmn.EndEvent") -> bool:
        return self._check_in_flows(event)

    def visit_intermediate_event(self, event: "bpmn.IntermediateEvent") -> bool:
        return self._check_in_flows(event)

    def visit_task(self, task: "bpmn.Task") -> bool:
        return self._check_in_flows(task)

    def visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> bool:
        return self._check_in_flows(gateway)

    def visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> bool:
        return self._check_in_flows(gateway)


class ValidateBpmnOutgoingFlows(bpmnvisitor.BpmnVisitor):  # type: ignore
    def _check_out_flows(self, element: "bpmn.Node") -> bool:
        if not element.out_flows:
            raise Exception(BpmnFlowOutgoingError(element.id))
        return True

    def visit_start_event(self, event: "bpmn.StartEvent") -> bool:
        return self._check_out_flows(event)

    def visit_intermediate_event(self, event: "bpmn.IntermediateEvent") -> bool:
        return self._check_out_flows(event)

    def visit_task(self, task: "bpmn.Task") -> bool:
        return self._check_out_flows(task)

    def visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> bool:
        return self._check_out_flows(gateway)

    def visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> bool:
        return self._check_out_flows(gateway)


class ValidateStartEventFlows(bpmnvisitor.BpmnVisitor):  # type: ignore
    def visit_start_event(self, event: "bpmn.StartEvent") -> bool:
        if event.in_flows:
            raise Exception(BpmnFlowStartEventError(event.id))
        if event.out_msgs:
            raise Exception(BpmnFlowStartEventError(event.id))
        if event.in_msgs and not event.message_event_definition:
            raise Exception(BpmnMsgStartEventError(event.id))
        return False


##########################
# validation functions
##########################
def validate_start_end_events(process: "bpmn.Process") -> None:
    start_events = sum(
        isinstance(itm, bpmn.StartEvent) for itm in process.all_items().values()
    )
    end_events = sum(
        isinstance(itm, bpmn.EndEvent) for itm in process.all_items().values()
    )

    # Determine if there is a valid starting point
    starting_point = start_events > 0 or any(
        itm.in_msgs for itm in process.all_items().values()
    )

    if not starting_point or end_events == 0:
        raise Exception(BpmnMissingEventsError(start_events, end_events))
