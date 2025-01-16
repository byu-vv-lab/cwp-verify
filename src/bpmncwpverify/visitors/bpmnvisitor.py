import bpmncwpverify.core.bpmn as bpmn


###################
# Bpmn Visitor interface
###################
class BpmnVisitor:
    def visit_start_event(self, event: "bpmn.StartEvent") -> bool:
        return True

    def end_visit_start_event(self, event: "bpmn.StartEvent") -> None:
        pass

    def visit_end_event(self, event: "bpmn.EndEvent") -> bool:
        return True

    def end_visit_end_event(self, event: "bpmn.EndEvent") -> None:
        pass

    def visit_intermediate_event(self, event: "bpmn.IntermediateEvent") -> bool:
        return True

    def end_visit_intermediate_event(self, event: "bpmn.IntermediateEvent") -> None:
        pass

    def visit_task(self, task: "bpmn.Task") -> bool:
        return True

    def end_visit_task(self, task: "bpmn.Task") -> None:
        pass

    def visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> bool:
        return True

    def end_visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> None:
        pass

    def visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> bool:
        return True

    def end_visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> None:
        pass

    def visit_sequence_flow(self, flow: "bpmn.SequenceFlow") -> bool:
        return True

    def end_visit_sequence_flow(self, flow: "bpmn.SequenceFlow") -> None:
        pass

    def visit_message_flow(self, flow: "bpmn.MessageFlow") -> bool:
        return True

    def end_visit_message_flow(self, flow: "bpmn.MessageFlow") -> None:
        pass

    def visit_process(self, process: "bpmn.Process") -> bool:
        return True

    def end_visit_process(self, process: "bpmn.Process") -> None:
        pass

    def visit_bpmn(self, bpmn: "bpmn.Bpmn") -> bool:
        return True

    def end_visit_bpmn(self, bpmn: "bpmn.Bpmn") -> None:
        pass
