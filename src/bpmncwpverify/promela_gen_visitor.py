from typing import List
from bpmncwpverify.bpmn import (
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    SubProcess,
    SequenceFlow,
    MessageFlow,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
    BpmnVisitor,
    Process,
    Activity,
    Bpmn,
    BpmnElement,
)


class PromelaGenVisitor(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.init_text = ""
        self.init_indent = 0
        self.places_text = ""
        self.places_indent = 0
        self.constants_indent = 0
        self.constants_text = ""
        self.behavior_model_text = ""
        self.behavior_model_indent = 0
        self.workflow_text = ""
        self.workflow_indent = 0
        self.flow_places: List[str] = []

    ####################
    # Helper Methods
    ####################
    def write_places_lines(self, text: str) -> None:
        self.places_text += ("\t" * self.places_indent).join(
            ("\n" + text.lstrip()).splitlines(True)
        )

    def write_constants_lines(self, text: str) -> None:
        self.constants_text += ("\t" * self.constants_indent).join(
            ("\n" + text.lstrip()).splitlines(True)
        )

    def write_behavior_model_lines(self, text: str) -> None:
        self.behavior_model_text += ("\t" * self.behavior_model_indent).join(
            ("\n" + text.lstrip()).splitlines(True)
        )

    def write_init_lines(self, text: str) -> None:
        self.init_text += ("\t" * self.init_indent).join(
            ("\n" + text.lstrip()).splitlines(True)
        )

    def write_workflow_lines(self, text: str) -> None:
        self.workflow_text += ("\t" * self.workflow_indent).join(
            ("\n" + text.lstrip()).splitlines(True)
        )

    def get_location(self, element: BpmnElement) -> str:
        if isinstance(element, Activity):
            return element.name + "_END"  # type: ignore
        else:
            return element.name  # type: ignore

    ####################
    # Visitor Methods
    ####################
    def visit_start_event(self, event: StartEvent) -> bool:
        return True

    def end_visit_start_event(self, event: StartEvent) -> None:
        pass

    def visit_end_event(self, event: EndEvent) -> bool:
        return True

    def end_visit_end_event(self, event: EndEvent) -> None:
        pass

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        return True

    def end_visit_intermediate_event(self, event: IntermediateEvent) -> None:
        pass

    def visit_task(self, task: Task) -> bool:
        return True

    def end_visit_task(self, task: Task) -> None:
        pass

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        return True

    def end_visit_sub_process(self, subprocess: SubProcess) -> None:
        pass

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def end_visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def visit_process(self, process: Process) -> None:
        pass

    def end_visit_process(self, process: Process) -> None:
        pass

    def visit_bpmn(self, bpmn: Bpmn) -> Bpmn:
        init_lines = "init {\n"
        init_lines += "\tatomic{\n"
        init_lines += "\t\tupdateState()\n"
        for process in bpmn.processes:
            init_lines += "\t\trun {}()\n".format(process.name)
        init_lines += "\t}\n"
        init_lines += "}\n\n"
        self.write_init_lines(init_lines)
        for place in self.flow_places:
            self.write_places_lines("bit {x} = 0".format(x=str(place)))

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        pass
