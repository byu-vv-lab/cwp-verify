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
    Bpmn,
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

    ####################
    # Visitor Methods
    ####################
    def visitStartEvent(self, event: StartEvent) -> bool:
        return True

    def endVisitStartEvent(self, event: StartEvent) -> None:
        pass

    def visitEndEvent(self, event: EndEvent) -> bool:
        return True

    def endVisitEndEvent(self, event: EndEvent) -> None:
        pass

    def visitIntermediateEvent(self, event: IntermediateEvent) -> bool:
        return True

    def endVisitIntermediateEvent(self, event: IntermediateEvent) -> None:
        pass

    def visitTask(self, task: Task) -> bool:
        return True

    def endVisitTask(self, task: Task) -> None:
        pass

    def visitSubProcess(self, subprocess: SubProcess) -> bool:
        return True

    def endVisitSubProcess(self, subprocess: SubProcess) -> None:
        pass

    def visitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def endVisitExclusiveGateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visitParallelGateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def endVisitParallelGateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    def endVisitSequenceFlow(self, flow: SequenceFlow) -> None:
        pass

    def visitMessageFlow(self, flow: MessageFlow) -> None:
        pass

    def endVisitMessageFlow(self, flow: MessageFlow) -> None:
        pass

    def visitProcess(self, process: Process) -> None:
        pass

    def endVisitProcess(self, process: Process) -> None:
        pass

    def visitBpmn(self, bpmn: Bpmn) -> Bpmn:
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

    def endVisitBpmn(self, bpmn: Bpmn) -> None:
        pass
