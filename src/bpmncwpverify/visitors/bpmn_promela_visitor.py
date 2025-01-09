from typing import List
from bpmncwpverify.core.bpmn import (
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    MessageFlow,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
    BpmnVisitor,
    Process,
    Bpmn,
)

##############
# Constants
##############
HELPER_FUNCS_STR = "\n\n#define hasToken(place) (place != 0)\n\n#define putToken(place) place = 1\n\n#define consumeToken(place) place = 0"
##############


class PromelaGenVisitor(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.defs: List[str] = []
        self.init_proc_contents: List[str] = []
        self.promela: List[str] = []
        self.indent: int = 0

    def _inc_indent(self) -> None:
        self.indent += 1

    def _dec_indent(self) -> None:
        self.indent -= 1

    def _tab(self) -> str:
        """return string contianing 'self.indent' tabs"""
        return "\t" * self.indent

    def _nl(self, nl: int) -> str:
        """return string contianing 'nl' new lines"""
        return "\n" * nl

    def _write_str(self, new_str: str, nl: int, instance_str: List[str]) -> None:
        instance_str.append(self._tab())
        instance_str.append(new_str)
        instance_str.append(self._nl(nl))

    def __repr__(self) -> str:
        return (
            "".join(self.defs)
            + "".join(self.init_proc_contents)
            + "".join(self.promela)
        )

    ####################
    # Visitor Methods
    ####################
    def visit_start_event(self, event: StartEvent) -> bool:
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        return True

    def visit_task(self, task: Task) -> bool:
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return True

    def visit_process(self, process: Process) -> bool:
        self._write_str(f"run {process.name}()", 1, self.init_proc_contents)
        return True

    def end_visit_process(self, process: Process) -> None:
        pass

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        self._write_str(HELPER_FUNCS_STR, 2, self.defs)
        self._write_str("init {", 1, self.init_proc_contents)
        self._inc_indent()
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        self._dec_indent()
        self._write_str("}", 1, self.init_proc_contents)
