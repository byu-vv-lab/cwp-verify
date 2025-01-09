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
    class StringManager:
        def __init__(self) -> None:
            self.contents: List[str] = []
            self.indent = 0

        def _tab(self) -> str:
            """return string contianing 'self.indent' tabs"""
            return "\t" * self.indent

        def _nl(self, nl: int) -> str:
            """return string contianing 'nl' new lines"""
            return "\n" * nl

        def inc_indent(self) -> None:
            self.indent += 1

        def dec_indent(self) -> None:
            self.indent -= 1

        def write_str(self, new_str: str, nl: int) -> None:
            self.contents.append(self._tab())
            self.contents.append(new_str)
            self.contents.append(self._nl(nl))

        def __repr__(self) -> str:
            return "".join(self.contents)

    def __init__(self) -> None:
        self.defs = PromelaGenVisitor.StringManager()
        self.init_proc_contents = PromelaGenVisitor.StringManager()
        self.promela = PromelaGenVisitor.StringManager()
        self.indent: int = 0

    def _write_str(self, new_str: str, nl: int, sm: StringManager) -> None:
        sm.write_str(new_str, nl)

    def __repr__(self) -> str:
        return str(self.defs) + str(self.init_proc_contents) + str(self.promela)

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
        self._write_str("hello", 1, self.promela)
        return True

    def end_visit_process(self, process: Process) -> None:
        pass

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        self._write_str(HELPER_FUNCS_STR, 2, self.defs)
        self._write_str("init {", 1, self.init_proc_contents)
        self.init_proc_contents.inc_indent()
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        self.init_proc_contents.dec_indent()
        self._write_str("}", 2, self.init_proc_contents)
