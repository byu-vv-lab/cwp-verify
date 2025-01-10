from typing import List
from enum import Enum
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
NL_NONE = 0
NL_SINGLE = 1
NL_DOUBLE = 2


##############
class IndentAction(Enum):
    NIL = 0
    INC = 1
    DEC = 2


class PromelaGenVisitor(BpmnVisitor):  # type: ignore
    class StringManager:
        def __init__(self) -> None:
            self.contents: List[str] = []
            self.indent = 0

        def _tab(self) -> str:
            """return string contianing 'self.indent' tabs"""
            return "\t" * self.indent

        def _newline(self, nl: int) -> str:
            """Return string containing 'nl' new lines."""
            return "\n" * nl

        def _inc_indent(self) -> None:
            self.indent += 1

        def _dec_indent(self) -> None:
            assert self.indent > 0
            self.indent -= 1

        def write_str(
            self,
            new_str: str,
            nl: int,
        ) -> None:
            self.contents.append(f"{self._tab()}{new_str}{self._newline(nl)}")

        def __repr__(self) -> str:
            return "".join(self.contents)

    def __init__(self) -> None:
        self.defs = PromelaGenVisitor.StringManager()
        self.init_proc_contents = PromelaGenVisitor.StringManager()
        self.promela = PromelaGenVisitor.StringManager()

    def __repr__(self) -> str:
        return f"{self.defs}{self.init_proc_contents}{self.promela}"

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
        return True

    def end_visit_process(self, process: Process) -> None:
        pass

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        pass
