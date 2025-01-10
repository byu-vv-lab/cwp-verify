from typing import List, Optional
from enum import Enum
from bpmncwpverify.core.bpmn import (
    Flow,
    Node,
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

        def write_str(self, new_str: str, nl: int, indent_action: IndentAction) -> None:
            if indent_action == IndentAction.DEC:
                self._dec_indent()
            self.contents.append(f"{self._tab()}{new_str}{self._newline(nl)}")
            if indent_action == IndentAction.INC:
                self._inc_indent()

        def __repr__(self) -> str:
            return "".join(self.contents)

    def __init__(self) -> None:
        self.defs = PromelaGenVisitor.StringManager()
        self.init_proc_contents = PromelaGenVisitor.StringManager()
        self.promela = PromelaGenVisitor.StringManager()

    def _generate_location_label(
        self, element: Node, flow_or_message: Optional[Flow] = None
    ) -> str:
        if flow_or_message:
            return f"{element.name}_FROM_{flow_or_message.source_node.name}"
        if isinstance(element, Task):
            return f"{element.name}_END"
        return element.name  # type: ignore

    def _get_consume_locations(self, element: Node) -> List[str]:
        if not (element.in_flows or element.in_msgs):
            return [self._generate_location_label(element)]
        consume_locations: List[str] = []
        for flow in element.in_flows + element.in_msgs:
            consume_locations.append(self._generate_location_label(element, flow))

        return consume_locations

    def _get_put_locations(self, element: Node) -> List[str]:
        put_locations: List[str] = []
        for flow in element.out_flows + element.out_msgs:
            put_locations.append(self._generate_location_label(flow.target_node, flow))

        return put_locations

    def _build_guard(self, element: Node) -> StringManager:
        guard = PromelaGenVisitor.StringManager()
        guard.write_str(
            "("
            + "||".join(
                [f"hasToken({node})" for node in self._get_consume_locations(element)]
            )
            + ")",
            NL_NONE,
            IndentAction.NIL,
        )
        return guard

    def __repr__(self) -> str:
        return f"{self.defs}{self.init_proc_contents}{self.promela}"

    ####################
    # Visitor Methods
    ####################
    def visit_start_event(self, event: StartEvent) -> bool:
        self.promela.write_str(f"putToken({event.name})", NL_SINGLE, IndentAction.NIL)
        self.promela.write_str("do", NL_SINGLE, IndentAction.NIL)

        guard = self._build_guard(event)

        self.promela.write_str(str(guard), NL_SINGLE, IndentAction.NIL)
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
        self.init_proc_contents.write_str(
            f"run {process.name}()", NL_SINGLE, IndentAction.NIL
        )
        self.promela.write_str(
            f"proctype {process.name}() {{", NL_SINGLE, IndentAction.INC
        )
        self.promela.write_str("pid me = _pid", NL_SINGLE, IndentAction.NIL)
        return True

    def end_visit_process(self, process: Process) -> None:
        self.promela.write_str("}", NL_SINGLE, IndentAction.DEC)

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        self.defs.write_str(HELPER_FUNCS_STR, NL_DOUBLE, IndentAction.INC)
        self.init_proc_contents.write_str("init {", NL_SINGLE, IndentAction.INC)
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        self.init_proc_contents.write_str("}", NL_DOUBLE, IndentAction.DEC)
