from typing import List, Optional, Union
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

        def write_str(
            self,
            new_str: Union[str, "PromelaGenVisitor.StringManager"],
            nl: int = NL_NONE,
            indent_action: IndentAction = IndentAction.NIL,
        ) -> None:
            """
            Appends a string or the contents of a StringManager object to the internal contents list
            with specified newline and indentation behavior.
            """
            # Validate input for StringManager instance usage
            if isinstance(new_str, PromelaGenVisitor.StringManager):
                if nl != NL_NONE or indent_action != IndentAction.NIL:
                    raise ValueError(
                        "When passing a StringManager, nl must be NL_NONE and indent_action must be IndentAction.NIL"
                    )

            if indent_action == IndentAction.DEC:
                self._dec_indent()

            def needs_tab(idx: int, items: List[str]) -> bool:
                """Helper function to determine if tabulation is necessary."""
                # Check if it's the first item and if the last content line ends with a newline
                if idx == 0:
                    return bool(self.contents and self.contents[-1].endswith("\n"))
                # Check the previous item for a newline
                return items[idx - 1].endswith("\n")

            # Normalize the input into a list for consistent handling
            items = [new_str] if isinstance(new_str, str) else new_str.contents

            for idx, item in enumerate(items):
                tab_required = needs_tab(idx, items)
                newline_suffix = self._newline(nl) if isinstance(new_str, str) else ""
                self.contents.append(
                    f"{self._tab() if tab_required else ''}{item}{newline_suffix}"
                )

            if indent_action == IndentAction.INC:
                self._inc_indent()

        def __repr__(self) -> str:
            return "".join(self.contents)

    def __init__(self) -> None:
        self.defs = PromelaGenVisitor.StringManager()
        self.behaviors = PromelaGenVisitor.StringManager()
        self.init_proc_contents = PromelaGenVisitor.StringManager()
        self.promela = PromelaGenVisitor.StringManager()

    def _generate_location_label(
        self, element: Node, flow_or_message: Optional[Flow] = None
    ) -> str:
        """
        Generates a unique label for a node, indicating the source of flow.
        If multiple flows lead into the node, the label specifies the source element
        (e.g., 'Node1_FROM_Start'). If the node is a Task, the label ends with '_END'.
        """
        if flow_or_message:
            return f"{element.name}_FROM_{flow_or_message.source_node.name}"
        if isinstance(element, Task):
            return f"{element.name}_END"
        return element.name  # type: ignore

    def _get_consume_locations(self, element: Node) -> List[str]:
        """
        Returns a list of labels representing all incoming flows to a node.
        If there are no incoming flows, the node itself is returned as a label.
        Example: ['Node2_FROM_Start', 'Node2_FROM_Node1']
        """
        if not (element.in_flows or element.in_msgs):
            return [self._generate_location_label(element)]
        consume_locations: List[str] = [
            self._generate_location_label(element, flow)
            for flow in element.in_flows + element.in_msgs
        ]
        return consume_locations

    def _get_put_locations(self, element: Node) -> List[str]:
        """
        Returns a list of labels representing all outgoing flows from a node.
        Each label indicates the target node and the current node as the source.
        Example: ['Node2_FROM_Node1']
        """
        put_locations: List[str] = [
            self._generate_location_label(flow.target_node, flow)
            for flow in element.out_flows + element.out_msgs
        ]
        return put_locations

    def _build_guard(self, element: Node) -> StringManager:
        """
        Constructs a guard condition for an atomic block in a process.
        The guard checks whether a token exists at the current node, based on incoming flows.
        Example: (hasToken(Node2_FROM_Start) || hasToken(Node2_FROM_Node1))
        """
        guard = PromelaGenVisitor.StringManager()
        guard.write_str(
            "||".join(
                [f"hasToken({node})" for node in self._get_consume_locations(element)]
            )
        )
        return guard

    def _build_atomic_block(self, element: Node) -> StringManager:
        """
        This function builds an atomic block to execute the element's behavior,
        consume the token and move the token forward.
        """
        atomic_block = PromelaGenVisitor.StringManager()
        atomic_block.write_str(":: atomic { (")

        guard = self._build_guard(element)

        atomic_block.write_str(guard)
        atomic_block.write_str(") ->", NL_SINGLE, IndentAction.INC)
        atomic_block.write_str(f"{element.name}_BehaviorModel()", NL_SINGLE)
        atomic_block.write_str("d_step {", NL_SINGLE, IndentAction.INC)

        for location in self._get_consume_locations(element):
            atomic_block.write_str(f"consumeToken({location})", NL_SINGLE)

        for location in self._get_put_locations(element):
            atomic_block.write_str(f"putToken({location})", NL_SINGLE)

        atomic_block.write_str("}", NL_SINGLE, IndentAction.DEC)
        atomic_block.write_str("}", NL_SINGLE, IndentAction.DEC)

        return atomic_block

    def _gen_behavior_model(self, element: Node) -> None:
        self.behaviors.write_str(
            f"inline {element.name}_BehaviorModel(){{", NL_SINGLE, IndentAction.INC
        )
        self.behaviors.write_str("skip", NL_SINGLE)
        self.behaviors.write_str("}", NL_DOUBLE, IndentAction.DEC)

    def __repr__(self) -> str:
        return f"{self.defs}{self.behaviors}{self.init_proc_contents}{self.promela}"

    ####################
    # Visitor Methods
    ####################
    def visit_start_event(self, event: StartEvent) -> bool:
        self._gen_behavior_model(event)
        self.promela.write_str(f"putToken({event.name})", NL_SINGLE, IndentAction.NIL)
        self.promela.write_str("do", NL_SINGLE, IndentAction.NIL)

        atomic_block = self._build_atomic_block(event)

        self.promela.write_str(atomic_block)
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        self._gen_behavior_model(event)
        atomic_block = self._build_atomic_block(event)

        self.promela.write_str(atomic_block)
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self._gen_behavior_model(event)
        atomic_block = self._build_atomic_block(event)

        self.promela.write_str(atomic_block)
        return True

    def visit_task(self, task: Task) -> bool:
        self._gen_behavior_model(task)
        atomic_block = self._build_atomic_block(task)

        self.promela.write_str(atomic_block)
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self._gen_behavior_model(gateway)
        atomic_block = self._build_atomic_block(gateway)

        self.promela.write_str(atomic_block)
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self._gen_behavior_model(gateway)
        atomic_block = self._build_atomic_block(gateway)

        self.promela.write_str(atomic_block)
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
