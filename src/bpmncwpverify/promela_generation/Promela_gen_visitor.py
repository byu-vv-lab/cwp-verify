"""
#########################################

Class and methods to generate a workflow model in Promela
using a BPMN object.

###########################################
"""

from typing import List, Optional, Union

from bpmncwpverify.state import SymbolTable
from returns.pipeline import is_successful
from bpmncwpverify.bpmn.BPMN import (
    Flow,
    Msg,
    EventNode,
    ActivityNode,
    Node,
    StartNode,
    GatewayNode,
    XorGatewayNode,
    ParallelGatewayJoinNode,
    ParallelGatewayForkNode,
    EndNode,
    MsgIntermediateNode,
    TimerIntermediateNode,
    Model,
    Process,
    BpmnVisitor,
)
from bpmncwpverify.xml_ingest.BPMNXMLIngestor import BPMNXMLIngestor
import sys
import os


class PromelaGenVisitor(BpmnVisitor):
    token_helpers = """#define hasToken(place) (place != 0)

    #define putToken(place) place = 1

    #define consumeToken(place) place = 0

    """

    temp_helpers = ""

    def __init__(self, printf_on: bool = False) -> None:
        self.printf_on = printf_on
        self.temp_helpers = self.temp_helpers
        self.helper_funcs = self.token_helpers
        self.constants_text = ""
        self.places_text = ""
        self.behavior_model_text = ""
        self.workflow_text = ""
        self.init_text = ""
        self.constants_indent = 0
        self.places_indent = 0
        self.behavior_model_indent = 0
        self.workflow_indent = 0
        self.init_indent = 0
        self.flow_places: List[str] = []

    def generate_log_counter_example_path(self, element_id: str) -> str:
        log_path = ""
        if self.printf_on:
            log_path += '\t\t\tprintf("###COUNTEREXAMPLE PATH OUTPUT###\\n")\n'
            log_path += '\t\t\tprintf("traversed element ID: {x}\\n")\n'.format(
                x=element_id
            )
            log_path += "\t\t\tlogState()\n"
            log_path += '\t\t\tprintf("###END OUTPUT###\\n")\n'
        return log_path

    def create_option(
        self,
        guard: str,
        consume_locations: List[str],
        behavior_inline: str,
        put_conditions: List[str],
        put_locations: List[str],
        put_flow_ids: List[str],
        element_id: str,
        element_type: str = "",
    ) -> str:
        option = ":: atomic {{ {x} -> \n".format(x=guard)
        option += "\t\t{x}\n".format(x=behavior_inline)
        option += "\t\td_step {\n"
        for location in consume_locations:
            option += "\t\t\tconsumeToken({x})\n".format(x=location)

        if "ParallelFALSE" in element_type:
            option += "\t\t\tif\n"
            option += "\t\t\t:: (locked[me]) -> locked[me] = false; unlock()\n"
            option += "\t\t\t:: (!locked[me]) -> locked[me] = true; lock(me)\n"
            option += "\t\t\tfi\n"

        option += self.generate_log_counter_example_path(element_id)

        if element_type == "XOR":
            option += "\t\t\tif\n"
            for condition, location, flow_id in zip(
                put_conditions, put_locations, put_flow_ids
            ):
                option += "\t\t\t\t:: {x} -> putToken({y})\n".format(
                    x=condition, y=location
                )
                option += self.generate_log_counter_example_path(flow_id)
            option += "\t\t\tfi\n"
        else:
            for location, flow_id in zip(put_locations, put_flow_ids):
                option += "\t\t\tputToken({x})\n".format(x=location)
                option += self.generate_log_counter_example_path(flow_id)

        if "ParallelFALSE" in element_type:
            option += "\t\t\tif\n"
            option += (
                '\t\t\t:: (!locked[me]) -> printf("###END PARALLEL GATEWAY###\\n")\n'
            )
            option += (
                '\t\t\t:: (locked[me]) -> printf("###START PARALLEL GATEWAY###\\n")\n'
            )
            option += "\t\t\tfi\n"

        option += "\t\t}\n"
        option += "\t}"
        return option

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

    def generate_xor_has_option_macro(self, gateway: XorGatewayNode) -> None:
        macro = "#define {}_hasOption \\\n".format(gateway.label)
        conditions = [str(flow.label) for flow in gateway.out_flows]
        macro += "(\\\n\t"
        macro += "||\\\n\t".join(conditions)
        macro += "\\\n)\n"
        self.write_constants_lines(macro)

    def generate_activation_option(
        self, element: Node, start_guard: str = "", element_type: str = ""
    ) -> None:
        guard = "("
        consume_locations: List[str] = []
        put_locations: List[str] = []
        behavior_inline = "skip"
        put_conditions: List[str] = []
        put_flow_ids: List[str] = []

        if element.id:
            element_id = element.id
        else:
            raise Exception("element does not have id")

        if element_type == "Task-END":
            consume_locations.append(self.get_location(element))
            guard += "hasToken({})".format(self.get_location(element))
        else:
            for flow in element.in_flows:
                consume_locations.append(self.get_location(element, flow))
            if element.in_flows:
                guard += "( "
                if element_type == "Parallel-join":
                    guard += "&&".join(
                        [
                            "hasToken({})".format(self.get_location(element, loc))
                            for loc in element.in_flows
                        ]
                    )
                else:
                    guard += "||".join(
                        [
                            "hasToken({})".format(self.get_location(element, loc))
                            for loc in element.in_flows
                        ]
                    )
                guard += " )\n"

        if element_type != "Task":
            for msg in element.in_msgs:
                consume_locations.append(self.get_location(element, msg))
            if element.in_msgs or element_type == "Task-END":
                guard += "&&"
                guard += "( "
                guard += "&&".join(
                    [
                        "hasToken({})".format(self.get_location(element, loc))
                        for loc in element.in_msgs
                    ]
                )
                guard += " )\n"

        if element_type == "XOR":
            guard += "\t&&"
            guard += "\t({}_hasOption)".format(element.label)
        guard += ")"

        if element_type != "Task-END":
            behavior_inline = "{x}_BehaviorModel()".format(x=element.label)

        if element_type == "Task":
            put_flow_ids.append(element_id)
            put_locations.append(self.get_location(element))
            for msg in element.out_msgs:
                if msg.id:
                    put_flow_ids.append(msg.id)
                else:
                    raise Exception("msg does not have id")
                put_locations.append(self.get_location(msg.to_node, msg))
        else:
            for flow in element.out_flows:
                if flow.id:
                    put_flow_ids.append(flow.id)
                else:
                    raise Exception("flow does not have id")
                put_locations.append(self.get_location(flow.to_node, flow))
                if element_type == "XOR":
                    put_conditions.append(str(flow.label))
            if element_type != "Task-END":
                for msg in element.out_msgs:
                    if msg.id:
                        put_flow_ids.append(msg.id)
                    else:
                        raise Exception("msg does not have id")
                    put_locations.append(self.get_location(msg.to_node, msg))

        if start_guard:
            guard = start_guard
            consume_locations.append(self.get_location(element))

        self.write_workflow_lines(
            self.create_option(
                guard,
                consume_locations,
                behavior_inline,
                put_conditions,
                put_locations,
                put_flow_ids,
                element_id,
                element_type,
            )
        )

    def generate_places(self, element: Node) -> None:
        if not element.in_flows and not element.in_msgs:
            self.flow_places.append(self.get_location(element))
        else:
            for flow in element.in_flows:
                self.flow_places.append(self.get_location(element, flow))
            for msg in element.in_msgs:
                self.flow_places.append(self.get_location(element, msg))
        if isinstance(element, ActivityNode):
            self.flow_places.append(self.get_location(element))

    # Visitor methods below are the same, following the snake_case refactoring

    def visit_node(self, element: Node) -> None:
        if element.seen:
            return
        element.seen = True
        self.generate_places(element)
        self.generate_activation_option(element)
        for flow in element.out_flows:
            flow.accept(self)

    # The other visit methods can follow the same pattern as the above method.

    # Helper functions (e.g., `get_location`) also remain refactored as needed.

    def visit_gateway_node(self, element: GatewayNode) -> None:
        pass

    def visit_flow(self, element: Flow) -> None:
        if element.seen:
            return
        element.seen = True
        target = element.to_node

        if target:
            target.accept(self)
        else:
            raise Exception("Exception in visit flow: element.toNode = None")

    def visit_msg(self, element: Msg) -> None:
        if element.seen:
            return
        element.seen = True
        self.flow_places.append(element.label)

    def visit_event_node(self, element: EventNode) -> None:
        self.visit_node(element)

    def visit_activity_node(self, element: ActivityNode) -> None:
        if element.seen:
            return
        element.seen = True
        self.generate_places(element)
        self.generate_activation_option(element, element_type="Task")
        self.generate_activation_option(element, element_type="Task-END")
        for flow in element.out_flows:
            flow.accept(self)

    def visit_xor_gateway_node(self, element: XorGatewayNode) -> None:
        if element.seen:
            return
        element.seen = True
        self.generate_places(element)
        if len(element.out_flows) == 1:
            self.generate_activation_option(element, element_type="XOR-JOIN")
        else:
            self.generate_xor_has_option_macro(element)
            self.generate_activation_option(element, element_type="XOR")
        for flow in element.out_flows:
            flow.accept(self)

    def visit_parallel_gateway_join_node(
        self, element: ParallelGatewayJoinNode
    ) -> None:
        if element.seen:
            return
        element.seen = True
        self.generate_places(element)
        self.generate_activation_option(element, element_type="Parallel-join")
        for flow in element.out_flows:
            flow.accept(self)

    def visit_parallel_gateway_fork_node(
        self, element: ParallelGatewayForkNode
    ) -> None:
        if element.seen:
            return
        element.seen = True
        self.generate_places(element)
        self.generate_activation_option(element, element_type="Parallel-fork")
        for flow in element.out_flows:
            flow.accept(self)

    def visit_timer_intermediate_node(self, element: TimerIntermediateNode) -> None:
        self.visit_node(element)

    def visit_msg_intermediate_node(self, element: MsgIntermediateNode) -> None:
        self.visit_node(element)

    def visit_start_node(self, element: StartNode) -> None:
        if element.seen:
            return
        element.seen = True
        if element.in_msgs:
            self.generate_places(element)
            self.generate_activation_option(element)
        else:
            self.generate_places(element)
            guard = "(hasToken({}))".format(element.label)
            self.generate_activation_option(element, start_guard=guard)
        for flow in element.out_flows:
            flow.accept(self)

    def visit_end_node(self, element: EndNode) -> None:
        if element.seen:
            print("already seen this end node")
            return
        element.seen = True
        self.generate_places(element)
        self.generate_activation_option(element)

    def visit_process(self, element: Process) -> None:
        self.write_workflow_lines("proctype {x}() {{".format(x=element.name))
        self.workflow_indent += 1
        # self.writeWorkflowLines("updateState()")
        self.write_workflow_lines("pid me = _pid")
        for startNode in element.start_state_list:
            if not startNode.in_msgs:
                self.write_workflow_lines("putToken({x})".format(x=startNode.label))
        self.write_workflow_lines("do")
        # self.workflowIndent += 1
        # self.writeWorkflowLines(":: true ->")
        # self.writeWorkflowLines("if")
        # self.writeWorkflowLines(":: (!mutex[me]) -> ")
        # self.workflowIndent += 1
        # self.writeWorkflowLines("if")
        for startNode in element.start_state_list:
            startNode.accept(self)
        # self.writeWorkflowLines("fi")
        # self.workflowIndent -= 1
        # self.writeWorkflowLines("fi")
        # self.workflowIndent -= 1
        self.write_workflow_lines("od")
        self.workflow_indent -= 1
        self.write_workflow_lines("}")

    def visit_model(self, element: Model) -> None:
        # self.writeConstantsLines("#define NUM_PROCS {}".format(len(element.processList)))
        # self.writeConstantsLines("bool mutex[NUM_PROCS] = false")
        # self.writeConstantsLines("bool locked[NUM_PROCS] = false")
        # mutexUnlockText = "inline unlock(){\n"
        # mutexLockText = "inline lock(proc){\n"
        # for i in range(len(element.processList)):
        # mutexUnlockText += "\tmutex[{}] = 0\n".format(i)
        # mutexLockText += "\tmutex[{}] = 1\n".format(i)
        # mutexLockText += "\tmutex[proc] = 0\n"
        # mutexUnlockText += "}"
        # mutexLockText += "}"
        # self.writeConstantsLines(mutexUnlockText)
        # self.writeConstantsLines(mutexLockText)
        initLines = "init {\n"
        initLines += "\tatomic{\n"
        initLines += "\t\tupdateState()\n"
        for process in element.process_list:
            initLines += "\t\trun {}()\n".format(process.name)
        initLines += "\t}\n"
        initLines += "}\n\n"
        self.write_init_lines(initLines)
        for process in element.process_list:
            process.accept(self)
        for place in self.flow_places:
            self.write_places_lines("bit {x} = 0".format(x=str(place)))

    def get_location(
        self, element: Optional[Node], flow_or_msg: Optional[Union[Msg, Flow]] = None
    ) -> str:
        if not element:
            return "Error: element provided = None"
        if flow_or_msg and flow_or_msg.from_node:
            return str(element.label) + "_FROM_" + str(flow_or_msg.from_node.label)
        else:
            if isinstance(element, ActivityNode):
                return str(element.label) + "_END"
            else:
                return str(element.label)

    def __repr__(self) -> str:
        return (
            self.constants_text
            + "\n\n"
            + self.temp_helpers
            + "\n\n"
            + self.helper_funcs
            + "\n\n"
            + self.places_text
            + "\n\n"
            + self.behavior_model_text
            + "\n\n"
            + self.init_text
            + "\n\n"
            + self.workflow_text
            + "\n\n"
        )


def main(argv: List[str]) -> None:
    bpmn_namespace_map = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}

    def read_state(state_file: str) -> str:
        with open(state_file) as f:
            return f.read()

    path = os.path.abspath(os.getcwd())
    result = SymbolTable.build(read_state(path + "/src/bpmncwpverify/state.txt"))
    assert is_successful(result)
    symbol_table: SymbolTable = result.unwrap()
    ingestor = BPMNXMLIngestor(symbol_table=symbol_table, ns=bpmn_namespace_map)
    ingestor.parse_input(argv)
    BPMNModel = ingestor.process_xml()
    myVisitor = PromelaGenVisitor()
    BPMNModel.accept(myVisitor)
    myVisitor.behavior_model_text = ingestor.create_inline_stub_file()
    with open("hello.pml", "w+") as f:
        f.write(str(myVisitor))


if __name__ == "__main__":
    main(sys.argv[1:])
