from typing import List, Optional
import graphviz
from bpmncwpverify.state import SymbolTable
from bpmncwpverify.cwp import CwpVisitor, CwpState, CwpEdge, Cwp
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
    BpmnElement,
    Node,
    Activity,
    Flow,
)

##############
# Constants
##############
HELPER_FUNCS = "#define hasToken(place) (place != 0)\n\n#define putToken(place) place = 1\n\n#define consumeToken(place) place = 0\n"
##############


class GraphVizVisitor(BpmnVisitor):  # type: ignore
    def __init__(self, process_number: int) -> None:
        self.dot = graphviz.Digraph(comment="Process graph {}".format(process_number))

    def visit_start_event(self, event: StartEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def end_visit_start_event(self, event: StartEvent) -> None:
        pass

    def visit_end_event(self, event: EndEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def end_visit_end_event(self, event: EndEvent) -> None:
        pass

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def end_visit_intermediate_event(self, event: IntermediateEvent) -> None:
        pass

    def visit_task(self, task: Task) -> bool:
        self.dot.node(task.id, task.name)
        return True

    def end_visit_task(self, task: Task) -> None:
        pass

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        self.dot.node(subprocess.id, subprocess.name)
        return True

    def end_visit_sub_process(self, subprocess: SubProcess) -> None:
        pass

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self.dot.node(gateway.id, gateway.name)
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self.dot.node(gateway.id, gateway.name)
        return True

    def end_visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        self.dot.edge(flow.source_node.id, flow.target_node.id, label=flow.name)
        pass

    def visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        self.dot.edge(flow.source_node.id, flow.target_node.id, label=flow.name)
        pass

    def visit_process(self, process: Process) -> None:
        pass

    def end_visit_process(self, process: Process) -> None:
        pass

    def visit_bpmn(self, bpmn: Bpmn) -> None:
        pass

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        for msg_id, msg_flow in bpmn.inter_process_msgs.items():
            self.dot.edge(
                msg_flow.source_node.id, msg_flow.target_node.id, label="message_flow"
            )


class PromelaGenVisitor(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.init_text = ""
        self.places_text = ""
        self.constants_text = ""
        self.behavior_model_text = ""
        self.workflow_text = ""
        self.workflow_indent = 0
        self.flow_places: List[str] = []

    ####################
    # Helper Methods
    ####################
    def __repr__(self) -> str:
        return (
            self.constants_text
            + "\n\n"
            + HELPER_FUNCS
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

    def gen_excl_gw_has_option_macro(self, gateway: ExclusiveGatewayNode) -> None:
        macro = "#define {}_hasOption \\\n".format(gateway.name)
        conditions = [str(flow.name) for flow in gateway.out_flows]
        macro += "(\\\n\t"
        macro += "||\\\n\t".join(conditions)
        macro += "\\\n)\n"
        self.write_constants_lines(macro)

    def write_places_lines(self, text: str) -> None:
        self.places_text += "".join(("\n" + text.lstrip()).splitlines(True))

    def write_constants_lines(self, text: str) -> None:
        self.constants_text += "".join(("\n" + text.lstrip()).splitlines(True))

    def write_behavior_model_lines(self, text: str) -> None:
        self.behavior_model_text += "".join(("\n" + text.lstrip()).splitlines(True))

    def write_init_lines(self, text: str) -> None:
        self.init_text += "".join(("\n" + text.lstrip()).splitlines(True))

    def write_workflow_lines(self, text: str) -> None:
        self.workflow_text += "".join(("\n" + text.lstrip()).splitlines(True))

    def get_location(
        self, element: BpmnElement, flow_or_msg: Optional[Flow] = None
    ) -> str:
        if flow_or_msg:
            return element.name + "_FROM_" + flow_or_msg.source_node.name  # type: ignore
        else:
            if isinstance(element, Activity):
                return element.name + "_END"  # type: ignore
            else:
                return element.name  # type: ignore

    def gen_places(self, element: Node) -> None:
        if not element.in_flows and not element.in_msgs:
            self.flow_places.append(self.get_location(element))
        else:
            for flow in element.in_flows:
                self.flow_places.append(self.get_location(element, flow))
            for msg in element.in_msgs:
                self.flow_places.append(self.get_location(element, msg))
        if isinstance(element, Activity):
            self.flow_places.append(self.get_location(element))

    def create_option(
        self,
        guard: str,
        consume_locations: List[str],
        behavior_inline: str,
        put_conditions: List[str],
        put_locations: List[str],
        put_flow_ids: List[str],
        element_id: str,
        type: str = "",
    ) -> str:
        ret = ":: atomic {{ {x} -> \n".format(x=guard)
        ret += "\t\t{x}\n".format(x=behavior_inline)
        ret += "\t\td_step {\n"
        for location in consume_locations:
            ret += "\t\t\tconsume_token({x})\n".format(x=location)
        if "ParallelFALSE" in type:
            ret += "\t\t\tif\n"
            ret += "\t\t\t:: (locked[me]) -> locked[me] = false; unlock()\n"
            ret += "\t\t\t:: (!locked[me]) -> locked[me] = true; lock(me)\n"
            ret += "\t\t\tfi\n"

        if type == "XOR":
            ret += "\t\t\tif\n"
            for condition, location, id in zip(
                put_conditions, put_locations, put_flow_ids
            ):
                ret += "\t\t\t\t:: {x} -> put_token({y})\n".format(
                    x=condition, y=location
                )
            ret += "\t\t\tfi\n"
        else:
            for location, id in zip(put_locations, put_flow_ids):
                ret += "\t\t\tput_token({x})\n".format(x=location)
        if "ParallelFALSE" in type:
            ret += "\t\t\tif\n"
            ret += '\t\t\t:: (!locked[me]) -> printf("###END PARALLEL GATEWAY###\\n")\n'
            ret += (
                '\t\t\t:: (locked[me]) -> printf("###START PARALLEL GATEWAY###\\n")\n'
            )
            ret += "\t\t\tfi\n"
        ret += "\t\t}\n"
        ret += "\t}"
        return ret

    def gen_activation_option(
        self, element: Node, start_guard: str = "", option_type: str = ""
    ) -> None:
        guard: str = "("
        consume_locations: List[str] = []
        put_locations: List[str] = []
        behavior_inline: str = "skip"
        put_conditions: List[str] = []
        put_flow_ids: List[str] = []
        element_id: str = element.id
        if option_type == "Task-END":
            consume_locations.append(self.get_location(element))
            guard += "hasToken({})".format(self.get_location(element))
        else:
            for flow in element.in_flows:
                consume_locations.append(self.get_location(element, flow))
            if element.in_flows:
                guard += "( "
                if option_type == "Parallel-join":
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
        if option_type != "Task":
            for msg in element.in_msgs:
                consume_locations.append(self.get_location(element, msg))
            if element.in_msgs:
                if element.in_flows or option_type == "Task-END":
                    guard += "&&"
                guard += "( "
                guard += "&&".join(
                    [
                        "hasToken({})".format(self.get_location(element, loc))
                        for loc in element.in_msgs
                    ]
                )
                guard += " )\n"
        if option_type == "XOR":
            guard += "\t&&"
            guard += "\t({}_hasOption)".format(element.name)
        guard += ")"
        if option_type != "Task-END":
            behavior_inline = "{x}_BehaviorModel()".format(x=element.name)
        if option_type == "Task":
            put_flow_ids.append(element_id)
            put_locations.append(self.get_location(element))
            for msg in element.out_msgs:
                put_flow_ids.append(msg.id)
                put_locations.append(self.get_location(msg.target_node, msg))
        else:
            for flow in element.out_flows:
                put_flow_ids.append(flow.id)
                put_locations.append(self.get_location(flow.target_node, flow))
                if option_type == "XOR":
                    put_conditions.append(flow.name)
            if option_type != "Task-END":
                for msg in element.out_msgs:
                    put_flow_ids.append(msg.id)
                    put_locations.append(self.get_location(msg.target_node, msg))
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
                option_type,
            )
        )

    def gen_behavior_model(self, place_name: str, update_state: bool = False) -> str:
        ret = "//{}\n".format(place_name)
        ret += "inline {x}_BehaviorModel(){{\n".format(x=place_name)
        # TODO: figure out how to do this without modifies file
        # if update_state:
        #     # vars_to_modify = self.modifies_clauses.get(place_name, [])
        #     for var_name in vars_to_modify:
        #         var = [var for var in self.var_list if var.bpmn == var_name][0]
        #         possible_vals = var.possible_values
        #         ret += "\tif\n"
        #         for val in possible_vals:
        #             ret += "\t\t:: true -> {var} = {val}\n".format(
        #                 var=var_name, val=val
        #             )
        #         ret += "\tfi\n"
        #     ret += "\tupdateState()\n"
        # else:
        ret += "\tskip\n"
        ret += "}\n\n"
        return ret

    ####################
    # Visitor Methods
    ####################
    def visit_node(self, element: Node, is_task: bool = False) -> None:
        update_state = isinstance(element, Task)
        self.behavior_model_text += self.gen_behavior_model(
            self.get_location(element), update_state=update_state
        )
        if not is_task:
            self.gen_places(element)
            self.gen_activation_option(element)
        else:
            self.gen_places(element)
            self.gen_activation_option(element, option_type="Task")
            self.gen_activation_option(element, option_type="Task-END")

    def visit_start_event(self, event: StartEvent) -> bool:
        if event.in_msgs:
            self.visit_node(event)
        else:
            self.gen_places(event)
            guard = "(hasToken({}))".format(event.name)
            self.gen_activation_option(event, start_guard=guard)
        return True

    def end_visit_start_event(self, event: StartEvent) -> None:
        pass

    def visit_end_event(self, event: EndEvent) -> bool:
        self.visit_node(event)
        self.behavior_model_text += self.gen_behavior_model(
            self.get_location(event), update_state=False
        )
        return False

    def end_visit_end_event(self, event: EndEvent) -> None:
        pass

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self.visit_node(event)
        return True

    def end_visit_intermediate_event(self, event: IntermediateEvent) -> None:
        pass

    def visit_task(self, task: Task) -> bool:
        self.visit_node(task, is_task=True)
        return True

    def end_visit_task(self, task: Task) -> None:
        pass

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        return True

    def end_visit_sub_process(self, subprocess: SubProcess) -> None:
        pass

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self.gen_activation_option(gateway)
        if len(gateway.out_flows) == 1:
            self.gen_activation_option(gateway, option_type="XOR-JOIN")
        else:
            self.gen_excl_gw_has_option_macro(gateway)
            self.gen_activation_option(gateway, option_type="XOR")
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self.gen_places(gateway)
        option_type = "Parallel-fork" if gateway.is_fork else "Parallel-join"
        self.gen_activation_option(gateway, option_type=option_type)
        return True

    def end_visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def visit_message_flow(self, flow: MessageFlow) -> None:
        self.flow_places.append(flow.name)

    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def visit_process(self, process: Process) -> None:
        self.write_workflow_lines("proctype {x}() {{".format(x=process.id))
        self.workflow_indent += 1
        self.write_workflow_lines("pid me = _pid")
        for start_node in process.get_start_states().values():
            self.write_workflow_lines("putToken({x})".format(x=start_node.name))
        self.write_workflow_lines("do")

    def end_visit_process(self, process: Process) -> None:
        self.write_workflow_lines("od")
        self.workflow_indent -= 1
        self.write_workflow_lines("}")

    def visit_bpmn(self, bpmn: Bpmn) -> None:
        init_lines = "init {\n\tatomic{\n\t\tupdateState()\n"
        for process in bpmn.processes.values():
            init_lines += "\t\trun {}()\n".format(process.name)
        init_lines += "\t}\n}\n\n"
        self.write_init_lines(init_lines)

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        for place in self.flow_places:
            self.write_places_lines("bit {x} = 0".format(x=str(place)))


class CwpGraphVizVisitor(CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.dot = graphviz.Digraph(comment="cwp graph")

    def visit_state(self, state: CwpState) -> None:
        self.dot.node(state.name, state.name)

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> None:
        if edge.source:
            self.dot.edge(edge.source.name, edge.dest.name, label=edge.expression)
        else:
            self.dot.edge("start", edge.dest.name, label=edge.expression)

    def end_visit_edge(self, edge: CwpEdge) -> None:
        pass

    def visit_cwp(self, model: Cwp) -> None:
        pass

    def end_visit_cwp(self, model: Cwp) -> None:
        pass


class CwpLtlVisitor(CwpVisitor):  # type: ignore
    def __init__(self, symbol_table: SymbolTable, print_on: bool = False) -> None:
        self.state_info: List[str] = []
        self.symbol_table = symbol_table
        self.output_str: List[str] = []
        self.print_on: bool = print_on
        self.property_list: List[str] = []
        self.cwp: Cwp
        self.debug: bool = False
        self.tab = 0

    def generate_all(self) -> None:
        self.generate_helper_functions()
        self.generate_LTL()

    def generate_helper_functions(self) -> None:
        self.write_state_variables()
        self.write_variable_range_invariants()
        self.write_init_states()
        self.write_edge_definitions()
        self.write_update_state()
        if self.print_on:
            self.write_log_state_inline()

    def generate_LTL(self) -> None:
        self.write_global_properties()
        for state in self.cwp.states.values():
            self.write_state_properties(state)
        self.write_line("")
        self.write_line("")
        self.write_line("")

    def write_state_variables(self) -> None:
        self.write_line("\n\n//**********VARIABLE DECLARATION************//\n")
        for name, value in self.symbol_table._consts.items():
            self.write_line(f"#define {name} {value[1]}")
            self.write_line("\n")
        self.write_line("\n")
        for enum in self.symbol_table._enums.values():
            self.write_line(f"mytpe = {{{' '.join([value for value in enum])}}}")
            self.write_line("\n")
        for name, value in self.symbol_table._vars.items():
            if len(value) == 3:
                self.write_line(f"mytype {value[0]} = {value[1]}")
            else:
                self.state_info.append(f"{value[0]} {name} = {value[0]}")
            self.write_line("\n")

        self.write_line("\n")

    def write_variable_range_invariants(self) -> None:
        self.state_info.append(
            "\n\n//**********Variable Range Invariants************//"
        )
        for enum_name, enum in self.symbol_table._enums.items():
            # if enum.isConstant:
            #     continue
            # cwp = enum.cwp
            invariant = "("
            for value in enum:
                if isinstance(value, int) or isinstance(value, str):
                    invariant += "({enum_name} == {value}) || ".format(
                        enum_name=enum_name, value=value
                    )
                else:
                    # TODO: see if range is included in new state syntax
                    pass
                    # valRange = value
                    # invariant += "({cwp} >= {min} && {cwp} <= {max}) || ".format(
                    #     cwp=cwp, min=valRange.min, max=valRange.max
                    # )

            invariant = invariant[:-4]
            invariant += ")"
            self.write_line("#define {}Invariant {}".format(enum_name, invariant))

    def write_init_states(self) -> None:
        self.write_line("\n\n//**********STATE VARIABLE DECLARATION************//")
        for state in self.cwp.states.values():
            if "init" in state.name.lower():
                self.write_line("bit {name} = 1".format(name=state.name))
            else:
                self.write_line("bit {name} = 0".format(name=state.name))

    def write_edge_definitions(self) -> None:
        self.write_line("\n\n//**********EDGE DECLARATION************//")
        for edge in self.cwp.edges.values():
            self.write_line("bit {name} = 0".format(name=edge.name))

    def write_update_state(self) -> None:
        self.write_line("\n\n//**********UPDATE STATE INLINE************//")
        self.write_line("inline updateState() {")
        self.tab += 1
        self.write_line("d_step {")
        self.tab += 1
        self.tab -= 1
        self.write_line("}")
        self.tab -= 1
        self.write_line("}")

    def write_variable_range_assertions(self) -> None:
        for var_name in self.symbol_table._vars.keys():
            self.write_line("assert({}Invariant)".format(var_name))

    def write_refresh_edges(self) -> None:
        for edge in self.cwp.edges.values():
            self.write_line("if")
            self.write_line(":: ({}) -> ".format(edge.expression))
            self.tab += 1
            self.write_line("{} = 1".format(edge.name))
            self.tab -= 1
            self.write_line(":: else -> ")
            self.tab += 1
            self.write_line("{} = 0".format(edge.name))
            self.tab -= 1
            self.write_line("fi")

    def write_refresh_states(self) -> None:
        for state in self.cwp.states.values():
            self.write_line("{} = ".format(state.name))
            self.tab += 1
            self.write_line("(")
            self.tab += 1

            # USE ONE OF THE FOLLOWING TWO

            # Conjunction of incoming
            if state.in_edges:
                self.write_line(
                    "(" + " && ".join([edge.name for edge in state.in_edges]) + ")"
                )

            # Disjunction of incoming
            # self.write_line("(" + " || ".join(state.inEdges) + ")")

            # Conjuncted with
            if state.in_edges and state.out_edges:
                self.write_line("&&")

            # Negated Disjunction of outgoing
            if state.out_edges:
                self.write_line(
                    "(! (" + " || ".join([edge.name for edge in state.out_edges]) + "))"
                )

            self.tab -= 1
            self.write_line(")")
            self.tab -= 1

    def write_global_properties(self) -> None:
        self.write_line("//**********GLOBAL PROPERTIES************//")
        self.write_ina_state_property()
        self.write_fair_property()
        self.write_line("")
        self.write_line("")

    def write_ina_state_property(self) -> None:
        self.property_list.append("alwaysInAState")
        self.write_line(
            "#define inAState "
            + " \\\n || ".join([state.name for state in self.cwp.states.values()])
        )
        self.write_line("ltl alwaysInAState {(always (inAState))}")

    def write_fair_property(self) -> None:
        self.property_list.append("fairPathExists")
        if self.debug:
            self.write_line("#define fair (true)")
        else:
            self.write_line(
                "#define fair (eventually ("
                + " || ".join([state.name for state in self.cwp.end_states])
                + "))"
            )
        self.write_line("ltl fairPathExists {(always (! fair))}")

    def write_state_properties(self, state: CwpState) -> None:
        self.write_line(
            "//**********{} STATE PROPERTIES************//".format(state.name)
        )
        self.write_exists_property(state)
        self.write_mutex_property(state)
        self.write_edges_property(state)
        self.write_line("")
        self.write_line("")

    def write_exists_property(self, state: CwpState) -> None:
        self.property_list.append("{}Exists".format(state.name))
        self.write_line(
            "ltl {name}Exists {{(fair implies (always (! {name})))}}".format(
                name=state.name
            )
        )

    def write_mutex_property(self, state: CwpState) -> None:
        self.property_list.append("{}Mutex".format(state.name))
        self.write_line("ltl {}Mutex {{".format(state.name))
        self.tab += 1
        self.write_line("(")
        self.tab += 1
        self.write_line("always (")
        self.tab += 1
        self.write_line("{} implies (".format(state.name))
        self.tab += 1
        self.write_line("{}".format(state.name))
        joinString = (")\n" + "\t" * self.tab) + "&& (! "
        self.write_line(
            "&& (! "
            + joinString.join(
                [x.name for x in self.cwp.states.values() if x is not state]
            )
            + ")"
        )
        self.tab -= 1
        self.write_line(")")
        self.tab -= 1
        self.write_line(")")
        self.tab -= 1
        self.write_line(")")
        self.tab -= 1
        self.write_line("}")

    def write_log_state_inline(self) -> None:
        if self.print_on:
            self.write_line("\n\n//**********LOG STATE************//\n\n")
        else:
            self.write_line("\n\n//***********LOG STATE FILLER*******//\n\n")

        self.write_line("inline logState(){")
        self.tab += 1

        if self.print_on:
            self.write_line('printf("******************************\\n")')
        else:
            self.write_line("skip")

        for state in self.cwp.states.values():
            self.write_log_state(state)
        for edge in self.cwp.edges.values():
            self.write_log_edge(edge)
        for var in self.symbol_table._vars.keys():
            self.write_log_var(var)
        if self.print_on:
            self.write_line('printf("******************************\\n")')
        else:
            self.write_line("skip")
        self.tab -= 1
        self.write_line("}")

    def write_log_var(self, var_name: str) -> None:
        if self.print_on:
            self.write_line('printf("**VAR {bpmn} = ")'.format(bpmn=var_name))
            self.write_line("printm({})".format(var_name))
            self.write_line('printf("\\n")')
        else:
            self.write_line("skip")
            self.write_line("skip")
            self.write_line("skip")

    def write_log_state(self, state: CwpState) -> None:
        self.write_line("if")
        self.write_line(":: ({}) -> ".format(state.name))
        self.tab += 1
        if self.print_on:
            self.write_line(
                'printf("**STATE {name}({id})\\n")'.format(name=state.name, id=state.id)
            )
        else:
            self.write_line("skip")
        self.tab -= 1
        self.write_line(":: else -> skip")
        self.write_line("fi")

    def write_log_edge(self, edge: CwpEdge) -> None:
        if self.print_on:
            self.write_line(
                'printf("**EDGE {id}({parent_id}) = %d\\n", {name})'.format(
                    id=edge.id, parent_id=edge.parent_id, name=edge.name
                )
            )
        else:
            self.write_line("skip")

    def write_edges_property(self, state: CwpState) -> None:
        self.property_list.append("{}Edges".format(state.name))
        outStates = [edge.dest for edge in state.out_edges]
        self.write_line("ltl {}Edges {{".format(state.name))
        self.tab += 1
        self.write_line("(")
        self.tab += 1
        self.write_line("fair implies (")
        self.tab += 1
        self.write_line("always (")
        self.tab += 1
        self.write_line("{} implies (".format(state.name))
        self.tab += 1
        if outStates:
            self.write_line("{} until (".format(state.name))
            self.tab += 1
            joinString = "\n" + ("\t" * self.tab) + "|| "
            self.write_line(joinString.join([s.name for s in outStates]))
            self.tab -= 1
            self.write_line(")")
        else:
            self.write_line("always {}".format(state.name))
        self.tab -= 1
        self.write_line(")")
        self.tab -= 1
        self.write_line(")")
        self.tab -= 1
        self.write_line(")")
        self.tab -= 1
        self.write_line(")")
        self.tab -= 1
        self.write_line("}")

    def write_line(self, line: str) -> None:
        self.output_str.append("\t" * self.tab)
        self.output_str.append(line)
        self.output_str.append("\n")

    def visit_cwp(self, model: Cwp) -> None:
        self.cwp = model
        self.generate_all()

    def end_visit_cwp(self, model: Cwp) -> None:
        pass
