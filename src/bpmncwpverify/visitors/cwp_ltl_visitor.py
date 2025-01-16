from typing import List
from bpmncwpverify.core.state import State
import bpmncwpverify.visitors.cwpvisitor as cwpvisitor
import bpmncwpverify.core.cwp as cwp
from bpmncwpverify.core import typechecking


class CwpLtlVisitor(cwpvisitor.CwpVisitor):  # type: ignore
    def __init__(self, symbol_table: State, print_on: bool = False) -> None:
        self.state_info: List[str] = []
        self.symbol_table = symbol_table
        self.output_str: List[str] = []
        self.print_on: bool = print_on
        self.property_list: List[str] = []
        self.cwp: cwp.Cwp
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
        for const_decl in self.symbol_table._consts:
            self.write_line(f"#define {const_decl.id} {const_decl.init.value}")
            self.write_line("\n")
        self.write_line("\n")
        for enum_decl in self.symbol_table._enums:
            self.write_line(
                f"mytpe = {{{' '.join(sorted([value.value for value in enum_decl.values]))}}}"
            )
            self.write_line("\n")
        self.write_line("\n")
        for var_decl in self.symbol_table._vars:
            if var_decl.type_ == typechecking.ENUM:
                self.write_line(f"mytype {var_decl.id} = {var_decl.init.value}")
            else:
                self.write_line(
                    f"{var_decl.type_} {var_decl.id} = {var_decl.init.value}"
                )
            self.write_line("\n")

        self.write_line("\n")

    def write_variable_range_invariants(self) -> None:
        self.state_info.append(
            "\n\n//**********Variable Range Invariants************//"
        )
        for enum_decl in self.symbol_table._enums:
            # if enum.isConstant:
            #     continue
            # cwp = enum.cwp
            invariant = "("
            for value in enum_decl.values:
                invariant += "({enum_name} == {value}) || ".format(
                    enum_name=enum_decl.id, value=value.value
                )

            invariant = invariant[:-4]
            invariant += ")"
            self.write_line("#define {}Invariant {}".format(enum_decl.id, invariant))

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
        self.write_line("skip")
        self.tab -= 1
        self.write_line("}")
        self.tab -= 1
        self.write_line("}")

    def write_variable_range_assertions(self) -> None:
        for var_name in self.symbol_table._vars:
            self.write_line("assert({}Invariant)".format(var_name.id))

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

    def write_state_properties(self, state: "cwp.CwpState") -> None:
        self.write_line(
            "//**********{} STATE PROPERTIES************//".format(state.name)
        )
        self.write_exists_property(state)
        self.write_mutex_property(state)
        self.write_edges_property(state)
        self.write_line("")
        self.write_line("")

    def write_exists_property(self, state: "cwp.CwpState") -> None:
        self.property_list.append("{}Exists".format(state.name))
        self.write_line(
            "ltl {name}Exists {{(fair implies (always (! {name})))}}".format(
                name=state.name
            )
        )

    def write_mutex_property(self, state: "cwp.CwpState") -> None:
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
        for var in self.symbol_table._vars:
            self.write_log_var(var.id)
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

    def write_log_state(self, state: "cwp.CwpState") -> None:
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

    def write_log_edge(self, edge: "cwp.CwpEdge") -> None:
        if self.print_on:
            self.write_line(
                'printf("**EDGE {id}({parent_id}) = %d\\n", {name})'.format(
                    id=edge.id, parent_id=edge.parent_id, name=edge.name
                )
            )
        else:
            self.write_line("skip")

    def write_edges_property(self, state: "cwp.CwpState") -> None:
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

    def visit_cwp(self, model: "cwp.Cwp") -> bool:
        self.cwp = model
        self.generate_all()
        return True
