from typing import List, Optional

from bpmncwpverify.core.bpmn import (
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
                    guard += " && ".join(
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
