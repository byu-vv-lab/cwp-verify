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
    Activity,
    Bpmn,
    BpmnElement,
    Node
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

    def get_location(self, element: BpmnElement) -> str:
        if isinstance(element, Activity):
            return element.name + "_END"  # type: ignore
        else:
            return element.name  # type: ignore

    def genActivationOption(self, element: Node, start_guard: str = "", option_type: str = "") -> None:
        guard = "("
        consume_locations = []
        put_locations = []
        behavior_inline = "skip"
        put_conditions: list[str] = []
        put_flow_ids = []
        element_id = element.id
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
            guard += "\t({}_hasOption)".format(element.label)
        guard += ")"
        if option_type != "Task-END":
            behavior_inline = "{x}_BehaviorModel()".format(x=element.label)
        if option_type == "Task":
            put_flow_ids.append(element_id)
            put_locations.append(self.get_location(element))
            for msg in element.out_msgs:
                put_flow_ids.append(msg.id)
                put_locations.append(self.get_location(msg.to_node, msg))
        else:
            for flow in element.out_flows:
                put_flow_ids.append(flow.id)
                put_locations.append(self.get_location(flow.to_node, flow))
                if option_type == "XOR":
                    put_conditions.append(flow.label)
            if option_type != "Task-END":
                for msg in element.out_msgs:
                    put_flow_ids.append(msg.id)
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
                option_type,
            )
        )

    ####################
    # Visitor Methods
    ####################
    def visit_start_event(self, event: StartEvent) -> bool:
        return True

    def end_visit_start_event(self, event: StartEvent) -> None:
        pass

    def visit_end_event(self, event: EndEvent) -> bool:
        return True

    def end_visit_end_event(self, event: EndEvent) -> None:
        self.gen_places(event)
        self.gen_activation_option(event)

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        return True

    def end_visit_intermediate_event(self, event: IntermediateEvent) -> None:
        pass

    def visit_task(self, task: Task) -> bool:
        return True

    def end_visit_task(self, task: Task) -> None:
        pass

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        return True

    def end_visit_sub_process(self, subprocess: SubProcess) -> None:
        pass

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def end_visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def visit_process(self, process: Process) -> None:
        # TODO: maybe give process a name instead of using id here
        self.write_workflow_lines("proctype {x}() {{".format(x=process.id))
        self.workflow_indent += 1
        self.write_workflow_lines("pid me = _pid")
        # TODO: handle start states with in_msgs here
        for start_node in process.get_start_states():
            self.write_workflow_lines("putToken({x})".format(x=start_node.label))
        self.write_workflow_lines("do")

    def end_visit_process(self, process: Process) -> None:
        self.write_workflow_lines("od")
        self.workflow_indent -= 1
        self.write_workflow_lines("}")

    def visit_bpmn(self, bpmn: Bpmn) -> Bpmn:
        init_lines = "init {\n"
        init_lines += "\tatomic{\n"
        init_lines += "\t\tupdateState()\n"
        for process in bpmn.processes:
            init_lines += "\t\trun {}()\n".format(process.name)
        init_lines += "\t}\n"
        init_lines += "}\n\n"
        self.write_init_lines(init_lines)

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        for place in self.flow_places:
            self.write_places_lines("bit {x} = 0".format(x=str(place)))
