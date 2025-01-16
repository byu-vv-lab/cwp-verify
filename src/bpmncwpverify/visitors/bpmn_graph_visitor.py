import graphviz
import bpmncwpverify.core.bpmn as bpmn
import bpmncwpverify.visitors.bpmnvisitor as bpmnvisitor


def dot_node(graph: graphviz.Digraph, id: str, name: str) -> None:
    graph.node(id, name)  # type: ignore[unused-ignore]


def dot_edge(graph: graphviz.Digraph, src: str, dst: str, label: str) -> None:
    graph.edge(src, dst, label=label)  # type: ignore[unused-ignore]


class GraphVizVisitor(bpmnvisitor.BpmnVisitor):  # type: ignore[misc]
    def __init__(self, process_number: int) -> None:
        self.dot = graphviz.Digraph(comment="Process graph {}".format(process_number))

    def visit_start_event(self, event: "bpmn.StartEvent") -> bool:
        dot_node(self.dot, event.id, event.name)
        return True

    def visit_end_event(self, event: "bpmn.EndEvent") -> bool:
        dot_node(self.dot, event.id, event.name)
        return True

    def visit_intermediate_event(self, event: "bpmn.IntermediateEvent") -> bool:
        dot_node(self.dot, event.id, event.name)
        return True

    def visit_task(self, task: "bpmn.Task") -> bool:
        dot_node(self.dot, task.id, task.name)
        return True

    def visit_exclusive_gateway(self, gateway: "bpmn.ExclusiveGatewayNode") -> bool:
        dot_node(self.dot, gateway.id, gateway.name)
        return True

    def visit_parallel_gateway(self, gateway: "bpmn.ParallelGatewayNode") -> bool:
        dot_node(self.dot, gateway.id, gateway.name)
        return True

    def end_visit_sequence_flow(self, flow: "bpmn.SequenceFlow") -> None:
        dot_edge(self.dot, flow.source_node.id, flow.target_node.id, flow.name)

    def end_visit_message_flow(self, flow: "bpmn.MessageFlow") -> None:
        dot_edge(self.dot, flow.source_node.id, flow.target_node.id, flow.name)

    def end_visit_bpmn(self, bpmn: "bpmn.Bpmn") -> None:
        for _msg_id, msg_flow in bpmn.inter_process_msgs.items():
            self.dot.edge(  # type: ignore[unused-ignore]
                msg_flow.source_node.id, msg_flow.target_node.id, label="message_flow"
            )
