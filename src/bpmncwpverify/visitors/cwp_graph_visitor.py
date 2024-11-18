import graphviz
from bpmncwpverify.core.cwp import CwpVisitor, CwpState, CwpEdge, Cwp


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
