import graphviz
from bpmncwpverify.core.cwp import CwpVisitor, CwpState, CwpEdge


class CwpGraphVizVisitor(CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.dot = graphviz.Digraph(comment="cwp graph")

    def visit_state(self, state: CwpState) -> bool:
        self.dot.node(state.name, state.name)
        return True

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> bool:
        if edge.source:
            self.dot.edge(edge.source.name, edge.dest.name, label=edge.expression)
        else:
            self.dot.edge("start", edge.dest.name, label=edge.expression)
        return True
