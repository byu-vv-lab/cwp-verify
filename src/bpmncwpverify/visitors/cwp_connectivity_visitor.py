from typing import Set
import bpmncwpverify.core.cwp as cwp
import bpmncwpverify.visitors.cwpvisitor as cwpvisitor
from bpmncwpverify.core.error import CwpGraphConnError


class CwpConnectivityVisitor(cwpvisitor.CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[cwp.CwpState] = set()

    def visit_state(self, state: "cwp.CwpState") -> bool:
        self.visited.add(state)
        return True

    def visit_edge(self, edge: "cwp.CwpEdge") -> bool:
        # This determines if an edge is a leaf node
        if edge.dest in self.visited:
            edge.is_leaf = True
            return False
        return True

    def end_visit_cwp(self, model: "cwp.Cwp") -> None:
        # This checks to see if any part of the graph is not connected
        if self.visited != set(model.states.values()) | {model.start_state}:
            raise Exception(CwpGraphConnError())
