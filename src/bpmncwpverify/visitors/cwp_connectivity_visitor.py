from typing import Set
from bpmncwpverify.core.cwp import Cwp, CwpState, CwpVisitor, CwpEdge


class CwpConnectivityVisitor(CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[CwpState] = set()

    def visit_state(self, state: CwpState) -> None:
        if state not in self.visited:
            self.visited.add(state)

    def visit_edge(self, edge: CwpEdge) -> None:
        if edge.dest in self.visited:
            edge.is_leaf = True

    def end_visit_cwp(self, model: Cwp) -> None:
        if self.visited != set(model.states.values()) | set(
            model.start_states.values()
        ):
            raise Exception("Graph is not connected")
