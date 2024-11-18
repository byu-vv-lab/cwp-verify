from typing import Set
from bpmncwpverify.core.cwp import CwpState, CwpVisitor, CwpEdge


class CwpConnectivityVisitor(CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.visited: Set[CwpState] = set()

    def visit_state(self, state: CwpState) -> None:
        if state not in self.visited:
            self.visited.add(state)

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> None:
        if edge.dest in self.visited:
            edge.is_leaf = True

    def end_visit_edge(self, edge: CwpEdge) -> None:
        pass
