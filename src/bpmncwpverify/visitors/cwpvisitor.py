import bpmncwpverify.core.cwp as cwp


class CwpVisitor:
    def visit_state(self, state: "cwp.CwpState") -> bool:
        return True

    def end_visit_state(self, state: "cwp.CwpState") -> None:
        pass

    def visit_edge(self, edge: "cwp.CwpEdge") -> bool:
        return True

    def end_visit_edge(self, edge: "cwp.CwpEdge") -> None:
        pass

    def visit_cwp(self, model: "cwp.Cwp") -> bool:
        return True

    def end_visit_cwp(self, model: "cwp.Cwp") -> None:
        pass
