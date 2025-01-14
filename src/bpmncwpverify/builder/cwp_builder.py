from bpmncwpverify.core.state import State
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor
from returns.result import Result, Success, Failure
from bpmncwpverify.core.error import (
    CwpMultStartStateError,
    CwpNoEndStatesError,
    CwpNoParentEdgeError,
    CwpNoStartStateError,
    Error,
)
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.expr import ExpressionListener
from returns.pipeline import is_successful
from returns.functions import not_


class CwpBuilder:
    def __init__(self) -> None:
        self._cur_edge_letter = "A"
        self._cwp = Cwp()

    def gen_edge_name(self) -> str:
        ret = "Edge" + self._cur_edge_letter
        self._cur_edge_letter = chr(ord(self._cur_edge_letter) + 1)
        return ret

    def build(self) -> Result[Cwp, Error]:
        try:
            end_states = [
                state
                for state in self._cwp.states.values()
                if not state.out_edges and state.in_edges
            ]

            start_states = [
                state
                for state in self._cwp.states.values()
                if not state.in_edges and state.out_edges
            ]

            if len(start_states) > 1:
                raise Exception(
                    CwpMultStartStateError([state.id for state in start_states])
                )
            elif not start_states:
                raise Exception(CwpNoStartStateError())

            self._cwp.start_state = start_states[0]

            if not end_states:
                raise Exception(CwpNoEndStatesError())

            self._cwp.states = {
                id: state
                for id, state in self._cwp.states.items()
                if state != self._cwp.start_state
            }

            # This step ensures connectivity of the graph and sets leaf edges
            visitor = CwpConnectivityVisitor()
            self._cwp.accept(visitor)

            return Success(self._cwp)
        except Exception as e:
            return Failure(e.args[0])

    def with_edge(
        self, edge: CwpEdge, source_ref: str, target_ref: str
    ) -> "CwpBuilder":
        source = self._cwp.states[source_ref]
        source.out_edges.append(edge)
        edge.set_source(source)

        dest = self._cwp.states[target_ref]
        dest.in_edges.append(edge)
        edge.set_dest(dest)
        self._cwp.edges[edge.id] = edge
        return self

    def check_expression(
        self,
        expr_checker: ExpressionListener,
        expression: str,
        parent: str,
        symbol_table: State,
    ) -> None:
        edge = self._cwp.edges.get(parent)
        if not edge:
            raise Exception(CwpNoParentEdgeError(parent))
        edge.expression = CwpEdge.cleanup_expression(expression)
        result = expr_checker.type_check(edge.expression, symbol_table)
        if not_(is_successful)(result):
            raise Exception(result.failure())

    def with_state(self, state: CwpState) -> "CwpBuilder":
        self._cwp.states[state.id] = state
        return self
