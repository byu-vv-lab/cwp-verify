from typing import List
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import SymbolTable
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor
from returns.result import Result, Success, Failure
from bpmncwpverify.error import (
    CwpEdgeNoParentExprError,
    CwpEdgeNoStateError,
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
    def __init__(self, symbol_table: SymbolTable) -> None:
        self.edges: List[Element] = []
        self.all_items: List[Element] = []
        self.states: List[Element] = []
        self._cur_edge_letter = "A"
        self._cwp = Cwp()
        self.symbol_table = symbol_table

    def _gen_edge_name(self) -> str:
        ret = "Edge" + self._cur_edge_letter
        self._cur_edge_letter = chr(ord(self._cur_edge_letter) + 1)
        return ret

    def _parse_states(self, mx_states: List[Element]) -> None:
        for mx_cell in mx_states:
            style = mx_cell.get("style")
            if style and "edgeLabel" not in style:
                state = CwpState(mx_cell)
                self._cwp.states[state.id] = state

    def _parse_edges(self, mx_edges: List[Element]) -> None:
        for mx_cell in mx_edges:
            sourceRef = mx_cell.get("source")
            targetRef = mx_cell.get("target")
            if not targetRef or not sourceRef:
                raise Exception(CwpEdgeNoStateError(mx_cell))
            edge = CwpEdge(mx_cell, self._gen_edge_name())
            source = self._cwp.states[sourceRef]
            source.out_edges.append(edge)
            edge.set_source(source)

            dest = self._cwp.states[targetRef]
            dest.in_edges.append(edge)
            edge.set_dest(dest)
            self._cwp.edges[edge.id] = edge

    def _add_and_check_expressions(
        self, all_items: List[Element], expr_checker: ExpressionListener
    ) -> None:
        for mx_cell in all_items:
            style = mx_cell.get("style")
            if style and "edgeLabel" in style:
                parent = mx_cell.get("parent")
                expression = mx_cell.get("value")
                if not (parent and expression):
                    raise Exception(CwpEdgeNoParentExprError(mx_cell))

                edge = self._cwp.edges.get(parent)
                if not edge or not (parent_id_ref := mx_cell.get("id")):
                    raise Exception(CwpNoParentEdgeError(mx_cell))

                edge.expression = CwpEdge.cleanup_expression(expression)
                result = expr_checker.type_check(edge.expression, self.symbol_table)
                if not_(is_successful)(result):
                    raise Exception(result.failure())

                edge.parent_id = parent_id_ref

    def build(self) -> Result[Cwp, Error]:
        try:
            expression_checker = ExpressionListener(self.symbol_table)
            self._parse_states(self.states)
            self._parse_edges(self.edges)

            # This step assigns expressions to each edge and checks to make sure expression is valid
            self._add_and_check_expressions(self.all_items, expression_checker)

            # end state must have no out edges and at least one in edge
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

    def with_edge(self, element: Element) -> None:
        self.edges.append(element)
        self.all_items.append(element)

    def with_state(self, element: Element) -> None:
        self.states.append(element)
        self.all_items.append(element)
