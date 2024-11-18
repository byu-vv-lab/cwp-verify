from typing import List
from abc import ABC, abstractmethod
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import SymbolTable
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor
from returns.result import Result, Success
from bpmncwpverify.error import Error
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.expr import ExpressionListener
from returns.pipeline import is_successful
from returns.functions import not_


class CwpBuilder(ABC):
    @abstractmethod
    def build_state(self, element: Element) -> None:
        pass

    @abstractmethod
    def build_edge(self, element: Element) -> None:
        pass

    @abstractmethod
    def build_cwp(self) -> None:
        pass

    @abstractmethod
    def get_cwp(self) -> Result[Cwp, Error]:
        pass


class ConcreteCwpBuilder(CwpBuilder):
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

    def _calc_end_states(self) -> None:
        for state in self._cwp.states.values():
            if not state.out_edges:
                self._cwp.end_states.append(state)

    def _set_leaf_edges(self) -> None:
        visited = set()

        def dfs(state: CwpState) -> None:
            nonlocal visited

            visited.add(state)
            for edge in state.out_edges:
                if edge.dest in visited:
                    edge.is_leaf = True
                else:
                    dfs(edge.dest)

        for state in self._cwp.start_states.values():
            dfs(state)

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
                raise Exception("Edge does not have a source or a target")
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
                    raise Exception("Expression or parent node not in edge")

                edge = self._cwp.edges.get(parent)
                if not edge or not (parent_id_ref := mx_cell.get("id")):
                    raise Exception("Parent edge not found or no parent ID reference")

                edge.expression = edge.cleanup_expression(expression)
                result = expr_checker.build(edge.expression, self.symbol_table)
                if not_(is_successful)(result):
                    raise Exception(result)

                edge.parent_id = parent_id_ref

    def build_cwp(self) -> None:
        expression_checker = ExpressionListener(self.symbol_table)
        self._parse_states(self.states)
        self._parse_edges(self.edges)
        self._add_and_check_expressions(self.all_items, expression_checker)

        self._cwp.start_states = {
            id: state for id, state in self._cwp.states.items() if not state.in_edges
        }
        self._cwp.states = {
            id: state
            for id, state in self._cwp.states.items()
            if id not in self._cwp.start_states
        }

        visitor = CwpConnectivityVisitor()
        self._cwp.accept(visitor)

    def build_edge(self, element: Element) -> None:
        self.edges.append(element)
        self.all_items.append(element)

    def build_state(self, element: Element) -> None:
        self.states.append(element)
        self.all_items.append(element)

    def get_cwp(self) -> Result[Cwp, Error]:
        return Success(self._cwp)
