from typing import List
from abc import ABC, abstractmethod
from xml.etree.ElementTree import Element
from returns.result import Result, Success
from bpmncwpverify.error import Error
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState


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
    def __init__(self) -> None:
        self.edges: List[Element] = []
        self.all_items: List[Element] = []
        self.states: List[Element] = []
        self._cwp
        self._cur_edge_letter = "A"

    def _gen_edge_name(self) -> str:
        ret = "Edge" + self._cur_edge_letter
        self._cur_edge_letter = chr(ord(self._cur_edge_letter) + 1)
        return ret

    def _calc_end_states(self) -> None:
        self.end_states = []
        for state in self._cwp.states.values():
            if not state.out_edges:
                self.end_states.append(state)

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
            if not targetRef:
                raise Exception("Edge does not have a target")
            edge = CwpEdge(mx_cell, self._gen_edge_name())
            if sourceRef:
                source = self._cwp.states[sourceRef]
                source.out_edges.append(edge)
                edge.set_source(source)
            else:
                self.start_edge = edge

            dest = self._cwp.states[targetRef]
            dest.in_edges.append(edge)
            edge.set_dest(dest)
            self._cwp.edges[edge.id] = edge

    def _add_expressions(self, all_items: List[Element]) -> None:
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

                edge.cleanup_expression(expression)
                edge.parent_id = parent_id_ref

    def build_cwp(self) -> None:
        self._cwp = Cwp()

    def build_edge(self, element: Element) -> None:
        self.edges.append(element)
        self.all_items.append(element)

    def build_state(self, element: Element) -> None:
        self.states.append(element)
        self.all_items.append(element)

    def get_cwp(self) -> Result[Cwp, Error]:
        self._parse_states(self.states)
        self._parse_edges(self.edges)
        self._add_expressions(self.all_items)
        self._set_leaf_edges()

        return Success(self._cwp)
