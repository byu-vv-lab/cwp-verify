from typing import List
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import State
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor
from returns.result import Result, Success, Failure
from bpmncwpverify.core.error import (
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
    def __init__(self, symbol_table: State) -> None:
        self.edges: List[Element] = []
        self.all_items: List[Element] = []
        self.states: List[Element] = []
        self._cur_edge_letter = "A"
        self._cwp = Cwp()
        self.symbol_table = symbol_table

    def gen_edge_name(self) -> str:
        ret = "Edge" + self._cur_edge_letter
        self._cur_edge_letter = chr(ord(self._cur_edge_letter) + 1)
        return ret

    def build(self) -> Result[Cwp, Error]:
        pass

    def with_edge(self, edge: CwpEdge) -> None:
        pass

    def with_init_state(self, state: CwpState) -> None:
        pass

    def with_final_state(self, state: CwpState) -> None:
        pass

    def with_state(self, state: CwpState) -> None:
        pass
