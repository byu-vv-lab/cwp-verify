from typing import Dict, List, Optional
from xml.etree.ElementTree import Element
import re
from bpmncwpverify.core.expr import ExpressionListener
from bpmncwpverify.core.state import State
from returns.result import Result, Failure
from bpmncwpverify.core.error import (
    CwpEdgeNoParentExprError,
    CwpEdgeNoStateError,
    CwpFileStructureError,
    Error,
)
import bpmncwpverify.builder.cwp_builder as cwp_builder
import bpmncwpverify.visitors.cwp_graph_visitor as cwp_graph_visitor
import bpmncwpverify.visitors.cwpvisitor as cwpvisitor
import bpmncwpverify.visitors.cwp_ltl_visitor as clv


class Cwp:
    def __init__(self) -> None:
        self.states: Dict[str, CwpState] = {}
        self.edges: Dict[str, CwpEdge] = {}
        self.start_state: CwpState
        self.end_states: List[CwpState] = []

    @staticmethod
    def from_xml(root: Element, symbol_table: State) -> Result["Cwp", Error]:
        builder = cwp_builder.CwpBuilder()

        if (diagram := root.find("diagram")) is None:
            return Failure(CwpFileStructureError("diagram"))
        if (mx_graph_model := diagram.find("mxGraphModel")) is None:
            return Failure(CwpFileStructureError("mxGraphModel"))
        if (mx_root := mx_graph_model.find("root")) is None:
            return Failure(CwpFileStructureError("root"))
        if not (mx_cells := mx_root.findall("mxCell")):
            return Failure(CwpFileStructureError("mxCell"))

        all_items: List[Element] = [itm for itm in mx_cells]
        edges: List[Element] = [itm for itm in mx_cells if itm.get("edge")]
        states: List[Element] = [itm for itm in mx_cells if itm.get("vertex")]
        expression_checker = ExpressionListener(symbol_table)

        for element in states:
            style = element.get("style")
            if style and "edgeLabel" not in style:
                state = CwpState.from_xml(element)
                builder = builder.with_state(state)

        for element in edges:
            source_ref = element.get("source")
            target_ref = element.get("target")
            if not target_ref or not source_ref:
                raise Exception(CwpEdgeNoStateError(element))
            edge = CwpEdge.from_xml(element, builder.gen_edge_name())

            builder = builder.with_edge(edge, source_ref, target_ref)

        for itm in all_items:
            style = itm.get("style")
            if style and "edgeLabel" in style:
                parent = itm.get("parent")
                expression = itm.get("value")
                if not (parent and expression):
                    raise Exception(CwpEdgeNoParentExprError(itm))
                builder.check_expression(
                    expression_checker, expression, parent, symbol_table
                )

        result: Result["Cwp", Error] = builder.build()
        return result

    def accept(self, visitor: "cwpvisitor.CwpVisitor") -> None:
        result = visitor.visit_cwp(self)
        if result:
            self.start_state.accept(visitor)
        visitor.end_visit_cwp(self)

    def generate_graph_viz(self) -> None:
        graph_viz_visitor = cwp_graph_visitor.CwpGraphVizVisitor()

        self.accept(graph_viz_visitor)

        graph_viz_visitor.dot.render("graphs/cwp_graph.gv", format="png")  # type: ignore[unused-ignore]

    def generate_ltl(self, symbol_table: State) -> str:
        ltl_visitor = clv.CwpLtlVisitor(symbol_table)

        self.accept(ltl_visitor)

        output_str = ltl_visitor.output_str

        return "".join(output_str)


class CwpState:
    def __init__(self, state: Element) -> None:
        id = state.get("id")
        name = state.get("value")
        if id is None:
            raise Exception("id not in cwp state")
        if name is None:
            name = id
        self.name: str
        self.id = id
        self.out_edges: List[CwpEdge] = []
        self.in_edges: List[CwpEdge] = []
        self.cleanup_name(name)

    def accept(self, visitor: "cwpvisitor.CwpVisitor") -> None:
        result = visitor.visit_state(self)
        if result:
            for edge in self.out_edges:
                edge.accept(visitor)
        visitor.end_visit_state(self)

    def cleanup_name(self, name: str) -> None:
        name = re.sub("[?,+=/]", "", name)
        name = re.sub("-", " ", name)
        name = re.sub(r"\s+", "_", name)

        name = re.sub("</?div>", "", name)

        self.name = name.strip()

    @staticmethod
    def from_xml(element: Element) -> "CwpState":
        return CwpState(element)


class CwpEdge:
    def __init__(self, edge: Element, name: str) -> None:
        id = edge.get("id")
        if id is None:
            raise Exception("No ID for edge or no targetRef")
        self.id = id
        self.name = name
        self.expression: str
        self.parent_id: str

        self.source: Optional[CwpState] = None
        self.dest: CwpState
        self.is_leaf = False

    def set_source(self, state: CwpState) -> None:
        self.source = state

    def set_dest(self, state: CwpState) -> None:
        self.dest = state

    def accept(self, visitor: "cwpvisitor.CwpVisitor") -> None:
        if visitor.visit_edge(self) and not self.is_leaf:
            self.dest.accept(visitor)
        visitor.end_visit_edge(self)

    @staticmethod
    def cleanup_expression(expression: str) -> str:
        expression = re.sub(r"&amp;", "&", expression)
        expression = re.sub(r"&lt;", "<", expression)
        expression = re.sub(r"&gt;", ">", expression)

        expression = re.sub(r"</?div>", "", expression)
        expression = re.sub(r"<br>", " ", expression)

        expression = re.sub(r"\s*(==|!=|&&|\|\|)\s*", r" \1 ", expression)

        expression = re.sub(r"\s+", " ", expression)

        return expression.strip()

    @staticmethod
    def from_xml(element: Element, name: str) -> "CwpEdge":
        return CwpEdge(element, name)
