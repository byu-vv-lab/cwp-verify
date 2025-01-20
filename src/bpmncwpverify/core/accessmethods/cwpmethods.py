from typing import List
from xml.etree.ElementTree import Element
from bpmncwpverify.core.expr import ExpressionListener
from bpmncwpverify.core.state import State
from returns.result import Result, Failure
from bpmncwpverify.core.error import (
    CwpEdgeNoParentExprError,
    CwpEdgeNoStateError,
    CwpFileStructureError,
    Error,
)
from bpmncwpverify.core.cwp import Cwp, CwpState, CwpEdge
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.visitors.cwp_graph_visitor import CwpGraphVizVisitor
from bpmncwpverify.visitors.cwp_ltl_visitor import CwpLtlVisitor


def from_xml(root: Element, symbol_table: State) -> Result["Cwp", Error]:
    builder = CwpBuilder()

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


def generate_graph_viz(cwp: Cwp) -> None:
    graph_viz_visitor = CwpGraphVizVisitor()

    cwp.accept(graph_viz_visitor)

    graph_viz_visitor.dot.render("graphs/cwp_graph.gv", format="png")  # type: ignore[unused-ignore]


def generate_ltl(cwp: Cwp, symbol_table: State) -> str:
    ltl_visitor = CwpLtlVisitor(symbol_table)

    cwp.accept(ltl_visitor)

    output_str = ltl_visitor.output_str

    return "".join(output_str)
