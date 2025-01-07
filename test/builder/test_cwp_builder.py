# type: ignore
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.error import (
    CwpEdgeNoParentExprError,
    CwpEdgeNoStateError,
    CwpNoParentEdgeError,
)
from returns.result import Success
import pytest

from xml.etree.ElementTree import Element, SubElement


@pytest.fixture
def builder():
    return CwpBuilder()


def create_mock_state(mocker, state_id, out_edges=None, in_edges=None):
    state = mocker.MagicMock()
    state.id = state_id
    state.out_edges = out_edges or []
    state.in_edges = in_edges or []
    return state


def create_mock_edge(mocker, name, dest=None):
    edge = mocker.MagicMock()
    edge.name = name
    edge.dest = dest
    edge.is_leaf = False
    return edge


def test_gen_edge_name(builder):
    assert builder.gen_edge_name() == "EdgeA"
    assert builder.gen_edge_name() == "EdgeB"
    assert builder.gen_edge_name() == "EdgeC"


def test_from_xml_success(mocker):
    mock_builder = mocker.patch("bpmncwpverify.builder.cwp_builder.CwpBuilder")
    mocker.patch("bpmncwpverify.core.cwp.CwpState")
    mocker.patch("bpmncwpverify.core.cwp.CwpEdge")
    mocker.patch("bpmncwpverify.core.expr.ExpressionListener")
    mock_result = mocker.Mock(spec=Success)

    mock_builder.return_value.build.return_value = mock_result

    root = Element("root")
    diagram = SubElement(root, "diagram")
    mx_graph_model = SubElement(diagram, "mxGraphModel")
    mx_root = SubElement(mx_graph_model, "root")

    state = SubElement(mx_root, "mxCell", vertex="1", style="stateStyle")
    state.set("id", "state1")

    edge = SubElement(mx_root, "mxCell", edge="1", source="state1", target="state2")
    edge.set("id", "edge1")

    SubElement(mx_root, "mxCell", style="edgeLabel", value="x > 0", parent="state1")

    result = Cwp.from_xml(root, mocker.Mock())

    assert isinstance(result, Success)
    mock_builder.return_value.with_state.assert_called()
    mock_builder.return_value.with_edge.assert_called()
    mock_builder.return_value.check_expression.assert_called()
    mock_builder.return_value.build.assert_called_once()


def test_from_xml_edge_missing_source_target(mocker):
    root = Element("root")
    diagram = SubElement(root, "diagram")
    mx_graph_model = SubElement(diagram, "mxGraphModel")
    mx_root = SubElement(mx_graph_model, "root")

    SubElement(mx_root, "mxCell", edge="1")
    symbol_table = mocker.MagicMock()

    with pytest.raises(Exception) as exc_info:
        Cwp.from_xml(root, symbol_table)

    assert isinstance(exc_info.value.args[0], CwpEdgeNoStateError)


def test_from_xml_missing_parent_or_expression(mocker):
    root = Element("root")
    diagram = SubElement(root, "diagram")
    mx_graph_model = SubElement(diagram, "mxGraphModel")
    mx_root = SubElement(mx_graph_model, "root")

    SubElement(mx_root, "mxCell", style="edgeLabel")
    symbol_table = mocker.MagicMock()

    with pytest.raises(Exception) as exc_info:
        Cwp.from_xml(root, symbol_table)

    assert isinstance(exc_info.value.args[0], CwpEdgeNoParentExprError)


def test_check_expression(mocker):
    mock_expr_checker = mocker.MagicMock()
    mock_expr_checker.type_check.return_value = Success(None)

    symbol_table = mocker.MagicMock()

    builder = CwpBuilder()
    builder._cwp = Cwp()
    builder._cwp.edges = {"edge": mocker.MagicMock(), "parent": mocker.MagicMock()}

    expression = "expression"

    builder.check_expression(mock_expr_checker, expression, "parent", symbol_table)


def test_check_expression_no_parent(mocker):
    builder = CwpBuilder()
    builder._cwp = Cwp()
    builder._cwp.edges = {"edge": mocker.MagicMock()}

    with pytest.raises(Exception) as exc_info:
        builder.check_expression(
            mocker.Mock(), mocker.Mock(), mocker.Mock(), mocker.Mock()
        )

    assert isinstance(exc_info.value.args[0], CwpNoParentEdgeError)


def test_with_edge(mocker):
    builder = CwpBuilder()
    builder._cwp = Cwp()
    source = mocker.MagicMock()
    source.out_edges = []
    dest = mocker.MagicMock()
    dest.in_edges = []
    builder._cwp.states = {"node1": source, "node2": dest}

    mock_edge = mocker.MagicMock()
    mock_edge.id = "edge1"

    builder.with_edge(mock_edge, "node1", "node2")

    mock_edge.set_source.assert_called_once_with(source)
    mock_edge.set_dest.assert_called_once_with(dest)

    assert builder._cwp.edges[mock_edge.id] == mock_edge
    assert len(dest.in_edges) == 1
    assert len(source.out_edges) == 1
