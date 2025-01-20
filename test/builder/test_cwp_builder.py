# type: ignore
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.error import (
    CwpEdgeNoParentExprError,
    CwpEdgeNoStateError,
    CwpNoParentEdgeError,
    CwpNoStartStateError,
)
from returns.result import Success
import pytest

from xml.etree.ElementTree import Element, SubElement
from returns.pipeline import is_successful
from returns.functions import not_
from bpmncwpverify.core.accessmethods.cwpmethods import from_xml


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
    mock_builder = mocker.patch(
        "bpmncwpverify.core.accessmethods.cwpmethods.CwpBuilder"
    )
    mock_result = mocker.Mock(spec=Success)
    mock_builder.return_value.with_state.return_value = mock_builder.return_value
    mock_builder.return_value.with_edge.return_value = mock_builder.return_value
    mock_builder.return_value.build.return_value = mock_result

    root = Element("root")
    diagram = SubElement(root, "diagram")
    mx_graph_model = SubElement(diagram, "mxGraphModel")
    mx_root = SubElement(mx_graph_model, "root")

    state1 = SubElement(mx_root, "mxCell", vertex="1", style="stateStyle")
    state1.set("id", "state1")

    state2 = SubElement(mx_root, "mxCell", vertex="1", style="stateStyle")
    state2.set("id", "state2")

    edge = SubElement(mx_root, "mxCell", edge="1", source="state1", target="state2")
    edge.set("id", "edge1")

    SubElement(
        mx_root, "mxCell", style="edgeLabel", vertex="1", value="x > 0", parent="edge1"
    )

    result = from_xml(root, mocker.Mock())

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
        from_xml(root, symbol_table)

    assert isinstance(exc_info.value.args[0], CwpEdgeNoStateError)


def test_from_xml_missing_parent_or_expression(mocker):
    root = Element("root")
    diagram = SubElement(root, "diagram")
    mx_graph_model = SubElement(diagram, "mxGraphModel")
    mx_root = SubElement(mx_graph_model, "root")

    SubElement(mx_root, "mxCell", style="edgeLabel")
    symbol_table = mocker.MagicMock()

    with pytest.raises(Exception) as exc_info:
        from_xml(root, symbol_table)

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


def test_build(mocker):
    states: dict[str, CwpState] = {
        "state1": mocker.MagicMock(spec=CwpState, in_edges=[], out_edges=["edge1"]),
        "state2": mocker.MagicMock(
            spec=CwpState, in_edges=["edge1"], out_edges=["edge2"]
        ),
        "state3": mocker.MagicMock(spec=CwpState, in_edges=["edge2"], out_edges=[]),
    }
    edges = {"edge1": mocker.MagicMock(), "edge2": mocker.MagicMock()}

    mock_cwp = mocker.MagicMock()
    mock_cwp.states = states

    obj = CwpBuilder()
    obj._cwp = mock_cwp
    obj._cwp.states = states
    obj._cwp.edges = edges
    mock_cwp.accept = mocker.MagicMock()

    result = obj.build()

    assert isinstance(result, Success)
    assert result.unwrap() == mock_cwp

    start_state = states["state1"]
    end_states = [states["state3"]]
    assert mock_cwp.start_state == start_state
    assert list(end_states) == [states["state3"]]

    mock_cwp.accept.assert_called_once()

    new_edge = CwpEdge(mocker.MagicMock(), mocker.MagicMock())
    states["state1"].in_edges = [new_edge]
    states["state3"].out_edges = [new_edge]

    result = obj.build()

    assert not_(is_successful)(result)
    assert isinstance(result.failure(), CwpNoStartStateError)
