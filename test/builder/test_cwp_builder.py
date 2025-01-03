# type: ignore
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import CwpEdge, CwpState
from bpmncwpverify.core.error import CwpNoStartStateError
from returns.result import Success
import pytest
from returns.pipeline import is_successful
from returns.functions import not_

from xml.etree.ElementTree import Element


@pytest.fixture
def builder(mocker):
    symbol_table = mocker.MagicMock()
    return CwpBuilder(symbol_table)


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
    assert builder._gen_edge_name() == "EdgeA"
    assert builder._gen_edge_name() == "EdgeB"
    assert builder._gen_edge_name() == "EdgeC"


def test_parse_states(builder):
    mx_states = [
        Element("mxCell", attrib={"id": "state1", "style": "someStyle"}),
        Element("mxCell", attrib={"id": "state2", "style": "anotherStyle"}),
        Element("mxCell", attrib={"id": "edge1", "style": "edgeLabel"}),
    ]

    builder._parse_states(mx_states)
    assert "state1" in builder._cwp.states
    assert "state2" in builder._cwp.states
    assert "edge1" not in builder._cwp.states


def test_parse_edges(mocker, builder):
    mock_set_source = mocker.patch.object(CwpEdge, "set_source")
    mock_set_dest = mocker.patch.object(CwpEdge, "set_dest")

    source_state = mocker.MagicMock()
    dest_state = mocker.MagicMock()
    source_state.out_edges = []
    dest_state.in_edges = []
    builder._cwp.states = {
        "sourceState": source_state,
        "destState": dest_state,
    }

    mx_edge = mocker.MagicMock(spec=Element)
    mx_edge.get.side_effect = lambda x: {
        "source": "sourceState",
        "target": "destState",
        "id": "123",
    }.get(x)
    mx_edges = [mx_edge]

    builder._parse_edges(mx_edges)

    mock_set_source.assert_called_once_with(source_state)
    mock_set_dest.assert_called_once_with(dest_state)


def test_add_and_check_expressions(mocker, builder):
    mock_expr_checker = mocker.MagicMock()
    mock_expr_checker.build.return_value = Success("bool")
    edge = create_mock_edge(mocker, "edge1")
    builder._cwp.edges = {"edge1": edge}

    all_items = [
        Element(
            "mxCell",
            attrib={
                "id": "expr1",
                "parent": "edge1",
                "value": "someExpr",
                "style": "edgeLabel",
            },
        )
    ]

    builder._add_and_check_expressions(all_items, mock_expr_checker)
    mock_expr_checker.type_check.assert_called_once_with(
        "someExpr", builder.symbol_table
    )
    assert edge.parent_id == "expr1"


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
    mock_cwp.edges = edges

    obj = CwpBuilder()
    obj._cwp = mock_cwp
    obj.check_expressions = mocker.MagicMock()
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
