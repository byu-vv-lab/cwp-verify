from bpmncwpverify.builder.cwp_builder import ConcreteCwpBuilder
import pytest


@pytest.fixture
def builder(mocker):
    symbol_table = mocker.MagicMock()
    return ConcreteCwpBuilder(symbol_table)


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


def test_calc_end_states(mocker, builder):
    state1 = create_mock_state(mocker, "state1", out_edges=[])
    state2 = create_mock_state(mocker, "state2", out_edges=["edge"])
    state3 = create_mock_state(mocker, "state3", out_edges=[])
    builder._cwp.states = {"state1": state1, "state2": state2, "state3": state3}

    builder._calc_end_states()
    assert builder._cwp.end_states == [state1, state3]
