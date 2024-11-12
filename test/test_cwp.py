# type: ignore
from bpmncwpverify.visitors import CwpLtlVisitor
from bpmncwpverify.cwp import Cwp, CwpEdge
from xml.etree.ElementTree import Element
import pytest


def test_write_init_states(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")

    symbol_table = mocker.MagicMock()
    instance = CwpLtlVisitor(symbol_table)

    instance.cwp = Cwp()
    instance.cwp.states = {
        "state1": type("", (), {"name": "init_state1"}),
        "state2": type("", (), {"name": "normal_state2"}),
    }

    instance.write_init_states()

    expected_calls = [
        mocker.call("\n\n//**********STATE VARIABLE DECLARATION************//"),
        mocker.call("bit init_state1 = 1"),
        mocker.call("bit normal_state2 = 0"),
    ]

    mock_write.assert_has_calls(expected_calls)


def test_cwp_write_exists_properties(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")

    state = mocker.MagicMock()
    state.name = "TestState"

    symbol_table = mocker.MagicMock()
    visitor = CwpLtlVisitor(symbol_table)
    visitor.property_list = []

    visitor.write_exists_property(state)

    assert "{}Exists".format(state.name) in visitor.property_list

    expected_call = mocker.call(
        "ltl TestStateExists {(fair implies (always (! TestState)))}"
    )

    mock_write.assert_has_calls([expected_call])


def test_cwp_mutex_property(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    state = mocker.MagicMock()
    state.name = "TestState"

    dummy_cwp = type("DummyCwp", (), {})()
    dummy_cwp.states = {
        "TestState": state,
        "OtherState1": mocker.MagicMock(name="OtherState1"),
        "OtherState2": mocker.MagicMock(name="OtherState2"),
        "OtherState3": mocker.MagicMock(name="OtherState3"),
    }
    dummy_cwp.states["OtherState1"].name = "OtherState1"
    dummy_cwp.states["OtherState2"].name = "OtherState2"
    dummy_cwp.states["OtherState3"].name = "OtherState3"

    symbol_table = mocker.MagicMock()
    visitor = CwpLtlVisitor(symbol_table)
    visitor.property_list = []
    visitor.cwp = dummy_cwp
    visitor.tab = 0

    visitor.write_mutex_property(state)

    assert "{}Mutex".format(state.name) in visitor.property_list

    expected_calls = [
        mocker.call("ltl TestStateMutex {"),
        mocker.call("("),
        mocker.call("always ("),
        mocker.call("TestState implies ("),
        mocker.call("TestState"),
        mocker.call(
            "&& (! OtherState1)\n\t\t\t\t&& (! OtherState2)\n\t\t\t\t&& (! OtherState3)"
        ),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call("}"),
    ]
    mock_write.assert_has_calls(expected_calls)

    assert visitor.tab == 0


def test_cwp_write_edges_property(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")

    state = mocker.MagicMock()
    state.name = "TestState"

    dest_state1 = mocker.MagicMock()
    dest_state1.name = "DestState1"
    dest_state2 = mocker.MagicMock()
    dest_state2.name = "DestState2"
    dest_state3 = mocker.MagicMock()
    dest_state3.name = "DestState3"

    state.out_edges = [
        mocker.MagicMock(dest=dest_state1),
        mocker.MagicMock(dest=dest_state2),
        mocker.MagicMock(dest=dest_state3),
    ]

    symbol_table = mocker.MagicMock()
    visitor = CwpLtlVisitor(symbol_table)
    visitor.property_list = []
    visitor.tab = 0

    visitor.write_edges_property(state)

    assert "{}Edges".format(state.name) in visitor.property_list

    expected_calls = [
        mocker.call("ltl TestStateEdges {"),
        mocker.call("("),
        mocker.call("fair implies ("),
        mocker.call("always ("),
        mocker.call("TestState implies ("),
        mocker.call("TestState until ("),
        mocker.call("DestState1\n\t\t\t\t\t\t|| DestState2\n\t\t\t\t\t\t|| DestState3"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call("}"),
    ]

    mock_write.assert_has_calls(expected_calls)

    assert visitor.tab == 0


def test_cwp_write_state_variables(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    symbol_table = mocker.MagicMock()
    symbol_table._consts = {"CONST_A": ("CONST_A", 10), "CONST_B": ("CONST_B", 20)}
    symbol_table._enums = {"EnumType": {"Value1", "Value2", "Value3"}}
    symbol_table._vars = {
        "var1": ("int", "initial_value"),
        "var2": ("int", "initial_value", {"extra_value"}),
    }

    visitor = CwpLtlVisitor(symbol_table)

    visitor.write_state_variables()

    expected_calls = [
        mocker.call("\n\n//**********VARIABLE DECLARATION************//\n"),
        mocker.call("#define CONST_A 10"),
        mocker.call("\n"),
        mocker.call("#define CONST_B 20"),
        mocker.call("\n"),
        mocker.call("\n"),
        mocker.call("mytpe = {Value1 Value2 Value3}"),
        mocker.call("\n"),
        mocker.call("\n"),
        mocker.call("int var1 = initial_value"),
        mocker.call("\n"),
        mocker.call("mytype var2 = initial_value"),
        mocker.call("\n"),
        mocker.call("\n"),
    ]
    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_variable_range_invariants(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    symbol_table = mocker.MagicMock()
    symbol_table._enums = {
        "TestEnum1": ("Value1", "Value2", "Value3"),
        "TestEnum2": ("Value1", "Value2", "Value3"),
    }

    visitor = CwpLtlVisitor(symbol_table)
    visitor.state_info = []

    visitor.write_variable_range_invariants()

    assert visitor.state_info == [
        "\n\n//**********Variable Range Invariants************//"
    ]

    expected_calls = [
        mocker.call(
            "#define TestEnum1Invariant ((TestEnum1 == Value1) || (TestEnum1 == Value2) || (TestEnum1 == Value3))"
        ),
        mocker.call(
            "#define TestEnum2Invariant ((TestEnum2 == Value1) || (TestEnum2 == Value2) || (TestEnum2 == Value3))"
        ),
    ]

    mock_write.assert_has_calls(expected_calls)


def test_cwp_write_edge_definitions(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    mock_cwp = mocker.MagicMock()
    mock_cwp.edges = {
        "edge1": mocker.MagicMock(),
        "edge2": mocker.MagicMock(),
        "edge3": mocker.MagicMock(),
    }

    mock_cwp.edges["edge1"].name = "edge1"
    mock_cwp.edges["edge2"].name = "edge2"
    mock_cwp.edges["edge3"].name = "edge3"

    instance = CwpLtlVisitor(mocker.MagicMock())
    instance.cwp = mock_cwp

    instance.write_edge_definitions()

    expected_calls = [
        mocker.call("\n\n//**********EDGE DECLARATION************//"),
        mocker.call("bit edge1 = 0"),
        mocker.call("bit edge2 = 0"),
        mocker.call("bit edge3 = 0"),
    ]

    mock_write.assert_has_calls(expected_calls)


def test_cwp_write_variable_range_assertions(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    symbol_table = mocker.MagicMock()
    symbol_table._vars = {
        "var1": mocker.MagicMock(),
        "var2": mocker.MagicMock(),
        "var3": mocker.MagicMock(),
    }

    visitor = CwpLtlVisitor(symbol_table)

    visitor.write_variable_range_assertions()

    expected_calls = [
        mocker.call("assert(var1Invariant)"),
        mocker.call("assert(var2Invariant)"),
        mocker.call("assert(var3Invariant)"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_refresh_edges(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.edges = {"edge1": mocker.MagicMock(), "edge2": mocker.MagicMock()}
    cwp.edges["edge1"].name = "Edge1"
    cwp.edges["edge1"].expression = "expression1"
    cwp.edges["edge2"].name = "Edge2"
    cwp.edges["edge2"].expression = "expression2"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.tab = 0

    visitor.write_refresh_edges()

    expected_calls = [
        mocker.call("if"),
        mocker.call(":: (expression1) -> "),
        mocker.call("Edge1 = 1"),
        mocker.call(":: else -> "),
        mocker.call("Edge1 = 0"),
        mocker.call("fi"),
        mocker.call("if"),
        mocker.call(":: (expression2) -> "),
        mocker.call("Edge2 = 1"),
        mocker.call(":: else -> "),
        mocker.call("Edge2 = 0"),
        mocker.call("fi"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)

    assert visitor.tab == 0


def test_cwp_write_refresh_states(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    in_edge1 = mocker.MagicMock()
    in_edge1.name = "InEdge1"
    in_edge2 = mocker.MagicMock()
    in_edge2.name = "InEdge2"
    out_edge1 = mocker.MagicMock()
    out_edge1.name = "OutEdge1"
    out_edge2 = mocker.MagicMock()
    out_edge2.name = "OutEdge2"

    cwp = mocker.MagicMock
    cwp.states = {"state1": mocker.MagicMock(), "state2": mocker.MagicMock()}
    cwp.states["state1"].name = "State1"
    cwp.states["state1"].in_edges = [in_edge1, in_edge2]
    cwp.states["state1"].out_edges = [out_edge1, out_edge2]

    cwp.states["state2"].name = "State2"
    cwp.states["state2"].in_edges = []
    cwp.states["state2"].out_edges = [out_edge1]

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.tab = 0

    visitor.write_refresh_states()

    expected_calls = [
        mocker.call("State1 = "),
        mocker.call("("),
        mocker.call("(InEdge1 && InEdge2)"),
        mocker.call("&&"),
        mocker.call("(! (OutEdge1 || OutEdge2))"),
        mocker.call(")"),
        mocker.call("State2 = "),
        mocker.call("("),
        mocker.call("(! (OutEdge1))"),
        mocker.call(")"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)

    assert visitor.tab == 0


def test_cwp_write_ina_state_property(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.states = {
        "state1": mocker.MagicMock(),
        "state2": mocker.MagicMock(),
        "state3": mocker.MagicMock(),
    }
    cwp.states["state1"].name = "State1"
    cwp.states["state2"].name = "State2"
    cwp.states["state3"].name = "State3"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.property_list = []

    visitor.write_ina_state_property()

    assert "alwaysInAState" in visitor.property_list

    expected_calls = [
        mocker.call("#define inAState State1 \\\n || State2 \\\n || State3"),
        mocker.call("ltl alwaysInAState {(always (inAState))}"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_fair_property_debug_true(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.end_states = [mocker.MagicMock(), mocker.MagicMock()]
    cwp.end_states[0].name = "EndState1"
    cwp.end_states[1].name = "EndState2"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.property_list = []
    visitor.debug = True

    visitor.write_fair_property()

    assert "fairPathExists" in visitor.property_list

    expected_calls = [
        mocker.call("#define fair (true)"),
        mocker.call("ltl fairPathExists {(always (! fair))}"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_fair_property_debug_false(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.end_states = [mocker.MagicMock(), mocker.MagicMock()]
    cwp.end_states[0].name = "EndState1"
    cwp.end_states[1].name = "EndState2"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.property_list = []
    visitor.debug = False

    visitor.write_fair_property()

    assert "fairPathExists" in visitor.property_list

    expected_calls = [
        mocker.call("#define fair (eventually (EndState1 || EndState2))"),
        mocker.call("ltl fairPathExists {(always (! fair))}"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_log_edge_print_on(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    edge = mocker.MagicMock()
    edge.id = "EdgeID"
    edge.parent_id = "ParentID"
    edge.name = "EdgeName"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.print_on = True

    visitor.write_log_edge(edge)

    expected_call = mocker.call('printf("**EDGE EdgeID(ParentID) = %d\\n", EdgeName)')

    mock_write.assert_has_calls([expected_call])


def test_cwp_write_log_state_print_on(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    state = mocker.MagicMock()
    state.name = "TestState"
    state.id = "StateID"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.print_on = True

    visitor.write_log_state(state)

    expected_calls = [
        mocker.call("if"),
        mocker.call(":: (TestState) -> "),
        mocker.call('printf("**STATE TestState(StateID)\\n")'),
        mocker.call(":: else -> skip"),
        mocker.call("fi"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


@pytest.mark.parametrize(
    "print_on, expected_header, expected_footer",
    [
        (
            True,
            "\n\n//**********LOG STATE************//\n\n",
            'printf("******************************\\n")',
        ),
        (False, "\n\n//***********LOG STATE FILLER*******//\n\n", "skip"),
    ],
)
def test_write_log_state_inline(mocker, print_on, expected_header, expected_footer):
    mock_write_line = mocker.patch.object(CwpLtlVisitor, "write_line")
    mock_write_log_state = mocker.patch.object(CwpLtlVisitor, "write_log_state")
    mock_write_log_edge = mocker.patch.object(CwpLtlVisitor, "write_log_edge")
    mock_write_log_var = mocker.patch.object(CwpLtlVisitor, "write_log_var")

    cwp = mocker.MagicMock()
    cwp.states = {
        "state1": mocker.MagicMock(),
        "state2": mocker.MagicMock(),
    }
    cwp.edges = {"edge1": mocker.MagicMock(), "edge2": mocker.MagicMock()}
    symbol_table = mocker.MagicMock()
    symbol_table._vars = {"var1": "var1_value", "var2": "var2_value"}

    visitor = CwpLtlVisitor(symbol_table)
    visitor.cwp = cwp
    visitor.print_on = print_on
    visitor.tab = 0

    visitor.write_log_state_inline()

    expected_calls = [
        mocker.call(expected_header),
        mocker.call("inline logState(){"),
        mocker.call(expected_footer),
        mocker.call(expected_footer),
        mocker.call("}"),
    ]
    mock_write_line.assert_has_calls(expected_calls, any_order=True)

    mock_write_log_state.assert_any_call(cwp.states["state1"])
    mock_write_log_state.assert_any_call(cwp.states["state2"])

    mock_write_log_edge.assert_any_call(cwp.edges["edge1"])
    mock_write_log_edge.assert_any_call(cwp.edges["edge2"])

    mock_write_log_var.assert_any_call("var1")
    mock_write_log_var.assert_any_call("var2")

    assert visitor.tab == 0


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


# Test for gen_edge_name
def test_gen_edge_name():
    cwp = Cwp()
    assert cwp.gen_edge_name() == "EdgeA"
    assert cwp.gen_edge_name() == "EdgeB"
    assert cwp.gen_edge_name() == "EdgeC"


# Test for calc_end_states
def test_calc_end_states(mocker):
    cwp = Cwp()
    state1 = create_mock_state(mocker, "state1", out_edges=[])
    state2 = create_mock_state(mocker, "state2", out_edges=["edge"])
    state3 = create_mock_state(mocker, "state3", out_edges=[])
    cwp.states = {"state1": state1, "state2": state2, "state3": state3}

    cwp.calc_end_states()
    assert cwp.end_states == [state1, state3]


# Test for _set_leaf_edges
def test_set_leaf_edges(mocker):
    cwp = Cwp()
    state1 = create_mock_state(mocker, "state1")
    state2 = create_mock_state(mocker, "state2")
    edge1 = create_mock_edge(mocker, "edge1", dest=state1)
    edge2 = create_mock_edge(mocker, "edge2", dest=state2)
    edge3 = create_mock_edge(mocker, "edge3", dest=state1)

    state1.out_edges = [edge2]
    state2.out_edges = [edge3]
    cwp.states = {"state1": state1, "state2": state2}
    cwp.start_edge = edge1

    cwp._set_leaf_edges()
    assert edge3.is_leaf is True
    assert edge1.is_leaf is False
    assert edge2.is_leaf is False


def test_parse_states():
    cwp = Cwp()
    mx_states = [
        Element("mxCell", attrib={"id": "state1", "style": "someStyle"}),
        Element("mxCell", attrib={"id": "state2", "style": "anotherStyle"}),
        Element("mxCell", attrib={"id": "edge1", "style": "edgeLabel"}),
    ]

    cwp._parse_states(mx_states)
    assert "state1" in cwp.states
    assert "state2" in cwp.states
    assert "edge1" not in cwp.states


def test_parse_edges(mocker):
    mock_set_source = mocker.patch.object(CwpEdge, "set_source")
    mock_set_dest = mocker.patch.object(CwpEdge, "set_dest")

    cwp = Cwp()
    source_state = mocker.MagicMock()
    dest_state = mocker.MagicMock()
    source_state.out_edges = []
    dest_state.in_edges = []
    cwp.states = {
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

    cwp._parse_edges(mx_edges)

    mock_set_source.assert_called_once_with(source_state)
    mock_set_dest.assert_called_once_with(dest_state)


def test_add_expressions(mocker):
    cwp = Cwp()
    edge = create_mock_edge(mocker, "edge1")
    cwp.edges = {"edge1": edge}

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

    cwp._add_expressions(all_items)
    edge.cleanup_expression.assert_called_with("someExpr")
    assert edge.parent_id == "expr1"


def test_generate_all(mocker):
    instance = CwpLtlVisitor(mocker.MagicMock())
    mock_generate_helper_functions = mocker.patch.object(
        instance, "generate_helper_functions"
    )
    mock_generate_LTL = mocker.patch.object(instance, "generate_LTL")

    instance.generate_all()

    mock_generate_helper_functions.assert_called_once()
    mock_generate_LTL.assert_called_once()


def test_generate_helper_functions(mocker):
    instance = CwpLtlVisitor(mocker.MagicMock())
    mock_write_state_variables = mocker.patch.object(instance, "write_state_variables")
    mock_write_variable_range_invariants = mocker.patch.object(
        instance, "write_variable_range_invariants"
    )
    mock_write_init_states = mocker.patch.object(instance, "write_init_states")
    mock_write_edge_definitions = mocker.patch.object(
        instance, "write_edge_definitions"
    )
    mock_write_update_state = mocker.patch.object(instance, "write_update_state")
    mock_write_log_state_inline = mocker.patch.object(
        instance, "write_log_state_inline"
    )

    instance.print_on = True
    instance.generate_helper_functions()
    mock_write_state_variables.assert_called_once()
    mock_write_variable_range_invariants.assert_called_once()
    mock_write_init_states.assert_called_once()
    mock_write_edge_definitions.assert_called_once()
    mock_write_update_state.assert_called_once()
    mock_write_log_state_inline.assert_called_once()

    mock_write_log_state_inline.reset_mock()
    instance.print_on = False
    instance.generate_helper_functions()
    mock_write_log_state_inline.assert_not_called()


def test_generate_LTL(mocker):
    instance = CwpLtlVisitor(mocker.MagicMock())
    instance.cwp = mocker.MagicMock()
    mock_write_global_properties = mocker.patch.object(
        instance, "write_global_properties"
    )
    mock_write_state_properties = mocker.patch.object(
        instance, "write_state_properties"
    )
    mock_write_line = mocker.patch.object(instance, "write_line")

    instance.cwp.states = {
        "state1": mocker.MagicMock(),
        "state2": mocker.MagicMock(),
    }

    instance.generate_LTL()

    mock_write_global_properties.assert_called_once()

    assert mock_write_state_properties.call_count == len(instance.cwp.states)
    mock_write_state_properties.assert_any_call(instance.cwp.states["state1"])
    mock_write_state_properties.assert_any_call(instance.cwp.states["state2"])

    expected_calls = [mocker.call(""), mocker.call(""), mocker.call("")]
    mock_write_line.assert_has_calls(expected_calls)
