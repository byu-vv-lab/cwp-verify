from bpmncwpverify.core.bpmn import Task
import pytest
from bpmncwpverify.visitors.bpmn_promela_visitor import (
    IndentAction,
    PromelaGenVisitor,
    NL_NONE,
    NL_SINGLE,
)


@pytest.fixture
def string_manager_factory():
    def _factory():
        return PromelaGenVisitor.StringManager()

    return _factory


@pytest.fixture
def promela_visitor():
    return PromelaGenVisitor()


def test_string_manager_initial_state(string_manager_factory):
    manager1 = string_manager_factory()
    assert manager1.contents == []
    assert manager1.indent == NL_NONE


def test_string_manager_write_str(string_manager_factory):
    manager1 = string_manager_factory()
    manager1.write_str("test", NL_SINGLE, IndentAction.NIL)
    assert repr(manager1) == "test\n"


def test_string_manager_write_str_no_tab(string_manager_factory):
    manager1: PromelaGenVisitor.StringManager = string_manager_factory()
    manager2: PromelaGenVisitor.StringManager = string_manager_factory()
    manager1.contents = []

    manager1.indent = 1

    manager1.write_str("hello", NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello"]

    manager2.write_str("test string 1", NL_NONE, IndentAction.NIL)
    manager2.write_str("test string 2", NL_NONE, IndentAction.NIL)

    manager1.write_str(manager2, NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello", "test string 1", "test string 2"]


def test_string_manager_write_str_with_tab(string_manager_factory):
    manager1: PromelaGenVisitor.StringManager = string_manager_factory()
    manager2: PromelaGenVisitor.StringManager = string_manager_factory()
    manager1.contents = []
    manager1.indent = 1

    manager1.write_str("hello", NL_SINGLE, IndentAction.NIL)

    assert manager1.contents == ["hello\n"]

    manager2.write_str("test string 1", NL_SINGLE, IndentAction.NIL)
    manager2.write_str("test string 2", NL_SINGLE, IndentAction.NIL)

    manager1.write_str(manager2, NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello\n", "\ttest string 1\n", "\ttest string 2\n"]


def test_string_manager_indent_increment(string_manager_factory):
    manager = string_manager_factory()
    manager.write_str("start", NL_SINGLE, IndentAction.INC)
    manager.write_str("indented", NL_SINGLE, IndentAction.NIL)
    assert repr(manager) == "start\n\tindented\n"


def test_string_manager_indent_decrement(string_manager_factory):
    manager = string_manager_factory()
    manager.indent = 1
    manager.write_str("start", NL_SINGLE, IndentAction.DEC)
    manager.write_str("indented", NL_SINGLE, IndentAction.NIL)
    assert repr(manager) == "start\nindented\n"


def test_string_manager_multiple_calls(string_manager_factory):
    manager = string_manager_factory()
    manager.indent = 1
    manager.write_str("line1", NL_SINGLE, IndentAction.INC)
    manager.write_str("line2", NL_SINGLE, IndentAction.INC)
    manager.write_str("line3", NL_SINGLE, IndentAction.NIL)
    manager.write_str("line4", NL_SINGLE, IndentAction.DEC)

    expected_output = "line1\n\t\tline2\n\t\t\tline3\n\t\tline4\n"
    assert repr(manager) == expected_output


def test_string_manager_needs_tab_logic(string_manager_factory):
    manager = string_manager_factory()
    manager.write_str("first", NL_NONE, IndentAction.NIL)
    manager.write_str("second", NL_SINGLE, IndentAction.NIL)
    manager.write_str("third", NL_SINGLE, IndentAction.NIL)
    manager.write_str("fourth", NL_NONE, IndentAction.NIL)

    expected_output = "firstsecond\nthird\nfourth"
    assert repr(manager) == expected_output


def test_string_manager_indent(string_manager_factory):
    manager1 = string_manager_factory()
    manager1._inc_indent()
    assert manager1.indent == NL_SINGLE

    manager1._dec_indent()
    assert manager1.indent == NL_NONE


def test_string_manager_assertion_error_on_negative_indent(string_manager_factory):
    manager1 = string_manager_factory()
    with pytest.raises(AssertionError):
        manager1._dec_indent()


############################
# PromelaGenVisitor tests
############################


def test_promela_gen_visitor_initial_state(promela_visitor):
    assert isinstance(promela_visitor.defs, PromelaGenVisitor.StringManager)
    assert isinstance(
        promela_visitor.init_proc_contents, PromelaGenVisitor.StringManager
    )
    assert isinstance(promela_visitor.promela, PromelaGenVisitor.StringManager)
    assert repr(promela_visitor) == ""


def test_generate_location_label(promela_visitor, mocker):
    node = mocker.Mock(spec=Task)
    node.name = "TEST"
    flow_or_message = mocker.Mock()
    flow_or_message.source_node.name = "SRC"

    ret_val = promela_visitor._generate_location_label(node, flow_or_message)

    assert ret_val == "TEST_FROM_SRC"

    ret_val = promela_visitor._generate_location_label(node)

    assert ret_val == "TEST_END"

    node_no_spec = mocker.Mock()
    node_no_spec.name = "TEST"

    ret_val = promela_visitor._generate_location_label(node_no_spec)

    assert ret_val == "TEST"


def test_get_consume_locations(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.in_flows = []
    node1.in_msgs = []
    node1.name = "NODE1"

    node2 = mocker.Mock()
    node2.name = "NODE2"

    node3 = mocker.Mock()
    node3.name = "NODE3"

    assert promela_visitor._get_consume_locations(node1) == []

    flow1 = mocker.Mock()
    flow1.source_node = node1

    flow2 = mocker.Mock()
    flow2.source_node = node3

    node2.in_flows = [flow1]
    node2.in_msgs = [flow2]

    assert promela_visitor._get_consume_locations(node2) == [
        "NODE2_FROM_NODE1",
        "NODE2_FROM_NODE3",
    ]


def test_get_put_locations(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.out_flows = []
    node1.out_msgs = []
    node1.name = "NODE1"

    node2 = mocker.Mock()
    node2.name = "NODE2"

    node3 = mocker.Mock()
    node3.name = "NODE3"

    assert promela_visitor._get_put_locations(node1) == []

    flow1 = mocker.Mock()
    flow1.source_node = node1
    flow1.target_node = node2

    flow2 = mocker.Mock()
    flow2.source_node = node1
    flow2.target_node = node3

    node1.out_flows = [flow1]
    node1.out_msgs = [flow2]

    assert promela_visitor._get_put_locations(node1) == [
        "NODE2_FROM_NODE1",
        "NODE3_FROM_NODE1",
    ]


def test_build_guard(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.name = "NODE1"

    node2 = mocker.Mock()
    node2.name = "NODE2"

    node3 = mocker.Mock()
    node3.name = "NODE3"

    flow1 = mocker.Mock()
    flow1.source_node = node2
    flow1.target_node = node1

    flow2 = mocker.Mock()
    flow2.source_node = node3
    flow2.target_node = node1

    node1.in_flows = [flow1, flow2]
    node1.in_msgs = []

    guard = promela_visitor._build_guard(node1)

    assert str(guard) == "hasToken(NODE1_FROM_NODE2)||hasToken(NODE1_FROM_NODE3)"
