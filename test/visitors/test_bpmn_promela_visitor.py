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


def test_promela_gen_visitor_initial_state(promela_visitor):
    assert repr(promela_visitor) == ""


def test_promela_gen_visitor_visits(promela_visitor, mocker):
    mock_event = mocker.Mock()
    assert promela_visitor.visit_start_event(mock_event) is True
    assert promela_visitor.visit_end_event(mock_event) is True
    assert promela_visitor.visit_intermediate_event(mock_event) is True
    assert promela_visitor.visit_task(mock_event) is True
    assert promela_visitor.visit_exclusive_gateway(mock_event) is True
    assert promela_visitor.visit_parallel_gateway(mock_event) is True
    assert promela_visitor.visit_message_flow(mock_event) is True
    assert promela_visitor.visit_process(mock_event) is True
    assert promela_visitor.visit_bpmn(mock_event) is True


def test_promela_gen_visitor_end_visits(promela_visitor, mocker):
    mock_process = mocker.Mock()
    mock_bpmn = mocker.Mock()

    promela_visitor.end_visit_process(mock_process)
    promela_visitor.end_visit_bpmn(mock_bpmn)

    assert repr(promela_visitor) == ""
