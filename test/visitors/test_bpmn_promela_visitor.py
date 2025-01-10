import pytest
from bpmncwpverify.visitors.bpmn_promela_visitor import PromelaGenVisitor


@pytest.fixture
def string_manager():
    return PromelaGenVisitor.StringManager()


@pytest.fixture
def promela_visitor():
    return PromelaGenVisitor()


def test_string_manager_initial_state(string_manager):
    assert string_manager.contents == []
    assert string_manager.indent == 0


def test_string_manager_write_str(string_manager):
    string_manager.write_str("test", 1)
    assert repr(string_manager) == "test\n"


def test_string_manager_indent(string_manager):
    string_manager._inc_indent()
    string_manager.write_str("indented", 1)
    assert repr(string_manager) == "\tindented\n"

    string_manager._dec_indent()
    string_manager.write_str("not indented", 1)
    assert repr(string_manager) == "\tindented\nnot indented\n"


def test_string_manager_assertion_error_on_negative_indent(string_manager):
    with pytest.raises(AssertionError):
        string_manager._dec_indent()


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
