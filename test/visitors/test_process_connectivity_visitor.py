# type: ignore
from bpmncwpverify.error import (
    BpmnGraphConnError,
    BpmnMissingEventsError,
    BpmnSeqFlowEndEventError,
    BpmnSeqFlowNoExprError,
    BpmnTaskFlowError,
)
import pytest
from bpmncwpverify.core.bpmn import EndEvent, StartEvent
from bpmncwpverify.visitors.process_connectivity_visitor import (
    ProcessConnectivityVisitor,
)


@pytest.fixture
def setup_process_and_visitor(mocker):
    # Create a mock Process and visitor instance
    process = mocker.MagicMock()
    start_event = mocker.Mock(spec=StartEvent)
    end_event = mocker.Mock(spec=EndEvent)
    other_event = mocker.Mock()

    visitor = ProcessConnectivityVisitor()

    return process, visitor, start_event, end_event, other_event


def test_fully_connected_graph(setup_process_and_visitor):
    process, visitor, start_event, end_event, other_event = setup_process_and_visitor
    # Simulate a fully connected graph
    process.all_items.return_value = {
        "start": start_event,
        "middle": other_event,
        "end": end_event,
    }
    visitor.visited = {start_event, other_event, end_event}

    # No exception should be raised
    visitor.end_visit_process(process)


def test_disconnected_graph_raises_exception(setup_process_and_visitor):
    process, visitor, start_event, end_event, other_event = setup_process_and_visitor
    # Simulate a disconnected graph
    process.all_items.return_value = {
        "start": start_event,
        "middle": other_event,
        "end": end_event,
    }
    visitor.visited = {start_event, other_event}  # Missing end_event

    with pytest.raises(Exception) as exc_info:
        visitor.end_visit_process(process)

    assert isinstance(exc_info.value.args[0], BpmnGraphConnError)


def test_no_start_or_end_event_raises_exception(setup_process_and_visitor):
    process, visitor, _, _, other_event = setup_process_and_visitor
    # Simulate no StartEvent or EndEvent
    process.all_items.return_value = {"middle": other_event}
    visitor.visited = {other_event}
    other_event.in_msgs = []

    with pytest.raises(Exception) as exc_info:
        visitor.end_visit_process(process)

    assert isinstance(exc_info.value.args[0], BpmnMissingEventsError)


def test_no_start_event_with_incoming_msgs(setup_process_and_visitor):
    process, visitor, _, end_event, other_event = setup_process_and_visitor
    # Simulate no StartEvent but a valid starting point with incoming messages
    process.all_items.return_value = {"middle": other_event, "end": end_event}
    visitor.visited = {other_event, end_event}
    other_event.in_msgs = [1]
    end_event.in_msgs = []

    # No exception should be raised
    visitor.end_visit_process(process)


def test_no_end_event_raises_exception(setup_process_and_visitor):
    process, visitor, start_event, end_event, other_event = setup_process_and_visitor
    # Simulate no EndEvent
    process.all_items.return_value = {"start": start_event, "middle": other_event}
    visitor.visited = {start_event, other_event}
    start_event.in_msgs = []
    other_event.in_msgs = [1]

    with pytest.raises(Exception) as exc_info:
        visitor.end_visit_process(process)

    assert isinstance(exc_info.value.args[0], BpmnMissingEventsError)


def test_no_start_event_with_no_incoming_msgs(setup_process_and_visitor):
    process, visitor, _, end_event, other_event = setup_process_and_visitor
    # Simulate no StartEvent but a valid starting point with incoming messages
    process.all_items.return_value = {"middle": other_event, "end": end_event}
    visitor.visited = {other_event, end_event}
    other_event.in_msgs = []
    end_event.in_msgs = []

    with pytest.raises(Exception) as exc_info:
        visitor.end_visit_process(process)

    assert isinstance(exc_info.value.args[0], BpmnMissingEventsError)


def test_valid_graph_resets_visited(setup_process_and_visitor):
    process, visitor, start_event, end_event, _ = setup_process_and_visitor

    process.all_items.return_value = {"start": start_event, "end": end_event}
    visitor.visited = {start_event, end_event}
    start_event.in_msgs = []
    end_event.in_msgs = [1]

    visitor.end_visit_process(process)

    assert visitor.visited == set()


def test_visit_end_event_no_outgoing_flows(mocker):
    event = mocker.MagicMock()
    event.out_flows = []
    event.id = "end_event_1"

    obj = ProcessConnectivityVisitor()
    obj.visited = set()

    result = obj.visit_end_event(event)

    assert result is True
    assert event in obj.visited


def test_visit_end_event_with_outgoing_flows(mocker):
    event = mocker.MagicMock()
    event.out_flows = ["flow1"]
    event.id = "end_event_2"

    obj = ProcessConnectivityVisitor()
    obj.visited = set()

    with pytest.raises(Exception) as exc_info:
        obj.visit_end_event(event)

    assert isinstance(exc_info.value.args[0], BpmnSeqFlowEndEventError)
    assert "end_event_2" == str(exc_info.value.args[0].event_id)
    assert event not in obj.visited


def test_validate_out_flows_valid_case(mocker):
    visitor = ProcessConnectivityVisitor()
    gateway = mocker.MagicMock()
    gateway.out_flows = [
        mocker.MagicMock(expression=True),
        mocker.MagicMock(expression=True),
    ]
    # Should not raise any exceptions
    visitor._validate_out_flows(gateway)


def test_validate_out_flows_invalid_case(mocker):
    visitor = ProcessConnectivityVisitor()
    gateway = mocker.MagicMock()
    gateway.id = "gateway1"
    gateway.out_flows = [
        mocker.MagicMock(expression=True, id="flow1"),
        mocker.MagicMock(expression=False, id="flow2"),
    ]
    with pytest.raises(Exception) as exc_info:
        visitor._validate_out_flows(gateway)
    assert isinstance(exc_info.value.args[0], BpmnSeqFlowNoExprError)


def test_visit_exclusive_gateway_valid(mocker):
    visitor = ProcessConnectivityVisitor()
    gateway = mocker.MagicMock()
    gateway.out_flows = [
        mocker.MagicMock(expression=True),
        mocker.MagicMock(expression=True),
    ]
    mocker.patch.object(
        visitor, "_validate_out_flows", wraps=visitor._validate_out_flows
    )
    result = visitor.visit_exclusive_gateway(gateway)
    assert result is True
    assert gateway in visitor.visited
    visitor._validate_out_flows.assert_called_once_with(gateway)


def test_visit_exclusive_gateway_invalid(mocker):
    visitor = ProcessConnectivityVisitor()
    gateway = mocker.MagicMock()
    gateway.out_flows = [
        mocker.MagicMock(expression=True),
        mocker.MagicMock(expression=False),
    ]
    mocker.patch.object(
        visitor, "_validate_out_flows", wraps=visitor._validate_out_flows
    )
    with pytest.raises(Exception):
        visitor.visit_exclusive_gateway(gateway)
    visitor._validate_out_flows.assert_called_once_with(gateway)


def test_visit_parallel_gateway_valid(mocker):
    visitor = ProcessConnectivityVisitor()
    gateway = mocker.MagicMock()
    gateway.out_flows = [
        mocker.MagicMock(expression=True),
        mocker.MagicMock(expression=True),
    ]
    mocker.patch.object(
        visitor, "_validate_out_flows", wraps=visitor._validate_out_flows
    )
    result = visitor.visit_parallel_gateway(gateway)
    assert result is True
    assert gateway in visitor.visited
    visitor._validate_out_flows.assert_called_once_with(gateway)


def test_visit_parallel_gateway_invalid(mocker):
    visitor = ProcessConnectivityVisitor()
    gateway = mocker.MagicMock()
    gateway.out_flows = [
        mocker.MagicMock(expression=True),
        mocker.MagicMock(expression=False),
    ]
    mocker.patch.object(
        visitor, "_validate_out_flows", wraps=visitor._validate_out_flows
    )
    with pytest.raises(Exception):
        visitor.visit_parallel_gateway(gateway)
    visitor._validate_out_flows.assert_called_once_with(gateway)


def test_visit_task_with_good_task(mocker):
    visitor = ProcessConnectivityVisitor()
    task = mocker.MagicMock()
    task.out_flows = [mocker.MagicMock()]
    task.in_flows = [mocker.MagicMock()]

    # No error thrown
    visitor.visit_task(task)


def test_visit_task_with_bad_task(mocker):
    visitor = ProcessConnectivityVisitor()
    task = mocker.MagicMock()
    task.id = "task1"
    task.out_flows = []
    task.in_flows = []

    with pytest.raises(Exception) as exc_info:
        visitor.visit_task(task)
    assert isinstance(exc_info.value.args[0], BpmnTaskFlowError)
    assert "task1" == str(exc_info.value.args[0].task_id)
