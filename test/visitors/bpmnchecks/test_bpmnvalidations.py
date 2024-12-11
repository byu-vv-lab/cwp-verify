from bpmncwpverify.error import (
    BpmnFlowIncomingError,
    BpmnGraphConnError,
    BpmnMissingEventsError,
    BpmnSeqFlowEndEventError,
    BpmnSeqFlowNoExprError,
    BpmnTaskFlowError,
)
import pytest
from bpmncwpverify.core.bpmn import EndEvent, ExclusiveGatewayNode, StartEvent, Task
from bpmncwpverify.visitors.bpmnchecks.bpmnvalidations import (
    ProcessConnectivityVisitor,
    ValidateBpmnIncomingFlows,
    validate_start_end_events,
    ValidateSeqFlowVisitor,
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


class TestProcessConnectivityVisitor:
    def test_fully_connected_graph(self, setup_process_and_visitor):
        process, visitor, start_event, end_event, other_event = (
            setup_process_and_visitor
        )
        # Simulate a fully connected graph
        process.all_items.return_value = {
            "start": start_event,
            "middle": other_event,
            "end": end_event,
        }
        visitor.visited = {start_event, other_event, end_event}

        # No exception should be raised
        visitor.end_visit_process(process)

    def test_disconnected_graph_raises_exception(self, setup_process_and_visitor):
        process, visitor, start_event, end_event, other_event = (
            setup_process_and_visitor
        )
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

    def test_no_start_event_with_incoming_msgs(self, setup_process_and_visitor):
        process, visitor, _, end_event, other_event = setup_process_and_visitor
        # Simulate no StartEvent but a valid starting point with incoming messages
        process.all_items.return_value = {"middle": other_event, "end": end_event}
        visitor.visited = {other_event, end_event}
        other_event.in_msgs = [1]
        end_event.in_msgs = []

        # No exception should be raised
        visitor.end_visit_process(process)

    def test_end_event(self, mocker):
        event = mocker.MagicMock()

        obj = ProcessConnectivityVisitor()

        result = obj.visit_end_event(event)

        assert result is True
        assert event in obj.visited


class TestValidateSeqFlowVisitor:
    def test_validate_out_flows_valid_case(self, mocker):
        visitor = ValidateSeqFlowVisitor()
        gateway = mocker.MagicMock()
        gateway.out_flows = [
            mocker.MagicMock(expression=True),
            mocker.MagicMock(expression=True),
        ]
        # Should not raise any exceptions
        visitor._validate_out_flows(gateway)

    def test_validate_out_flows_invalid_case(self, mocker):
        visitor = ValidateSeqFlowVisitor()
        gateway = mocker.MagicMock()
        gateway.id = "gateway1"
        gateway.out_flows = [
            mocker.MagicMock(expression=True, id="flow1"),
            mocker.MagicMock(expression=False, id="flow2"),
        ]
        with pytest.raises(Exception) as exc_info:
            visitor._validate_out_flows(gateway)
        assert isinstance(exc_info.value.args[0], BpmnSeqFlowNoExprError)

    def test_visit_exclusive_gateway_valid(self, mocker):
        visitor = ValidateSeqFlowVisitor()
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
        visitor._validate_out_flows.assert_called_once_with(gateway)

    def test_visit_exclusive_gateway_invalid(self, mocker):
        visitor = ValidateSeqFlowVisitor()
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

    def test_visit_parallel_gateway_valid(self, mocker):
        visitor = ValidateSeqFlowVisitor()
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
        visitor._validate_out_flows.assert_called_once_with(gateway)

    def test_visit_parallel_gateway_invalid(self, mocker):
        visitor = ValidateSeqFlowVisitor()
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

    def test_visit_task_with_good_task(self, mocker):
        visitor = ValidateSeqFlowVisitor()
        task = mocker.MagicMock()
        task.out_flows = [mocker.MagicMock()]
        task.in_flows = [mocker.MagicMock()]

        # No error thrown
        visitor.visit_task(task)

    def test_visit_task_with_bad_task(self, mocker):
        visitor = ValidateSeqFlowVisitor()
        task = mocker.MagicMock()
        task.id = "task1"
        task.out_flows = []
        task.in_flows = []

        with pytest.raises(Exception) as exc_info:
            visitor.visit_task(task)
        assert isinstance(exc_info.value.args[0], BpmnTaskFlowError)
        assert "task1" == str(exc_info.value.args[0].task_id)

    def test_visit_end_event_with_outgoing_flows(self, mocker):
        event = mocker.MagicMock()
        event.out_flows = ["flow1"]
        event.id = "end_event_2"

        obj = ValidateSeqFlowVisitor()

        with pytest.raises(Exception) as exc_info:
            obj.visit_end_event(event)

        assert isinstance(exc_info.value.args[0], BpmnSeqFlowEndEventError)
        assert "end_event_2" == str(exc_info.value.args[0].event_id)

    def test_visit_end_event_no_outgoing_flows(self, mocker):
        event = mocker.MagicMock()
        event.out_flows = []
        event.id = "end_event_1"

        obj = ValidateSeqFlowVisitor()

        result = obj.visit_end_event(event)

        assert result is True

    def test_no_start_event_with_no_incoming_msgs(self, setup_process_and_visitor):
        process, _, _, end_event, other_event = setup_process_and_visitor
        process.all_items.return_value = {"middle": other_event, "end": end_event}
        other_event.in_msgs = []
        end_event.in_msgs = []

        with pytest.raises(Exception) as exc_info:
            validate_start_end_events(process)

        assert isinstance(exc_info.value.args[0], BpmnMissingEventsError)

    def test_no_end_event_raises_exception(self, setup_process_and_visitor):
        process, _, start_event, _, other_event = setup_process_and_visitor
        process.all_items.return_value = {"start": start_event, "middle": other_event}
        start_event.in_msgs = []
        other_event.in_msgs = [1]

        with pytest.raises(Exception) as exc_info:
            validate_start_end_events(process)

        assert isinstance(exc_info.value.args[0], BpmnMissingEventsError)

    def test_no_start_or_end_event_raises_exception(self, setup_process_and_visitor):
        process, _, _, _, other_event = setup_process_and_visitor
        # Simulate no StartEvent or EndEvent
        process.all_items.return_value = {"middle": other_event}
        other_event.in_msgs = []

        with pytest.raises(Exception) as exc_info:
            validate_start_end_events(process)

        assert isinstance(exc_info.value.args[0], BpmnMissingEventsError)


class TestValidateBpmnIncomingFlows:
    def test_visit_end_event_with_incoming_flows(self, mocker):
        mock_event = mocker.MagicMock(spec=EndEvent)
        mock_event.id = "end1"
        mock_event.in_flows = ["flow1"]

        visitor = ValidateBpmnIncomingFlows()
        result = visitor.visit_end_event(mock_event)

        assert result is True

    def test_visit_end_event_without_incoming_flows(self, mocker):
        mock_event = mocker.MagicMock(spec=EndEvent)
        mock_event.id = "end1"
        mock_event.in_flows = []

        visitor = ValidateBpmnIncomingFlows()

        with pytest.raises(Exception) as exc_info:
            visitor.visit_end_event(mock_event)

        assert isinstance(exc_info.value.args[0], BpmnFlowIncomingError)
        assert exc_info.value.args[0].node_id == "end1"

    def test_visit_task_with_incoming_flows(self, mocker):
        mock_task = mocker.MagicMock(spec=Task)
        mock_task.id = "task1"
        mock_task.in_flows = ["flow1"]

        visitor = ValidateBpmnIncomingFlows()
        result = visitor.visit_task(mock_task)

        assert result is True

    def test_visit_task_without_incoming_flows(self, mocker):
        mock_task = mocker.MagicMock(spec=Task)
        mock_task.id = "task1"
        mock_task.in_flows = []

        visitor = ValidateBpmnIncomingFlows()

        with pytest.raises(Exception) as exc_info:
            visitor.visit_task(mock_task)

        assert isinstance(exc_info.value.args[0], BpmnFlowIncomingError)
        assert exc_info.value.args[0].node_id == "task1"

    def test_visit_exclusive_gateway_with_incoming_flows(self, mocker):
        mock_gateway = mocker.MagicMock(spec=ExclusiveGatewayNode)
        mock_gateway.id = "gateway1"
        mock_gateway.in_flows = ["flow1"]

        visitor = ValidateBpmnIncomingFlows()
        result = visitor.visit_exclusive_gateway(mock_gateway)

        assert result is True

    def test_visit_exclusive_gateway_without_incoming_flows(self, mocker):
        mock_gateway = mocker.MagicMock(spec=ExclusiveGatewayNode)
        mock_gateway.id = "gateway1"
        mock_gateway.in_flows = []

        visitor = ValidateBpmnIncomingFlows()

        with pytest.raises(Exception) as exc_info:
            visitor.visit_exclusive_gateway(mock_gateway)

        assert isinstance(exc_info.value.args[0], BpmnFlowIncomingError)
        assert exc_info.value.args[0].node_id == "gateway1"