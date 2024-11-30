from bpmncwpverify.error import MessageError
import pytest
from xml.etree.ElementTree import Element
from bpmncwpverify.builder.bpmn_builder import BpmnBuilder
from bpmncwpverify.core.bpmn import Node
from returns.result import Success


def test_build_method(mocker):
    mock_bpmn = mocker.patch("bpmncwpverify.core.bpmn.Bpmn", autospec=True)
    mock_bpmn_instance = mock_bpmn.return_value
    mock_bpmn_instance.accept = mocker.Mock()

    builder = BpmnBuilder()

    builder._bpmn = mock_bpmn_instance
    builder._msg_connects_diff_pools = mocker.MagicMock()
    mock_bpmn_instance.processes = [1]
    mock_bpmn_instance.add_inter_process_msg = [1]

    result = builder.build()

    assert isinstance(result, Success)
    assert result.unwrap() == mock_bpmn_instance


def test_add_message_valid_input(mocker):
    mock_bpmn = mocker.MagicMock()
    mock_source_node = mocker.MagicMock(spec=Node)
    mock_target_node = mocker.MagicMock(spec=Node)
    mock_msg_flow = mocker.MagicMock(spec=Element)
    mock_msg_flow.get.side_effect = lambda x: {
        "sourceRef": "source_id",
        "targetRef": "target_id",
    }[x]

    mock_bpmn.get_element_from_id_mapping.side_effect = lambda x: {
        "source_id": mock_source_node,
        "target_id": mock_target_node,
    }[x]

    builder = BpmnBuilder()
    builder._bpmn = mock_bpmn

    builder.add_message(mock_msg_flow)

    mock_bpmn.add_inter_process_msg.assert_called_once()
    mock_bpmn.store_element.assert_called_once()
    assert mock_source_node.add_out_msg.called
    assert mock_target_node.add_in_msg.called


def test_add_message_missing_refs(mocker):
    mock_bpmn = mocker.MagicMock()
    mock_msg_flow = mocker.MagicMock(spec=Element)
    mock_msg_flow.get.side_effect = lambda x: {
        "sourceRef": None,
        "targetRef": "target_id",
    }[x]

    builder = BpmnBuilder()
    builder._bpmn = mock_bpmn

    with pytest.raises(
        Exception, match="source ref or target ref not included with message"
    ):
        builder.add_message(mock_msg_flow)


def test_add_message_invalid_nodes(mocker):
    mock_bpmn = mocker.Mock()
    mock_msg_flow = mocker.MagicMock(spec=Element)
    mock_msg_flow.get.side_effect = lambda x: {
        "sourceRef": "source_id",
        "targetRef": "target_id",
    }[x]
    mock_bpmn.get_element_from_id_mapping.side_effect = lambda x: {
        "source_id": "invalid_node",
        "target_id": "invalid_node",
    }[x]

    builder = BpmnBuilder()
    builder._bpmn = mock_bpmn

    with pytest.raises(TypeError, match="to_node or from_node is not of type Node"):
        builder.add_message(mock_msg_flow)


def test_check_messages_valid(mocker):
    mock_bpmn = mocker.MagicMock()

    mock_message1 = mocker.MagicMock()
    mock_message1.id = "message1"
    mock_message1.target_node.id = "target1"
    mock_message1.source_node.id = "source1"
    mock_bpmn.inter_process_msgs.values.return_value = [mock_message1]

    mock_process = mocker.MagicMock()
    mock_process.all_items.return_value = {"target1", "source1"}
    mock_bpmn.processes.values.return_value = [mock_process]

    obj = BpmnBuilder()
    obj._bpmn = mock_bpmn

    with pytest.raises(
        Exception,
    ) as exc_info:
        obj._msg_connects_diff_pools()
    assert isinstance(exc_info.value.args[0], MessageError)
    assert (
        "Error at Message message1, A message flow cannot connect nodes in the same pool."
        == str(exc_info.value.args[0].msg)
    )


def test_check_messages_no_intersection(mocker):
    mock_bpmn = mocker.MagicMock()

    mock_message1 = mocker.MagicMock()
    mock_message1.target_node.id = "target1"
    mock_message1.source_node.id = "source2"
    mock_bpmn.inter_process_msgs.values.return_value = [mock_message1]

    mock_process = mocker.MagicMock()
    mock_process.all_items.return_value = {"item1", "item2"}
    mock_bpmn.processes.values.return_value = [mock_process]

    obj = BpmnBuilder()
    obj._bpmn = mock_bpmn

    obj._msg_connects_diff_pools()


def test_check_messages_empty(mocker):
    mock_bpmn = mocker.MagicMock()

    mock_bpmn.inter_process_msgs.values.return_value = []

    mock_process = mocker.MagicMock()
    mock_process.all_items.return_value = []
    mock_bpmn.processes.values.return_value = [mock_process]

    obj = mocker.MagicMock()
    obj._bpmn = mock_bpmn

    obj._msg_connects_diff_pools()
