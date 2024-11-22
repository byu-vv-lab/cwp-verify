import pytest
from xml.etree.ElementTree import Element
from bpmncwpverify.builder.bpmn_builder import BpmnBuilder
from bpmncwpverify.core.bpmn import Node, Task
from returns.result import Success


def test_build_method(mocker):
    mock_bpmn = mocker.patch("bpmncwpverify.core.bpmn.Bpmn", autospec=True)
    mock_bpmn_instance = mock_bpmn.return_value
    mock_bpmn_instance.accept = mocker.Mock()

    builder = BpmnBuilder()

    builder._bpmn = mock_bpmn_instance
    mock_bpmn_instance.processes = [1]
    mock_bpmn_instance.add_inter_process_msg = [1]

    result = builder.build()

    assert isinstance(result, Success)
    assert result.unwrap() == mock_bpmn_instance


def test_bpmn_build_no_inter_process_messages(mocker):
    bpmn_builder = BpmnBuilder()

    bpmn = mocker.Mock()
    bpmn_builder._bpmn = bpmn
    process1 = mocker.Mock()
    process2 = mocker.Mock()

    task1 = Task(Element("task", attrib={"id": "task1"}))
    task2 = Task(Element("task", attrib={"id": "task2"}))

    process1.all_items.return_value = {"task1": task1}
    process2.all_items.return_value = {"task2": task2}

    bpmn.processes = {"process1": process1, "process2": process2}
    bpmn.inter_process_msgs = {}

    with pytest.raises(
        Exception, match="No inter process messages exist in this bpmn model."
    ):
        bpmn_builder.build()


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
