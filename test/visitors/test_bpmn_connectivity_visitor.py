from bpmncwpverify.visitors.bpmn_connectivity_visitor import BpmnConnectivityVisitor
import pytest
from bpmncwpverify.core.bpmn import Node


def test_ensure_in_messages_no_message_event_def(mocker):
    test_node = mocker.Mock(spec=Node)
    test_node.id = "123"
    test_node.in_msgs = [1]
    test_node.message_event_definition = ""

    visitor = BpmnConnectivityVisitor()

    with pytest.raises(
        Exception,
        match="Exception occurred while visiting event:123. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool.",
    ):
        visitor._ensure_in_messages(test_node, "event")
