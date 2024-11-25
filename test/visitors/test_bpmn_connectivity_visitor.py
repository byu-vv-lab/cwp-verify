from bpmncwpverify.visitors.bpmn_connectivity_visitor import BpmnConnectivityVisitor
import pytest
from bpmncwpverify.core.bpmn import Node


def test_ensure_in_and_out_messages(mocker):
    def setup_node(id, in_msgs=None, out_msgs=None, message_event_definition=""):
        node = mocker.Mock(spec=Node)
        node.id = id
        node.in_msgs = in_msgs or []
        node.out_msgs = out_msgs or []
        node.message_event_definition = message_event_definition
        return node

    visitor = BpmnConnectivityVisitor()

    # Test ensure_in_messages - no message event definition
    test_node_in = setup_node("123", in_msgs=[1])
    with pytest.raises(
        Exception,
        match="Exception occurred while visiting event:123. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool.",
    ):
        visitor._ensure_in_messages(test_node_in, "event")

    # Test ensure_in_messages - with message event definition
    test_node_in_def = setup_node(
        "123", in_msgs=[1], message_event_definition="test-id"
    )
    visitor._ensure_in_messages(test_node_in_def, "event")  # no error expected

    # Test ensure_out_messages - no message event definition
    test_node_out = setup_node("123", out_msgs=[1])
    with pytest.raises(
        Exception,
        match="Exception occurred while visiting event:123. A message flow can only come from a Messege end or intermediate event; Send, User, or Service task; Subprocess; or black box pool.",
    ):
        visitor._ensure_out_messages(test_node_out, "event")

    # Test ensure_out_messages - with message event definition
    test_node_out_def = setup_node(
        "123", out_msgs=[1], message_event_definition="test-id"
    )
    visitor._ensure_out_messages(test_node_out_def, "event")  # no error expected
