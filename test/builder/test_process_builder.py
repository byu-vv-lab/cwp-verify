# type: ignore
from bpmncwpverify.builder.process_builder import ProcessBuilder
from bpmncwpverify.core.bpmn import Node, SequenceFlow
from bpmncwpverify.core.state import State
from returns.result import Success


def test_add_element(mocker):
    mock_element = mocker.MagicMock()
    mock_element.id = "1"

    builder = ProcessBuilder(mocker.MagicMock(), mocker.MagicMock())

    mock_process = mocker.MagicMock()
    builder._process = mock_process

    builder.with_element(mock_element)

    mock_process.__setitem__.assert_called_once_with("1", mock_element)


def test_build_graph(mocker):
    mock_process = mocker.MagicMock()

    class MockNode(Node):
        def __init__(self, id):
            self.id = id
            self.out_flows = []
            self.in_flows = []

        def add_out_flow(self, flow):
            self.out_flows.append(flow)

        def add_in_flow(self, flow):
            self.in_flows.append(flow)

    element_1 = mocker.MagicMock(
        attrib={"id": "flow_1", "sourceRef": "node_1", "targetRef": "node_2"}
    )
    element_2 = mocker.MagicMock(
        attrib={"id": "flow_2", "sourceRef": "node_2", "targetRef": "node_1"}
    )

    flow_1 = mocker.MagicMock(spec=SequenceFlow, element=element_1, expression="")
    flow_2 = mocker.MagicMock(spec=SequenceFlow, element=element_2, expression="")

    node_1 = MockNode(id="node_1")
    node_2 = MockNode(id="node_2")

    mock_process.__getitem__.side_effect = lambda key: {
        "flow_1": flow_1,
        "flow_2": flow_2,
        "node_1": node_1,
        "node_2": node_2,
    }[key]

    mock_process.element.findall.return_value = [element_1, element_2]

    builder = ProcessBuilder(mocker.Mock(), mocker.Mock())
    builder._process = mock_process

    builder.with_process_flow("flow_1", "node_1", "node_2", None)
    builder.with_process_flow("flow_2", "node_2", "node_1", None)

    assert flow_1.source_node == node_1
    assert flow_1.target_node == node_2
    assert flow_2.source_node == node_2
    assert flow_2.target_node == node_1
    assert node_1.out_flows == [flow_1]
    assert node_2.in_flows == [flow_1]
    assert node_2.out_flows == [flow_2]
    assert node_1.in_flows == [flow_2]


def test_build_graph_with_expression_checker(mocker):
    mock_process = mocker.MagicMock()

    class MockNode(Node):
        def __init__(self, id):
            self.id = id
            self.out_flows, self.in_flows = [], []

    node_1, node_2 = MockNode("node_1"), MockNode("node_2")
    flow_1 = mocker.MagicMock(spec=SequenceFlow)
    mock_process.__getitem__.side_effect = lambda key: {
        "flow_1": flow_1,
        "node_1": node_1,
        "node_2": node_2,
    }[key]

    mock_symbol_table = mocker.MagicMock(spec=State)
    mock_type_check = mocker.patch(
        "bpmncwpverify.core.expr.ExpressionListener.type_check",
        return_value=Success("bool"),
    )

    builder = ProcessBuilder(mocker.Mock(), mock_symbol_table)
    builder._process = mock_process

    builder.with_process_flow("flow_1", "node_1", "node_2", "clean_expression")

    mock_type_check.assert_called_once_with("clean_expression", mock_symbol_table)
    assert flow_1.expression == "clean_expression"
