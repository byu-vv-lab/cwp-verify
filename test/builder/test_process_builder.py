# type: ignore
from xml.etree.ElementTree import Element
from bpmncwpverify.builder.process_builder import ProcessBuilder
from bpmncwpverify.core.bpmn import Node, SequenceFlow
from bpmncwpverify.core.state import SymbolTable
from returns.result import Success


def test_add_element(mocker):
    mock_element = Element("{test}task")
    mock_bpmn = mocker.Mock()
    mock_task = mocker.MagicMock()
    mock_task.id = "1"

    mock_class = mocker.patch("bpmncwpverify.core.bpmn.Task", return_value=mock_task)
    mocker.patch.dict(
        "bpmncwpverify.builder.process_builder.ProcessBuilder._TAG_CLASS_MAPPING",
        {"task": mock_class},
    )

    builder = ProcessBuilder(mock_bpmn, mocker.MagicMock(), mocker.MagicMock())

    mock_process = mocker.MagicMock()
    builder._process = mock_process

    builder.add_element(mock_element)

    mock_process.__setitem__.assert_called_once_with("1", mock_task)
    mock_bpmn.store_element.assert_called_once_with(mock_task)


def test_build_graph(mocker):
    mock_process = mocker.MagicMock()
    mock_bpmn = mocker.MagicMock()

    class MockFlow(SequenceFlow):
        def __init__(self, element, source_node=None, target_node=None):
            self.element = element
            self.source_node = source_node
            self.target_node = target_node

    class MockNode(Node):
        def __init__(self, id):
            self.id = id
            self.out_flows = []
            self.in_flows = []

        def add_out_flow(self, flow):
            self.out_flows.append(flow)

        def add_in_flow(self, flow):
            self.in_flows.append(flow)

    mock_element_1 = mocker.MagicMock()
    mock_element_1.element.findall.return_value = [mocker.MagicMock(text="flow_1")]
    mock_element_2 = mocker.MagicMock()
    mock_element_2.element.findall.return_value = [mocker.MagicMock(text="flow_2")]

    mock_process.all_items.return_value = {
        "node_1": mock_element_1,
        "node_2": mock_element_2,
    }

    flow_1 = MockFlow(
        element=mocker.MagicMock(attrib={"sourceRef": "node_1", "targetRef": "node_2"})
    )
    flow_2 = MockFlow(
        element=mocker.MagicMock(attrib={"sourceRef": "node_2", "targetRef": "node_1"})
    )
    mock_process.__getitem__.side_effect = lambda key: {
        "flow_1": flow_1,
        "flow_2": flow_2,
    }[key.strip()]

    node_1 = MockNode(id="node_1")
    node_2 = MockNode(id="node_2")
    mock_bpmn.get_element_from_id_mapping.side_effect = lambda id: {
        "node_1": node_1,
        "node_2": node_2,
    }[id]

    builder = ProcessBuilder(mocker.Mock(), mocker.Mock(), mocker.Mock())
    builder._bpmn = mock_bpmn
    builder._process = mock_process
    builder._construct_flow_network()

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
    mock_bpmn = mocker.MagicMock()

    class MockFlow(SequenceFlow):
        def __init__(self, element, source_node=None, target_node=None, name=None):
            self.element = element
            self.expression = name
            self.source_node = source_node
            self.target_node = target_node

    class MockNode(Node):
        def __init__(self, id):
            self.id = id
            self.out_flows = []
            self.in_flows = []

        def add_out_flow(self, flow):
            self.out_flows.append(flow)

        def add_in_flow(self, flow):
            self.in_flows.append(flow)

    mock_element_1 = mocker.MagicMock()
    mock_element_1.element.findall.return_value = [mocker.MagicMock(text="flow_1")]
    mock_element_2 = mocker.MagicMock()
    mock_element_2.element.findall.return_value = []

    mock_process.all_items.return_value = {
        "node_1": mock_element_1,
        "node_2": mock_element_2,
    }

    flow_1 = MockFlow(
        element=mocker.MagicMock(
            attrib={
                "sourceRef": "node_1",
                "targetRef": "node_2",
                "name": "clean_expression",
            }
        )
    )
    mock_process.__getitem__.side_effect = lambda key: {
        "flow_1": flow_1,
    }[key.strip()]

    node_1 = MockNode(id="node_1")
    node_2 = MockNode(id="node_2")
    mock_bpmn.get_element_from_id_mapping.side_effect = lambda id: {
        "node_1": node_1,
        "node_2": node_2,
    }[id]

    mock_symbol_table = mocker.MagicMock(spec=SymbolTable)
    mock_build = mocker.patch(
        "bpmncwpverify.core.expr.ExpressionListener.type_check",
        return_value=Success("bool"),
    )

    builder = ProcessBuilder(mocker.Mock(), mocker.Mock(), mock_symbol_table)
    builder._bpmn = mock_bpmn
    builder._process = mock_process
    builder._construct_flow_network()

    mock_build.assert_called_once_with("clean_expression", mock_symbol_table)
    assert flow_1.expression == "clean_expression"
