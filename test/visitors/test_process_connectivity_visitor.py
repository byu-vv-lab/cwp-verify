# type: ignore
from bpmncwpverify.builder.process_builder import ProcessBuilder
import pytest
from bpmncwpverify.core.bpmn import Bpmn, EndEvent, StartEvent
from bpmncwpverify.visitors.process_connectivity_visitor import (
    ProcessConnectivityVisitor,
)
import xml.etree.ElementTree as ET


def test_process_connectivity(mocker):
    ns = "{http://www.omg.org/spec/BPMN/20100524/MODEL}"
    root = ET.Element("root")
    process = ET.SubElement(root, f"{ns}process", attrib={"id": "process1"})
    start_event = ET.SubElement(process, f"{ns}startEvent", attrib={"id": "startEvent"})
    start_flow = ET.SubElement(
        process,
        f"{ns}sequenceFlow",
        attrib={"id": "first_flow", "sourceRef": "startEvent", "targetRef": "task0"},
    )
    ET.SubElement(start_event, f"{ns}outgoing").text = start_flow.attrib["id"]

    for j in range(5):
        if j == 4:
            task = ET.SubElement(process, f"{ns}endEvent", attrib={"id": f"task{j}"})
        else:
            task = ET.SubElement(process, f"{ns}task", attrib={"id": f"task{j}"})
        if j < 4:
            flow = ET.SubElement(
                process,
                f"{ns}sequenceFlow",
                attrib={
                    "id": f"flow{j}",
                    "sourceRef": f"task{j}",
                    "targetRef": f"task{j+1}",
                },
            )
            ET.SubElement(task, f"{ns}outgoing").text = flow.attrib["id"]

    task3 = process.find(".//*[@id='task3']")
    cyclic_flow = ET.SubElement(
        process,
        f"{ns}sequenceFlow",
        attrib={"id": "cyclic_flow", "sourceRef": "task3", "targetRef": "task1"},
    )
    ET.SubElement(task3, f"{ns}outgoing").text = cyclic_flow.attrib["id"]

    symbol_table = mocker.Mock()
    bpmn = Bpmn()
    builder = ProcessBuilder(bpmn, process, symbol_table)
    for element in process:
        builder.add_element(element)

    builder._construct_flow_network()

    visitor = ProcessConnectivityVisitor()
    builder._process.accept(visitor)

    assert len(visitor.last_visited_set) == 6
    for flow_id, flow in builder._process._flows.items():
        assert flow.is_leaf if flow_id == "cyclic_flow" else not flow.is_leaf
    assert all(
        task in visitor.last_visited_set
        for task in builder._process.all_items().values()
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

    with pytest.raises(Exception, match="Process graph is not fully connected"):
        visitor.end_visit_process(process)


def test_no_start_or_end_event_raises_exception(setup_process_and_visitor):
    process, visitor, _, _, other_event = setup_process_and_visitor
    # Simulate no StartEvent or EndEvent
    process.all_items.return_value = {"middle": other_event}
    visitor.visited = {other_event}
    other_event.in_msgs = []

    with pytest.raises(Exception, match="Error with end events or start events"):
        visitor.end_visit_process(process)


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

    with pytest.raises(Exception, match="Error with end events or start events"):
        visitor.end_visit_process(process)


def test_no_start_event_with_no_incoming_msgs(setup_process_and_visitor):
    process, visitor, _, end_event, other_event = setup_process_and_visitor
    # Simulate no StartEvent but a valid starting point with incoming messages
    process.all_items.return_value = {"middle": other_event, "end": end_event}
    visitor.visited = {other_event, end_event}
    other_event.in_msgs = []
    end_event.in_msgs = []

    with pytest.raises(Exception, match="Error with end events or start events"):
        visitor.end_visit_process(process)


def test_valid_graph_resets_visited(setup_process_and_visitor):
    process, visitor, start_event, end_event, _ = setup_process_and_visitor
    # Simulate a valid graph
    process.all_items.return_value = {"start": start_event, "end": end_event}
    visitor.visited = {start_event, end_event}
    start_event.in_msgs = []
    end_event.in_msgs = [1]

    visitor.end_visit_process(process)

    # Ensure visited is reset
    assert visitor.visited == set()
