# type: ignore
import pytest
from bpmncwpverify.builder.bpmn_builder import ConcreteBpmnBuilder
from bpmncwpverify.core.bpmn import Task
from bpmncwpverify.visitors.bpmn_connectivity_visitor import BpmnConnectivityVisitor
import xml.etree.ElementTree as ET


def test_cwp_connectivity(mocker):
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

    builder = ConcreteBpmnBuilder()
    builder.add_process(process, mocker.Mock())
    bpmn = builder.build().unwrap()

    visitor = BpmnConnectivityVisitor()
    bpmn.accept(visitor)

    assert len(visitor.last_visited_set) == 6
    for flow_id, flow in bpmn.processes["process1"]._flows.items():
        assert flow.is_leaf if flow_id == "cyclic_flow" else not flow.is_leaf
    for process in bpmn.processes.values():
        assert all(
            task in visitor.last_visited_set for task in process.all_items().values()
        )


def test_end_bpmn_visit(mocker):
    visitor = BpmnConnectivityVisitor()

    bpmn = mocker.Mock()
    process1 = mocker.Mock()
    process2 = mocker.Mock()
    process3 = mocker.Mock()

    task1 = Task(ET.Element("process1_task", attrib={"id": "process1_task"}))
    task2 = Task(ET.Element("process2_task", attrib={"id": "process2_task"}))
    task3 = Task(ET.Element("process3_task", attrib={"id": "process3_task"}))

    process1.all_items.return_value = {"process1_task": task1}
    process2.all_items.return_value = {"process2_task": task2}
    process3.all_items.return_value = {"process3_task": task3}

    flow1 = mocker.Mock()
    flow2 = mocker.Mock()

    flow1.source_node = task1
    flow1.target_node = task2
    flow2.source_node = task2
    flow2.target_node = task3

    bpmn.processes = {"process1": process1, "process2": process2, "process3": process3}
    bpmn.inter_process_msgs = {"flow1": flow1, "flow2": flow2}

    visitor.end_visit_bpmn(bpmn)
    # should not throw an error


def test_end_visit_bpmn_no_inter_process_messages(mocker):
    visitor = BpmnConnectivityVisitor()

    bpmn = mocker.Mock()
    process1 = mocker.Mock()
    process2 = mocker.Mock()

    task1 = Task(ET.Element("task", attrib={"id": "task1"}))
    task2 = Task(ET.Element("task", attrib={"id": "task2"}))

    process1.all_items.return_value = {"task1": task1}
    process2.all_items.return_value = {"task2": task2}

    bpmn.processes = {"process1": process1, "process2": process2}
    bpmn.inter_process_msgs = {}

    with pytest.raises(
        Exception, match="No inter process messages exist in this bpmn model."
    ):
        visitor.end_visit_bpmn(bpmn)


def test_end_visit_bpmn_single_process(mocker):
    visitor = BpmnConnectivityVisitor()

    bpmn = mocker.Mock()
    process1 = mocker.Mock()

    task1 = Task(ET.Element("task", attrib={"id": "task1"}))
    process1.all_items.return_value = {"task1": task1}

    bpmn.processes = {"process1": process1}
    bpmn.inter_process_msgs = {}  # No inter-process messages required for a single process

    visitor.end_visit_bpmn(bpmn)  # Should not raise an exception
