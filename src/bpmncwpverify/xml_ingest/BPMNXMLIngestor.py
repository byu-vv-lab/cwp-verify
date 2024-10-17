from ..bpmn.BPMN import Bpmn
from defusedxml.ElementTree import parse
from xml.etree.ElementTree import ElementTree, Element
from ..constants import NAMESPACES


def _traverse_tasks(process: Element, bpmn: Bpmn) -> None:
    for task in process.findall("bpmn:task", NAMESPACES):
        task_id = task.attrib.get("id")
        task_name = task.attrib.get("name")
        print(f"  Task ID: {task_id}, Task Name: {task_name}")


def _traverse_xml(root: ElementTree, bpmn: Bpmn) -> None:
    processes = root.findall("bpmn:process", NAMESPACES)

    for process in processes:
        # get process id
        _traverse_tasks(process, bpmn)


def get_bpmn_from_xml(xml_file: str) -> Bpmn:
    tree = parse(xml_file)

    root = tree.getroot()
    bpmn = Bpmn()

    _traverse_xml(root, bpmn)

    return Bpmn()
