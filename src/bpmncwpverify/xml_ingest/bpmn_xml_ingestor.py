from xml.etree.ElementTree import Element, parse
from bpmncwpverify.bpmn.BPMN import (
    Bpmn,
    Task,
    StartEvent,
    EndEvent,
    ExclusiveGatewayNode,
    ParallelGatewayNode,
    SequenceFlow,
    Process,
)


################
# Constants
################
NAMESPACES = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}

TAG_CLASS_MAPPING = {
    "task": Task,
    "startEvent": StartEvent,
    "endEvent": EndEvent,
    "exclusiveGateway": ExclusiveGatewayNode,
    "parallelGateway": ParallelGatewayNode,
}

FLOW_MAPPING = {"sequenceFlow": SequenceFlow}
################


def _build_graph(process: Process) -> None:
    for element_id, element_instance in process.elements.items():
        for outgoing in element_instance.element.findall("bpmn:outgoing", NAMESPACES):
            flow_id = outgoing.text
            if not flow_id:
                raise Exception("flow id is None")
            flow = process.flows.get(flow_id.strip())
            if flow is not None:
                target_ref = flow.element.attrib["targetRef"]
                process.graph[element_id].append(target_ref)


def _traverse_process(process_element: Element) -> Process:
    process = Process(process_element)

    for element in process_element:
        tag_local = element.tag.partition("}")[2]
        if tag_local in TAG_CLASS_MAPPING:
            element_class = TAG_CLASS_MAPPING[tag_local]
            element_instance = element_class(element)
            element_id = element_instance.id
            process.elements[element_id] = element_instance

            process.graph[element_id] = []
        elif tag_local in FLOW_MAPPING:
            flow_id = element.attrib["id"]
            element_class = FLOW_MAPPING[tag_local]
            element_instance = element_class(element)
            process.flows[flow_id] = element_instance

    _build_graph(process)

    return process


def _print_bpmn(bpmn: Bpmn) -> None:
    for process in bpmn.processes:
        print(f"Process ID: {process.id}, Name: {process.name}")
        for element_id, outgoing_ids in process.graph.items():
            element_instance = process.elements[element_id]
            name = element_instance.name
            print(f"  Element ID: {element_id}, Name: {name}")
            print("    Outgoing to:")
            for target_id in outgoing_ids:
                target_element = process.elements.get(target_id)
                target_name = target_element.name if target_element else "Unknown"
                print(f"      Element ID: {target_id}, Name: {target_name}")
        print()


def get_bpmn_from_xml(xml_file: str) -> Bpmn:
    tree = parse(xml_file)
    root = tree.getroot()
    bpmn = Bpmn()
    processes = root.findall("bpmn:process", NAMESPACES)
    for process_element in processes:
        process = _traverse_process(process_element)
        bpmn.processes.append(process)

    return bpmn
