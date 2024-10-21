from xml.etree.ElementTree import Element, parse
from bpmncwpverify.bpmn.BPMN import (
    Bpmn,
    Node,
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
from bpmncwpverify.constants import NAMESPACES

TAG_CLASS_MAPPING = {
    "task": Task,
    "startEvent": StartEvent,
    "endEvent": EndEvent,
    "exclusiveGateway": ExclusiveGatewayNode,
    "parallelGateway": ParallelGatewayNode,
}

FLOW_MAPPING = {"sequenceFlow": SequenceFlow}
################


# TODO: Add collaboration logic


def _find_cycles(bpmn: Bpmn) -> None:
    visited = set()

    def detect_cycles(node: Node) -> None:
        visited.add(node)

        for flow in node.out_flows:
            if flow.target_node in visited:
                flow.cycle_flow = True
            elif flow.target_node:
                detect_cycles(flow.target_node)
            else:
                raise Exception("Node is none when it should not be")

    for process in bpmn.processes:
        for start_node in process.get_start_states().values():
            detect_cycles(start_node)


def _build_graph(process: Process) -> None:
    for element_id, element_instance in process.items():
        for outgoing in element_instance.element.findall("bpmn:outgoing", NAMESPACES):
            flow_id = outgoing.text
            if not flow_id:
                raise Exception("flow id is None")
            flow = process.flows.get(flow_id.strip())
            if flow is not None:
                source_ref = flow.element.attrib["sourceRef"]
                target_ref = flow.element.attrib["targetRef"]

                # add target node id to neighbor list of current element
                process.adj_list[element_id].append(target_ref)

                # update flow's source_node
                flow.source_node = process[source_ref]
                # update flow's target_node
                flow.target_node = process[target_ref]

                # update source node's out flows array
                process[source_ref].out_flows.append(flow)
                # update target node's in flows array
                process[target_ref].in_flows.append(flow)


def _traverse_process(process_element: Element) -> Process:
    process = Process(process_element)

    for element in process_element:
        tag_local = element.tag.partition("}")[2]
        if tag_local in TAG_CLASS_MAPPING:
            element_class = TAG_CLASS_MAPPING[tag_local]
            element_instance = element_class(element)
            element_id = element_instance.id
            process[element_id] = element_instance

            process.adj_list[element_id] = []
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
        for element_id, outgoing_ids in process.adj_list.items():
            element_instance = process[element_id]
            name = element_instance.name
            print(f"  Element ID: {element_id}, Name: {name}")
            print("    Outgoing to:")
            for target_id in outgoing_ids:
                target_element = process[target_id]
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

    _find_cycles(bpmn)

    return bpmn
