# mypy: ignore-errors
"""#########################################

Class and methods for ingesting an XML .bpmn file and creating a BPMN object

###########################################"""

import xml.etree.ElementTree as ET
import getopt
import sys
import os
import re
from bpmncwpverify.bpmn import BPMN
from bpmncwpverify.state import SymbolTable
from returns.pipeline import is_successful  # type: ignore

bpmn_namespace_map = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}


class BPMNXMLIngestor:
    def __init__(self, symbol_table=None, ns=None) -> None:
        if ns is None:
            self.ns = []
        else:
            self.ns = ns
        self.input_file = ""
        self.stored_elems = {}
        self.generate_stub = False
        self.cond_parser = None  # TODO: put expressions here
        self.symbol_table = symbol_table
        self.root = None

    def create_inline_stub_file(self) -> str:
        file_string = ""
        for process in self.processes:
            for element in process:
                update_state = False
                if "sequenceFlow" not in element.tag:
                    if "task" in element.tag or "Task" in element.tag:
                        name = (
                            self.cleanup_task_name(element.get("name"))
                            if element.get("name") is not None
                            else self.cleanup_name(element.get("id"))
                        )

                        update_state = True
                    else:
                        name = (
                            self.cleanup_name(element.get("name"))
                            if element.get("name") is not None
                            else self.cleanup_name(element.get("id"))
                        )
                    if "parallel" in element.tag:
                        update_state = True
                    file_string += "//{x}\n".format(x=name)
                    file_string = self.write_inline_stub(
                        name, file_string, update_state
                    )
        return file_string

    def write_inline_stub(self, place_name, file_string, update_state=False) -> str:
        file_string += "inline {x}_BehaviorModel(){{\n".format(x=place_name)
        file_string += "\tskip\n"
        file_string += "}\n"
        return file_string

    def parse_xml(self, xml_file) -> ET.ElementTree:
        tree = ET.parse(xml_file)
        return tree

    def parse_input(self, argv) -> None:
        self.input_file = ""
        try:
            opts, args = getopt.getopt(argv, "si:o:", ["stub"])
        except getopt.GetoptError:
            print("BPMNXMLIngestor.py -i <inputFile>")
            sys.exit(2)
        for opt, arg in opts:
            if opt == "-i":
                self.input_file = arg
            if opt == "-o":
                self.output_file = arg

    def execute(self) -> BPMN.Model:
        model = self.process_xml()

        if self.generate_stub:
            self.create_inline_stub_file()

        return model

    def process_xml(self) -> BPMN.Model:
        tree = self.parse_xml(self.input_file)
        self.root = tree.getroot()

        self.collab = self.root.find("bpmn:collaboration", self.ns)

        if self.collab:
            self.participant_map = {
                participant.get("processRef"): participant.get("name")
                for participant in self.collab.findall("bpmn:participant", self.ns)
            }

        self.processes = self.root.findall("bpmn:process", self.ns)

        bpmn_model = BPMN.Model(raw_ingest_ref=tree)
        for process in self.processes:
            bpmn_proc = self._process_proc(process)
            bpmn_model.add_process(bpmn_proc)
        if self.collab:
            for msg in self.collab.findall("bpmn:messageFlow", self.ns):
                raw_id = msg.get("id")
                id = self.cleanup_name(msg.get("id"))
                name = self.cleanup_name(msg.get("name"))
                if name is None:
                    name = id
                message = BPMN.Msg(name, id=raw_id)
                source_ref = msg.get("sourceRef")
                target_ref = msg.get("targetRef")
                from_node = self.stored_elems[source_ref]
                to_node = self.stored_elems[target_ref]
                message.set_to_node(to_node)
                message.set_from_node(from_node)
                from_node.add_out_msg(message)
                to_node.add_in_msg(message)
        return bpmn_model

    def _process_proc(self, process: BPMN.Process) -> BPMN.Process:
        bpmn_proc = BPMN.Process(
            self.cleanup_name(self.participant_map[process.get("id")])
        )
        for element in process:
            if "task" in element.tag.lower():
                name = self.cleanup_task_name(element.get("name"))
            else:
                name = self.cleanup_name(element.get("name"))

            id = self.cleanup_name(element.get("id"))
            raw_id = element.get("id")

            if name is None:
                name = id
            if "startEvent" in element.tag:
                event = BPMN.StartNode(name, id=raw_id)
                bpmn_proc.add_start_state(event)
            elif "sendTask" in element.tag:
                itm = BPMN.MsgIntermediateNode(name, id=raw_id)
            elif "task" in element.tag.lower():
                itm = BPMN.ActivityNode(name, id=raw_id)
            elif "intermediateCatchEvent" in element.tag:
                itm = BPMN.EventNode(name, id=raw_id)
            elif "intermediateThrowEvent" in element.tag:
                itm = BPMN.EventNode(name, id=raw_id)
            elif "businessRuleTask" in element.tag:
                itm = BPMN.ActivityNode(name, id=raw_id)
            elif "exclusiveGateway" in element.tag:
                itm = BPMN.XorGatewayNode(name, id=raw_id)
            elif "parallelGateway" in element.tag:
                if self.has_multiple_out_edges(element):
                    itm = BPMN.ParallelGatewayForkNode(name, id=raw_id)
                else:
                    itm = BPMN.ParallelGatewayJoinNode(name, id=raw_id)
            elif "serviceTask" in element.tag:
                itm = BPMN.ActivityNode(name, id=raw_id)
            elif "endEvent" in element.tag:
                itm = BPMN.EndNode(name, id=raw_id)

            self.stored_elems[id] = itm
        for element in process:
            raw_id = element.get("id")
            name = self.cleanup_flow(element.get("name"))
            id = self.cleanup_flow(element.get("id"))
            if name is None:
                name = id
            if "sequenceFlow" in element.tag:
                source_ref = element.get("sourceRef")
                target_ref = element.get("targetRef")
                from_node = self.stored_elems[source_ref]
                to_node = self.stored_elems[target_ref]

                flow = BPMN.Flow(name, id=raw_id)

                flow.set_to_node(to_node)
                flow.set_from_node(from_node)
                from_node.add_out_flow(flow)
                to_node.add_in_flow(flow)
        return bpmn_proc

    def bpmn_has_multiple_out_edges(self, node):
        if len(node.out_flows) > 1:
            return True
        else:
            return False

    def has_multiple_out_edges(self, element):
        if len(element.findall("bpmn:outgoing", self.ns)) > 1:
            return True
        else:
            return False

    # cleans up flow name (make it Promela compliant)
    def cleanup_flow(self, name):
        # Get rid of newlines in flows
        if name:
            name = name.replace("\n", "")
        return name

    # cleans up a name (make it Promela compliant)
    def cleanup_name(self, name):
        if name is None:
            return name
        # Remove punctuation
        name = re.sub("[?,+=/]", "", name)
        # replace all dashes with spaces
        name = re.sub("[-]", " ", name)
        # Replace all runs of whitespace with a single underscore
        name = re.sub(r"\s+", "_", name)

        return name.strip()

    def cleanup_task_name(self, name):
        if name is None:
            return name
        name = "T" + name.split("-", 1)[0]
        return name.strip()


def main(argv):
    def read_state(state_file):
        with open(state_file) as f:
            return f.read()

    path = os.path.abspath(os.getcwd())
    result = SymbolTable.build(read_state(path + "/src/bpmncwpverify/state.txt"))
    assert is_successful(result)
    symbol_table: SymbolTable = result.unwrap()
    ingestor = BPMNXMLIngestor(symbolTable=symbol_table, ns=bpmn_namespace_map)
    ingestor.parseInput(argv)
    myBPMN = ingestor.execute()
    myBPMN.exportXML("./../../output/XMLOut.bpmn")


if __name__ == "__main__":
    main(sys.argv[1:])
