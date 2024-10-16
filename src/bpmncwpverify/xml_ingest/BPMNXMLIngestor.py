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

BPMNNamespaceMap = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}


class BPMNXMLIngestor:
    def __init__(self, symbolTable=None, ns=None) -> None:
        if ns is None:
            self.ns = []
        else:
            self.ns = ns
        self.inputfile = ""
        self.storedElems = {}
        self.generateStub = False
        self.condParser = None  # TODO: put expressions here
        self.symbolTable = symbolTable
        # self.condParser.setVarList(self.varList)
        self.root = None

    def createInlineStubFile(self) -> str:
        fileString = ""
        for process in self.processes:
            for element in process:
                updateState = False
                if "sequenceFlow" not in element.tag:
                    if "task" in element.tag or "Task" in element.tag:
                        name = (
                            self.cleanup_task_name(element.get("name"))
                            if element.get("name") is not None
                            else self.cleanup_name(element.get("id"))
                        )

                        updateState = True
                    else:
                        name = (
                            self.cleanup_name(element.get("name"))
                            if element.get("name") is not None
                            else self.cleanup_name(element.get("id"))
                        )
                    if "parallel" in element.tag:
                        updateState = True
                    fileString += "//{x}\n".format(x=name)
                    fileString = self.writeInlineStub(name, fileString, updateState)
        return fileString

    def writeInlineStub(self, placeName, fileString, updateState=False) -> str:
        fileString += "inline {x}_BehaviorModel(){{\n".format(x=placeName)
        fileString += "\tskip\n"
        fileString += "}\n"
        return fileString

    def parseXML(self, xmlFile) -> ET.ElementTree:
        tree = ET.parse(xmlFile)
        return tree

    def parseInput(self, argv) -> None:
        self.inputfile = ""
        try:
            opts, args = getopt.getopt(argv, "si:o:", ["stub"])
        except getopt.GetoptError:
            print("BPMNXMLIngestor.py -i <inputFile>")
            sys.exit(2)
        for opt, arg in opts:
            if opt == "-i":
                self.inputfile = arg
            if opt == "-o":
                self.outputfile = arg

    def execute(self) -> BPMN.Model:
        model = self.processXML()

        if self.generateStub:
            self.createInlineStubFile()

        return model

    def processXML(self) -> BPMN.Model:
        tree = self.parseXML(self.inputfile)
        self.root = tree.getroot()

        self.collab = self.root.find("bpmn:collaboration", self.ns)

        if self.collab:
            self.participantMap = {
                participant.get("processRef"): participant.get("name")
                for participant in self.collab.findall("bpmn:participant", self.ns)
            }

        self.processes = self.root.findall("bpmn:process", self.ns)

        BPMNmodel = BPMN.Model(rawIngestRef=tree)
        for process in self.processes:
            BPMNproc = self.processProc(process)
            BPMNmodel.addProcess(BPMNproc)
        if self.collab:
            for msg in self.collab.findall("bpmn:messageFlow", self.ns):
                raw_id = msg.get("id")
                id = self.cleanup_name(msg.get("id"))
                name = self.cleanup_name(msg.get("name"))
                if name is None:
                    name = id
                message = BPMN.Msg(name, id=raw_id)
                sourceRef = msg.get("sourceRef")
                targetRef = msg.get("targetRef")
                fromNode = self.storedElems[sourceRef]
                toNode = self.storedElems[targetRef]
                message.setToNode(toNode)
                message.setFromNode(fromNode)
                fromNode.addOutMsg(message)
                toNode.addInMsg(message)
        return BPMNmodel

    def _processProc(self, process: BPMN.Process) -> BPMN.Process:
        BPMNproc = BPMN.Process(
            self.cleanup_name(self.participantMap[process.get("id")])
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
                BPMNproc.addStartState(event)
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
                if self.hasMultipleOutEdges(element):
                    itm = BPMN.ParallelGatewayForkNode(name, id=raw_id)
                else:
                    itm = BPMN.ParallelGatewayJoinNode(name, id=raw_id)
            elif "serviceTask" in element.tag:
                itm = BPMN.ActivityNode(name, id=raw_id)
            elif "endEvent" in element.tag:
                itm = BPMN.EndNode(name, id=raw_id)

            self.storedElems[id] = itm
        for element in process:
            raw_id = element.get("id")
            name = self.cleanup_flow(element.get("name"))
            id = self.cleanup_flow(element.get("id"))
            if name is None:
                name = id
            if "sequenceFlow" in element.tag:
                sourceRef = element.get("sourceRef")
                targetRef = element.get("targetRef")
                fromNode = self.storedElems[sourceRef]
                toNode = self.storedElems[targetRef]

                # TODO: follow this logic but with new expression parser
                # if isinstance(
                #     fromNode, BPMN.XorGatewayNode
                # ) and self.BPMNhasMultipleOutEdges(fromNode):
                #     # root = self.condParser.execute(name)
                #     # newroot = TreeNode(value="()", type=TokenType.PAREN, left=root)
                #     # flow = BPMN.Flow(newroot, id=raw_id)
                #     pass
                # else:
                # flow = BPMN.Flow(name, id=raw_id)

                flow = BPMN.Flow(name, id=raw_id)

                flow.setToNode(toNode)
                flow.setFromNode(fromNode)
                fromNode.addOutFlow(flow)
                toNode.addInFlow(flow)
        return BPMNproc

    def BPMNhasMultipleOutEdges(self, node):
        if len(node.outFlows) > 1:
            return True
        else:
            return False

    def hasMultipleOutEdges(self, element):
        if len(element.findall("bpmn:outgoing", self.ns)) > 1:
            return True
        else:
            return False

    # cleans up flow name (make it Promela Compliant)
    def cleanup_flow(self, name):
        # Get rid of newlines in flows
        if name:
            name = name.replace("\n", "")
        return name

    # cleans up a name (make is Promela Compliant)
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
    ingestor = BPMNXMLIngestor(symbolTable=symbol_table, ns=BPMNNamespaceMap)
    ingestor.parseInput(argv)
    myBPMN = ingestor.execute()
    myBPMN.exportXML("./../../output/XMLOut.bpmn")


if __name__ == "__main__":
    main(sys.argv[1:])
