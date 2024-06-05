import xml.etree.ElementTree as ET
import random
import string
import getopt
import sys
import os
from textwrap import dedent


class LongScaling:
    def __init__(self, stubFile=None, numLoops=5):
        self.ns = {
            "bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL",
            "bpmndi": "http://www.omg.org/spec/BPMN/20100524/DI",
            "dc": "http://www.omg.org/spec/DD/20100524/DC",
            "di": "http://www.omg.org/spec/DD/20100524/DI",
        }
        stubFile = stubFile
        if not stubFile:
            stubFile = "./../../assets/stubs/longScalingStub.bpmn"
        self.assetDir = "./../../assets/examples/longScaling{}".format(numLoops)

        if not os.path.exists(self.assetDir):
            os.makedirs(self.assetDir)
        self.cwpStubFile = "./../../assets/stubs/scalingCWPstub.xml"
        self.elementTree = ET.parse(stubFile)
        self.root = self.elementTree.getroot()
        self.process = self.root.find("bpmn:process", self.ns)
        self.curloopNum = 2
        self.numLoops = numLoops
        self.lastGateway = self.process.find(
            "bpmn:exclusiveGateway[@name='GATEWAY1']", self.ns
        )
        self.finalTask = self.process.find("bpmn:task[@name='999-FINAL']", self.ns)

    def genFiles(self):
        self.genWorkflowFile()
        self.genModifiesFile()
        self.genStateFile()
        self.genCWPFile()
        self.genBehaviorModelsFile()

    def genWorkflowFile(self):
        workflowFile = "{}/workflow.bpmn".format(self.assetDir)
        for _ in range(self.numLoops - 1):
            self.addLoop()
        self.finalize()
        self.elementTree.write(workflowFile)

    def genModifiesFile(self):
        modifiesFile = "{}/modifies.txt".format(self.assetDir)
        with open(modifiesFile, "w+") as f:
            for i in range(1, self.numLoops + 1):
                f.write("T{:02d} var{}\n".format(i, i))

    def genStateFile(self):
        stateFile = "{}/state.txt".format(self.assetDir)
        with open(stateFile, "w+") as f:
            f.write("const enum True True\n")
            f.write("const enum False False\n")
            f.write("const enum INIT INIT\n")
            for i in range(1, self.numLoops + 1):
                f.write("enum var{} var{} INIT [INIT, True, False]\n".format(i, i))

    def genCWPFile(self):
        cwpFile = "{}/cwp.xml".format(self.assetDir)
        tree = ET.parse(self.cwpStubFile)
        root = tree.getroot()
        edge = root.find(".//*[@id='TGB-_AdT9mRaeSGGOheL-6']")
        condList = ["var{} == True".format(i) for i in range(1, self.numLoops + 1)]
        conditionString = "&&".join(condList)
        edge.set("value", conditionString)
        tree.write(cwpFile)

    def genBehaviorModelsFile(self):
        behaviorModelsFile = "{}/behaviorModels.pml".format(self.assetDir)
        with open(behaviorModelsFile, "w+") as f:
            f.write(
                dedent(
                    """\
                //START
                inline START_BehaviorModel(){
                    skip
                }
                """
                )
            )
            for i in range(1, self.numLoops + 1):
                task = "T{:02d}".format(i)
                gateway = "GATEWAY{}".format(i)
                f.write(
                    dedent(
                        """\
                //{task}
                inline {task}_BehaviorModel(){{
                    if
                        :: true -> var{i} = True
                        :: true -> var{i} = False
                    fi
                    updateState()
                }}

                //{gateway}
                inline {gateway}_BehaviorModel(){{
                    skip
                }}

                """.format(i=i, task=task, gateway=gateway)
                    )
                )
            f.write(
                dedent(
                    """\
                //T999
                inline T999_BehaviorModel(){
                    updateState()
                }
                //END
                inline END_BehaviorModel(){
                    skip
                }
                """
                )
            )

    def addLoop(self):
        taskId = "Activity_" + self.gen_id()
        task = ET.Element(
            "ns0:task",
            {"id": taskId, "name": "{:02d}-MIDDLE ACTIVITY".format(self.curloopNum)},
        )
        gatewayId = "Gateway_" + self.gen_id()
        gateway = ET.Element(
            "ns0:exclusiveGateway",
            {"id": gatewayId, "name": "GATEWAY{}".format(self.curloopNum)},
        )
        flowId1 = "Flow_" + self.gen_id()
        incoming1 = ET.Element("ns0:incoming")
        incoming1.text = flowId1
        outgoing1 = ET.Element("ns0:incoming")
        outgoing1.text = flowId1
        flow1 = ET.Element(
            "ns0:sequenceFlow",
            {
                "id": flowId1,
                "name": "var{}==True".format(self.curloopNum - 1),
                "sourceRef": self.lastGateway.get("id"),
                "targetRef": taskId,
            },
        )
        flowId2 = "Flow_" + self.gen_id()
        incoming2 = ET.Element("ns0:incoming")
        incoming2.text = flowId2
        outgoing2 = ET.Element("ns0:incoming")
        outgoing2.text = flowId2
        flow2 = ET.Element(
            "ns0:sequenceFlow",
            {"id": flowId2, "sourceRef": taskId, "targetRef": gatewayId},
        )
        flowId3 = "Flow_" + self.gen_id()
        incoming3 = ET.Element("ns0:incoming")
        incoming3.text = flowId3
        outgoing3 = ET.Element("ns0:incoming")
        outgoing3.text = flowId3
        flow3 = ET.Element(
            "ns0:sequenceFlow",
            {
                "id": flowId3,
                "name": "var{}==False".format(self.curloopNum),
                "sourceRef": gatewayId,
                "targetRef": taskId,
            },
        )

        self.lastGateway.append(outgoing1)
        self.lastGateway = gateway
        task.append(incoming1)
        task.append(outgoing2)
        task.append(incoming3)

        gateway.append(incoming2)
        gateway.append(outgoing3)

        self.process.append(task)
        self.process.append(gateway)
        self.process.append(flow1)
        self.process.append(flow2)
        self.process.append(flow3)
        self.curloopNum += 1

    def gen_id(self):
        return "".join(
            random.choice(string.ascii_lowercase + string.digits) for _ in range(7)
        )

    def finalize(self):
        flowId = "Flow_" + self.gen_id()
        flow = ET.Element(
            "ns0:sequenceFlow",
            {
                "id": flowId,
                "name": "var{}==True".format(self.curloopNum - 1),
                "sourceRef": self.lastGateway.get("id"),
                "targetRef": self.finalTask.get("id"),
            },
        )
        outgoing = ET.Element("ns0:outgoing")
        outgoing.text = flowId
        incoming = ET.Element("ns0:incoming")
        incoming.text = flowId
        self.lastGateway.append(outgoing)
        self.finalTask.append(incoming)
        self.process.append(flow)


def parse(argv):
    try:
        opts, args = getopt.getopt(argv, "n", ["numLoops="])
    except getopt.GetoptError:
        print("WideScaling.py <List of number of loops>")
        sys.exit(2)
    numLoopsList = args
    return numLoopsList


def main(argv):
    numLoopsList = parse(argv)
    for numLoops in numLoopsList:
        longscaling = LongScaling(numLoops=int(numLoops))
        longscaling.genFiles()


if __name__ == "__main__":
    main(sys.argv[1:])
