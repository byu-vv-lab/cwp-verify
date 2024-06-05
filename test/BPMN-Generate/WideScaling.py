import BPMN.BPMN as bpmn
import pickle
import os
import getopt
import sys
import xml.etree.ElementTree as ET
from textwrap import dedent


class WideScaling:
    def __init__(self, numActors=5, outputFile=None):
        self.numActors = numActors
        self.curActor = 1
        self.assetDir = "./../../assets/examples/wideScaling{}".format(self.numActors)
        self.cwpStubFile = "./../../assets/stubs/scalingCWPstub.xml"
        if outputFile is None:
            self.outputFile = "{}/workflow.pickle".format(self.assetDir)
        else:
            self.outputFile = outputFile
        self.bpmnModel = bpmn.Model()
        if not os.path.exists(self.assetDir):
            os.makedirs(self.assetDir)

    def genFiles(self):
        self.genWorkflowFile()
        self.genModifiesFile()
        self.genStateFile()
        self.genCWPFile()
        self.genBehaviorModelsFile()

    def genWorkflowFile(self):
        for _ in range(self.numActors):
            self.addActor()
        self.pickle_model()

    def genModifiesFile(self):
        modifiesFile = "{}/modifies.txt".format(self.assetDir)
        with open(modifiesFile, "w+") as f:
            for i in range(self.numActors):
                taskNum = ((i + 1) * 2) - 1
                f.write("T{:02d} semaphore\n".format(taskNum))
                taskNum = taskNum + 1
                finNum = i + 1
                f.write("T{:02d} fin{}\n".format(taskNum, finNum))

    def genStateFile(self):
        stateFile = "{}/state.txt".format(self.assetDir)
        with open(stateFile, "w+") as f:
            f.write("const enum True True\n")
            f.write("const enum False False\n")
            f.write("const enum INIT INIT\n")
            for i in range(self.numActors):
                actNum = i + 1
                f.write("const enum act{} act{}\n".format(actNum, actNum))
            actList = ["act{}".format(i) for i in range(1, self.numActors + 1)]
            f.write(
                "enum semaphore semaphore INIT [INIT, {}]\n".format(", ".join(actList))
            )
            for i in range(self.numActors):
                finNum = i + 1
                f.write("enum fin{} fin{} False [True, False]\n".format(finNum, finNum))

    def genCWPFile(self):
        cwpFile = "{}/cwp.xml".format(self.assetDir)
        tree = ET.parse(self.cwpStubFile)
        root = tree.getroot()
        edge = root.find(".//*[@id='TGB-_AdT9mRaeSGGOheL-6']")
        condList = ["fin{} == True".format(i) for i in range(1, self.numActors + 1)]
        conditionString = "&&".join(condList)
        edge.set("value", conditionString)
        tree.write(cwpFile)

    def genBehaviorModelsFile(self):
        behaviorModelsFile = "{}/behaviorModels.pml".format(self.assetDir)
        with open(behaviorModelsFile, "w+") as f:
            for i in range(1, self.numActors + 1):
                task1 = "T{:02d}".format(i * 2 - 1)
                task2 = "T{:02d}".format(i * 2)
                start = "start{}".format(i)
                gateway = "gateway{}".format(i)
                end = "end{}".format(i)
                f.write(
                    dedent(
                        """\
                //{start}
                inline {start}_BehaviorModel(){{
                    skip
                }}

                //{task1}
                inline {task1}_BehaviorModel(){{
                    semaphore = act{i}
                    updateState()
                }}

                //{gateway}
                inline {gateway}_BehaviorModel(){{
                    skip
                }}

                //{task2}
                inline {task2}_BehaviorModel(){{
                    fin{i} = True
                    updateState()
                }}

                //{end}
                inline {end}_BehaviorModel(){{
                    skip
                }}

                """.format(
                            i=i,
                            start=start,
                            task1=task1,
                            gateway=gateway,
                            task2=task2,
                            end=end,
                        )
                    )
                )

    def addActor(self):
        name = "Actor{}".format(self.curActor)
        startState = bpmn.StartNode("start{}".format(self.curActor))
        task1 = bpmn.ActivityNode("T{:02d}".format(self.curActor * 2 - 1))
        task2 = bpmn.ActivityNode("T{:02d}".format(self.curActor * 2))
        gateway = bpmn.XorGatewayNode("gateway{}".format(self.curActor))
        end = bpmn.EndNode("end{}".format(self.curActor))

        edge1 = bpmn.Flow(
            label="flow-{}-1".format(self.curActor), fromNode=startState, toNode=task1
        )
        edge2 = bpmn.Flow(
            label="flow-{}-2".format(self.curActor), fromNode=task1, toNode=gateway
        )
        edge3 = bpmn.Flow(
            label="semaphore!=act{}".format(self.curActor),
            fromNode=gateway,
            toNode=task1,
        )
        edge4 = bpmn.Flow(
            label="semaphore==act{}".format(self.curActor),
            fromNode=gateway,
            toNode=task2,
        )
        edge5 = bpmn.Flow(
            label="flow-{}-3".format(self.curActor), fromNode=task2, toNode=end
        )

        startState.addOutFlow(edge1)
        task1.addInFlow(edge1)
        task1.addOutFlow(edge2)
        task1.addInFlow(edge3)
        gateway.addInFlow(edge2)
        gateway.addOutFlow(edge3)
        gateway.addOutFlow(edge4)
        task2.addInFlow(edge4)
        task2.addOutFlow(edge5)
        end.addInFlow(edge5)

        proc = bpmn.Process(name, [startState])
        self.bpmnModel.addProcess(proc)
        self.curActor += 1

    def pickle_model(self):
        with open(self.outputFile, "wb+") as f:
            pickle.dump(self.bpmnModel, f)


def parse(argv):
    try:
        opts, args = getopt.getopt(argv, "n", ["numActors="])
    except getopt.GetoptError:
        print("WideScaling.py <List of number of actors>")
        sys.exit(2)
    numActorsList = args
    return numActorsList


def main(argv):
    numActorsList = parse(argv)
    for numActors in numActorsList:
        wideScaling = WideScaling(int(numActors))
        wideScaling.genFiles()


if __name__ == "__main__":
    main(sys.argv[1:])
