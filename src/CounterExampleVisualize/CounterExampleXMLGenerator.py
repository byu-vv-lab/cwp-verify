from CounterExampleParser.CounterExampleParser import CounterExampleParser
from CounterExampleVisualize.BPMNETModifier import BPMNETModifier
from CounterExampleVisualize.CWPETModifier import CWPETModifier
from XMLIngest.CWPXMLIngestor import CWPXMLIngestor
import getopt
import sys
import os
import xml.etree.ElementTree as ET
import numpy as np
from copy import deepcopy


class CounterExampleXMLGenerator:
    def __init__(
        self,
        counterExampleFile="",
        bpmnFile="",
        cwpFile="",
        varList=None,
        premadeBPMN=False,
        premadeCWP=False,
    ):
        self.counterExampleFile = counterExampleFile
        self.bpmnFile = bpmnFile
        self.cwpFile = cwpFile
        self.varList = varList
        self.premadeBPMN = premadeBPMN
        self.premadeCWP = premadeCWP

    def genCounterExampleImages(self):
        myCwpIngestor = CWPXMLIngestor(varList=self.varList)
        myCwpIngestor.inputfile = self.cwpFile
        myCwpIngestor.ingestXML()
        cwpModel = myCwpIngestor.cwp
        # create directory
        # print(os.path.split(self.counterExampleFile))
        path, _ = os.path.split(self.counterExampleFile)
        if not os.path.exists(path):
            os.mkdir(path)
        # parse counterExample into list of IDs
        parser = CounterExampleParser(self.counterExampleFile)
        parser.parseCounterExample()
        steps = parser.steps
        # create new BPMN file for each step in the counterExample
        colors = self.genGreenGradient(steps)
        ids = [step.traversed_ids for step in steps]
        startingIdGroups = [ids[0:i] for i in range(1, len(colors))]
        restIdGroups = [ids[i : i + len(colors)] for i in range(len(ids) + 1 - len(colors))]
        idGroups = startingIdGroups + restIdGroups
        varChanged = [False] * len(steps[0].varMap.values())
        stateChanged = False
        oldVals = list(steps[0].varMap.values())
        oldStates = steps[0].cwp_states
        for idGroup, step in zip(idGroups, steps):
            if self.premadeBPMN:
                bpmnModifier = deepcopy(self.bpmnFile)
            else:
                bpmnModifier = BPMNETModifier(ET.parse(self.bpmnFile))
            if self.premadeCWP:
                cwpModifier = deepcopy(self.cwpFile)
            else:
                cwpModifier = CWPETModifier(ET.parse(self.cwpFile))
            bpmnModifier.addPathColors(idGroup, colors)
            for varOffset, (var, val) in enumerate(step.varMap.items()):
                if val == oldVals[varOffset]:
                    varChanged[varOffset] = False
                else:
                    varChanged[varOffset] = True
                bpmnModifier.createStateVarAnnotation(
                    var, val, varOffset, changed=varChanged[varOffset]
                )
                oldVals[varOffset] = val
            stateChanged = not step.cwp_states == oldStates

            # cwpModifier.color_active_edges(step.edgeIds, step.edgeLabelIds)

            # If there are multiple states, color them red
            if len(step.cwp_states) > 1:
                color = "red"
                step.interesting = True
                step.interestingText = "Mutual Exclusion Violated"
            elif len(step.cwp_states) < 1:
                color = "red"
                step.interesting = True
                step.interestingText = "Universal Inclusion Violated"
            elif len(oldStates) > 1:
                color = "red"
                step.interesting = True
                step.interestingText = "Mutual Exclusion Violated"
            elif len(oldStates) < 1:
                color = "red"
                step.interesting = True
                step.interestingText = "Universal Inclusion Violated"

            # check if we are in the same state as last step. If so, color green
            elif stateChanged is False:
                color = "green"
            # Check if there is an edge between previous state and current state. If there is, color green
            elif cwpModel.isEdgeFrom(oldStates[0], step.cwp_states[0]):
                color = "green"
            # Otherwise, color it red
            else:
                color = "red"
                step.interesting = True
                step.interestingText = "INVALID STATE TRANSITION"

            cwpModifier.color_active_states(step.cwpStateIds, color)
            bpmnModifier.createCWPStateAnnotation(
                step.cwp_states, changed=stateChanged, color=color
            )
            oldStates = step.cwp_states

            if step.interesting:
                bpmnModifier.createInterestingAnnotation(step.interestingText)
            cwpModifier.add_step_num_annotation(step.step_num)
            if len(steps) > 99:
                bpmnModifier.elementTree.write(
                    path + "/step" + "{:03d}".format(step.step_num) + ".bpmn"
                )
                cwpModifier.elementTree.write(
                    path + "/step" + "{:03d}".format(step.step_num) + ".cwp.xml"
                )
            elif len(steps) > 9:
                bpmnModifier.elementTree.write(
                    path + "/step" + "{:02d}".format(step.step_num) + ".bpmn"
                )
                cwpModifier.elementTree.write(
                    path + "/step" + "{:02d}".format(step.step_num) + ".cwp.xml"
                )
            else:
                bpmnModifier.elementTree.write(
                    path + "/step" + "{:01d}".format(step.step_num) + ".bpmn"
                )
                cwpModifier.elementTree.write(
                    path + "/step" + "{:01d}".format(step.step_num) + ".cwp.xml"
                )

    def genRedGradient(self, ids):
        gbcolors = np.linspace(0, 180, 6, dtype="int")
        colors = [
            "#{red}{green}{blue}".format(red="FF", green=format(gb, "02x"), blue=format(gb, "02x"))
            for gb in gbcolors
        ]
        colors.reverse()
        return colors

    def genGreenGradient(self, ids):
        rbcolors = np.linspace(0, 180, 6, dtype="int")
        colors = [
            "#{red}{green}{blue}".format(red=format(rb, "02x"), green="FF", blue=format(rb, "02x"))
            for rb in rbcolors
        ]
        colors.reverse()
        return colors

    def parseInput(self, argv):
        self.inputfile = ""
        try:
            opts, args = getopt.getopt(argv, "c:b:", [])
        except getopt.GetoptError:
            print("CounterExampleBPMNGenerator.py -c <counterExampleFile> -b <BPMNFile>")
            sys.exit(2)
        for opt, arg in opts:
            if opt == "-c":
                self.counterExampleFile = arg
            if opt == "-b":
                self.bpmnFile = arg


def main(argv):
    # gen = CounterExampleBPMNGenerator()
    # gen.parseInput(argv)
    # gen.genCounterExampleImages()
    pass


if __name__ == "__main__":
    main(sys.argv[1:])
