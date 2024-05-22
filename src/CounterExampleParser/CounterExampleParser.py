import re
import getopt
import sys


class CounterExampleStep:
    def __init__(
        self, step_num, traversed_ids, cwp_states, cwpStateIds, varMap, edgeIds, edgeLabelIds
    ):
        self.step_num = step_num
        self.traversed_ids = traversed_ids
        self.cwp_states = cwp_states
        self.cwpStateIds = cwpStateIds
        self.varMap = varMap
        self.edgeIds = edgeIds
        self.edgeLabelIds = edgeLabelIds
        self.interesting = False
        self.interestingText = ""

    def set_interesting(self):
        self.interesting = True


class CounterExampleParser:
    def __init__(self, inputFile=""):
        self.inputFile = inputFile
        self.START_STR = "COUNTEREXAMPLE PATH OUTPUT"
        self.END_STR = "END OUTPUT"
        self.TRAVERSED_PREFIX = "traversed element ID:"
        self.NVR = "Never claim moves"
        self.START_PARALLEL_STR = "START PARALLEL GATEWAY"
        self.END_PARALLEL_STR = "END PARALLEL GATEWAY"
        self.steps = []

    def parseCounterExample(self):
        with open(self.inputFile) as f:
            matches = re.findall(
                "(?<={start}).*?(?={end})|{never}|{parallelStart}|{parallelEnd}".format(
                    start=self.START_STR,
                    end=self.END_STR,
                    never=self.NVR,
                    parallelStart=self.START_PARALLEL_STR,
                    parallelEnd=self.END_PARALLEL_STR,
                ),
                f.read(),
                re.S | re.I,
            )
            stepNum = 0
            parallelStepCount = 0
            inParallel = False
            for match in matches:
                states = []
                stateIds = []
                varMap = {}
                edgeIds = []
                edgeLabelIds = []
                traversed_id = None
                if self.START_PARALLEL_STR in match:
                    inParallel = True
                    parallelStepCount = 0
                    continue
                if self.END_PARALLEL_STR in match:
                    inParallel = False
                    combinedStep = self.combineSteps(
                        self.steps[stepNum - parallelStepCount : stepNum]
                    )
                    self.steps = self.steps[: stepNum - parallelStepCount] + [combinedStep]
                    stepNum = combinedStep.step_num + 1
                    continue
                if self.NVR in match:
                    if stepNum > 1:
                        self.steps[stepNum - 2].set_interesting()
                        self.steps[stepNum - 2].interestingText = "POSSIBLE MOMENT OF INTEREST"
                    if stepNum > 0:
                        self.steps[stepNum - 1].set_interesting()
                        self.steps[stepNum - 1].interestingText = "POSSIBLE MOMENT OF INTEREST"
                    continue
                for line in match.splitlines():
                    if self.TRAVERSED_PREFIX in line:
                        traversed_id = self.grabTraversedId(line)
                    elif "**STATE" in line:
                        stateName, stateId = self.grabCWPState(line)
                        states.append(stateName)
                        stateIds.append(stateId)
                    elif "**VAR" in line:
                        variable, value = self.grabVariable(line)
                        varMap[variable] = value
                    elif "**EDGE" in line:
                        id, labelId, val = self.grabEdgeIdVal(line)
                        if val == "1":
                            edgeIds.append(id)
                            edgeLabelIds.append(labelId)
                self.steps.append(
                    CounterExampleStep(
                        stepNum, [traversed_id], states, stateIds, varMap, edgeIds, edgeLabelIds
                    )
                )
                stepNum += 1
                if inParallel:
                    parallelStepCount += 1

    def combineSteps(self, steps) -> CounterExampleStep:
        newStepNum = steps[0].step_num
        newtraversedIDs = [id for step in steps for id in step.traversed_ids]
        newStates = steps[-1].cwp_states
        newStateIds = steps[-1].cwpStateIds
        newVarMap = steps[-1].varMap
        newEdgeIds = steps[-1].edgeIds
        newEdgeLabelIds = steps[-1].edgeLabelIds
        newStep = CounterExampleStep(
            newStepNum,
            newtraversedIDs,
            newStates,
            newStateIds,
            newVarMap,
            newEdgeIds,
            newEdgeLabelIds,
        )
        return newStep

    def grabEdgeIdVal(self, str):
        match = re.search("(?<=\*\*EDGE )(.*)(\(.*\)) = (.*)", str, re.I)
        if match:
            return match.group(1).strip(), match.group(2).strip()[1:-1], match.group(3).strip()
        else:
            return None, None, None

    def grabTraversedId(self, str):
        id = re.search("(?<={}).*".format(self.TRAVERSED_PREFIX), str, re.I)
        if id:
            return id.group(0).strip()

    def grabCWPState(self, str):
        state = re.search("(?<=\*\*STATE )(.*)(\(.*\))", str, re.I)
        if state:
            return state.group(1).strip(), state.group(2).strip()[1:-1]
        else:
            return None, None

    def grabVariable(self, str):
        match = re.search("(?<=\*\*VAR )(.*) = (.*)", str, re.I)
        if match:
            return match.group(1).strip(), match.group(2).strip()
        else:
            return None, None

    def parseInput(self, argv):
        self.inputfile = ""
        try:
            opts, args = getopt.getopt(argv, "i:", [])
        except getopt.GetoptError:
            print("BPMNXMLIngestor.py -i <inputFile>")
            sys.exit(2)
        for opt, arg in opts:
            if opt == "-i":
                self.inputFile = arg


if __name__ == "__main__":
    myparser = CounterExampleParser()
    myparser.parseInput(sys.argv[1:])
    myparser.parseCounterExample()
    print(myparser.traversed_ids)
