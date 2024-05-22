"""#########################################

Class and methods for importing a TXT file containing both workflow
and CWP state variables and storing it as a dictionary.

###########################################"""

import re


class StateVar:
    def __init__(self, bpmn, cwp, initValue, type, isConstant, possibleValues=None):
        self.bpmn = bpmn
        self.cwp = cwp
        self.initValue = initValue
        self.type = type
        self.isConstant = isConstant
        if possibleValues:
            self.possibleValues = possibleValues
        else:
            self.possibleValues = []


class VarRange:
    def __init__(self, min, max):
        self.min = min
        self.max = max


class StateIngestor:
    def __init__(self, inputFile):
        self.inputFile = inputFile
        self.varList = []
        self.inputFile = inputFile

    def ingestState(self):
        with open(self.inputFile) as f:
            for line in f:
                splitLine = line.split()
                if not splitLine:
                    continue
                if splitLine[0].lower() == "const":
                    isConstant = True
                    if splitLine[1].lower() == "byte":
                        type = "byte"
                        initVal = splitLine[4]
                    if splitLine[1].lower() == "short":
                        type = "short"
                        initVal = splitLine[4]
                    if splitLine[1].lower() == "int":
                        type = "int"
                        initVal = splitLine[4]
                    if splitLine[1].lower() == "enum":
                        type = "mtype"
                        initVal = ""
                    workflowPart, cwpPart = splitLine[2:4]
                    valsList = None
                else:
                    isConstant = False
                    if splitLine[0].lower() == "byte":
                        type = "byte"
                    if splitLine[0].lower() == "short":
                        type = "short"
                    if splitLine[0].lower() == "int":
                        type = "int"
                    if splitLine[0].lower() == "enum":
                        type = "mtype"
                    if splitLine[0].lower() == "bool":
                        type = "bool"
                    workflowPart, cwpPart, initVal = splitLine[1:4]
                    valsList = self.parsePossibleVals("".join(splitLine[4:]), type)

                var = StateVar(workflowPart, cwpPart, initVal, type, isConstant, valsList)
                self.varList.append(var)

    def parsePossibleVals(self, possibleValsString, type):
        possibleValsList = []
        if type == "mtype":
            return [val.strip() for val in possibleValsString[1:-1].split(",")]
        else:
            rawPossibleValsList = [val.strip() for val in possibleValsString[1:-1].split(",")]
            for val in rawPossibleValsList:
                pattern = r"([0-9]*)-([0-9]*)"
                match = re.search(pattern, val)
                if match:
                    upper = max(int(match.group(1)), int(match.group(2)))
                    lower = min(int(match.group(1)), int(match.group(2)))
                    r = VarRange(lower, upper)
                    possibleValsList.append(r)
                else:
                    possibleValsList.append(val)
        return possibleValsList


if __name__ == "__main__":
    myIngestor = StateIngestor("./../../assets/state.txt")
    myIngestor.ingestState()
    print(myIngestor.varList)
