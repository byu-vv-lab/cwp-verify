"""#########################################

Class and methods for importing a CSV export of a CWP diagram.
Stores the information as a CWP object

###########################################"""

import getopt
import sys
import pandas as pd
import re
from CWP.CWP import CWP, CWPEdge, CWPState


class CSVIngestor:
    def __init__(self):
        self.storedElems = {}
        self.cwp = CWP()
        self.curEdgeLetter = "A"
        self.inputfile = ""

    def ingestCSV(self):
        pd_data = pd.read_csv(self.inputfile)
        for ind in pd_data.index:
            if pd_data["Name"][ind] in ["Text", "Process"]:
                state = CWPState(self.cleanup_name(pd_data["Text Area 1"][ind]))
                self.cwp.addState(state)
                self.storedElems[pd_data["Id"][ind]] = state
        for ind in pd_data.index:
            if pd_data["Name"][ind] in ["Line"]:
                if (
                    pd_data["Line Source"][ind] in self.storedElems
                    and pd_data["Line Destination"][ind] in self.storedElems
                ):
                    name = self.genEdgeName()
                    label = self.cleanup_line_label(pd_data["Text Area 1"][ind])
                    edge = CWPEdge(label=label, name=name)
                    source = self.storedElems[pd_data["Line Source"][ind]]
                    source.addOutEdge(edge)
                    dest = self.storedElems[pd_data["Line Destination"][ind]]
                    dest.addInEdge(edge)
                    edge.setSource(source)
                    edge.setDest(dest)
                    self.cwp.addEdge(edge)

        self.cwp.calcEndStates()

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

    def cleanup_line_label(self, label):
        if label:
            label = label.encode("ASCII", "ignore")
            label = label.decode()
        return label

    def genEdgeName(self):
        ret = "Edge" + self.curEdgeLetter
        self.curEdgeLetter = chr(ord(self.curEdgeLetter) + 1)
        return ret

    def parseInput(self, argv):
        self.inputfile = ""
        try:
            opts, _ = getopt.getopt(argv, "i:")
        except getopt.GetoptError:
            print("CSVIngestor.py -i <inputFile>")
            sys.exit(2)
        for opt, arg in opts:
            if opt == "-i":
                self.inputfile = arg


def main(argv):
    ingestor = CSVIngestor()
    ingestor.parseInput(argv)
    ingestor.ingestCSV()


if __name__ == "__main__":
    main(sys.argv[1:])
