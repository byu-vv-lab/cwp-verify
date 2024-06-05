import xml.etree.ElementTree as ET
import re
from ExpressionParse.ExpressionParser import ExpressionParser
from CWP.CWP import CWP, CWPEdge, CWPState


class CWPXMLIngestor:
    def __init__(self, varList=None, ns=None):
        self.storedElems = {}
        self.cwp = CWP()
        self.curEdgeLetter = "A"
        self.inputfile = ""
        self.root = None
        self.condParser = ExpressionParser()
        if varList:
            self.varList = varList
            self.CWPLang = [var.cwp for var in self.varList]
        else:
            self.varList = []
            self.CWPLang = []
        self.condParser.setVarList(self.varList)
        self.root = None

    def ingestXML(self) -> CWP:
        tree = self.parseXML(self.inputfile)
        self.root = tree.getroot()
        self.diagram = self.root.find("diagram")
        if self.diagram is None:
            raise Exception("ERROR: self.diagram is None")
        self.mxGraphModel = self.diagram.find("mxGraphModel")
        if self.mxGraphModel is None:
            raise Exception("ERROR: self.mxGraphModel is None")
        self.mxRoot = self.mxGraphModel.find("root")
        if self.mxRoot is None:
            raise Exception("ERROR: self.mxRoot is None")
        mxCells = self.mxRoot.findall("mxCell")
        for mxCell in mxCells:
            if mxCell is None:
                raise Exception("ERROR: self.mxCells is None")
            tmp = mxCell.get("style")
            if tmp is None:
                raise Exception('ERROR: mxCell.get("style") is None')
            if mxCell.get("vertex") and "edgeLabel" not in tmp:
                name = self.cleanup_name(mxCell.get("value"))
                state = CWPState(name, mxCell.get("id"))
                self.cwp.addState(state)
                self.storedElems[mxCell.get("id")] = state
        for mxCell in mxCells:
            if mxCell.get("edge"):
                sourceRef = mxCell.get("source")
                targetRef = mxCell.get("target")
                id = mxCell.get("id")
                name = self.genEdgeName()
                edge = CWPEdge(
                    "",
                    name,
                    id,
                )
                if sourceRef:
                    source = self.storedElems[sourceRef]
                    source.addOutEdge(edge)
                    edge.setSource(source)
                dest = self.storedElems[targetRef]
                dest.addInEdge(edge)
                edge.setDest(dest)
                self.storedElems[id] = edge
                self.cwp.addEdge(edge)
        for mxCell in mxCells:
            tmp = mxCell.get("style")
            if tmp is None:
                raise Exception('ERROR: mxCell.get("style") is None')
            if mxCell.get("style") and "edgeLabel" in tmp:
                edge = self.storedElems[mxCell.get("parent")]
                edge.label = self.cleanup_line_label(mxCell.get("value"))
                self.condParser.execute(edge.label)
                edge.labelIdRef = mxCell.get("id")

        self.cwp.calcEndStates()

    def parseXML(self, xmlFile) -> ET.ElementTree:
        tree = ET.parse(xmlFile)
        return tree

    def cleanup_line_label(self, label):
        if label:
            label = label.encode("ASCII", "ignore")
            label = label.decode()

        # Fix div error
        label = re.sub("<div>", "", label)
        label = re.sub("</div>", "", label)
        # Fix br error
        label = re.sub("<br>", " ", label)
        label = re.sub("</br>", "", label)
        # Fix LT
        label = re.sub("&lt;", "<", label)
        # Fix GT
        label = re.sub("&gt;", ">", label)
        # Fix AMP
        label = re.sub("&amp;", "&", label)

        return label

    def genEdgeName(self):
        ret = "Edge" + self.curEdgeLetter
        self.curEdgeLetter = chr(ord(self.curEdgeLetter) + 1)
        return ret

    def cleanup_name(self, name):
        if name is None:
            return name
        # Remove punctuation
        name = re.sub("[?,+=/]", "", name)
        # replace all dashes with spaces
        name = re.sub("[-]", " ", name)
        # Replace all runs of whitespace with a single underscore
        name = re.sub(r"\s+", "_", name)
        # Fix div error
        name = re.sub("<div>", "", name)
        name = re.sub("</div>", "", name)
        return name.strip()
