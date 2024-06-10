import xml.etree.ElementTree as ET


class BPMNETModifier:
    def __init__(self, elementTree: ET.ElementTree):
        self.elementTree = elementTree
        self.ns = {
            "bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL",
            "bpmndi": "http://www.omg.org/spec/BPMN/20100524/DI",
            "dc": "http://www.omg.org/spec/DD/20100524/DC",
            "di": "http://www.omg.org/spec/DD/20100524/DI",
        }
        self.color_changed = "red"
        self.color_unchanged = "green"

    def addPathColors(self, elementIDGroup, colors) -> ET.ElementTree:
        if len(elementIDGroup) < len(colors):
            colors = colors[len(colors) - len(elementIDGroup) :]
        diag = self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns)
        if diag is None:
            raise Exception(
                'ERROR: self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns) is None'
            )
        plane = diag.find("bpmndi:BPMNPlane", self.ns)
        if plane is None:
            raise Exception('ERROR: diag.find("bpmndi:BPMNPlane", self.ns)')
        for elementID, color in zip(elementIDGroup, colors):
            for id in elementID:
                shape = plane.find(
                    "bpmndi:BPMNShape[@bpmnElement='{}']".format(id), self.ns
                )
                line = plane.find(
                    "bpmndi:BPMNEdge[@bpmnElement='{}']".format(id), self.ns
                )
                if shape:
                    shape.set("color:background-color", color)
                if line:
                    line.set("color:border-color", color)
        return self.elementTree

    def createStateVarAnnotation(self, variable, value, varOffset, changed):
        collab = self.elementTree.getroot().find("bpmn:collaboration", self.ns)
        annotationID = "stateVariableAnnotation_{}".format(variable)
        textElement = ET.Element("bpmn:text")
        textElement.text = "{var}: {value}".format(var=variable, value=value)
        textAnnotationElem = ET.Element("bpmn:textAnnotation")
        textAnnotationElem.set("id", annotationID)
        textAnnotationElem.append(textElement)
        collab.append(textAnnotationElem)
        x, y, width, height = self.findVarAssociationLocation(varOffset)

        diag = self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns)
        plane = diag.find("bpmndi:BPMNPlane", self.ns)
        labelElem = ET.Element("bpmndi:BPMNLabel")
        boundsElem = ET.Element("dc:Bounds")
        boundsElem.set("x", x)
        boundsElem.set("y", y)
        boundsElem.set("width", width)
        boundsElem.set("height", height)
        shapeElem = ET.Element("bpmndi:BPMNShape")
        if changed:
            shapeElem.set("color:border-color", "green")
        shapeElem.set("id", "{}_di".format(annotationID))
        shapeElem.set("bpmnElement", "{}".format(annotationID))
        shapeElem.append(boundsElem)
        shapeElem.append(labelElem)
        plane.append(shapeElem)

    def createCWPStateAnnotation(self, cwp_states, changed, color):
        collab = self.elementTree.getroot().find("bpmn:collaboration", self.ns)
        annotationID = "cwpStateAnnotation"
        textElement = ET.Element("bpmn:text")
        textElement.text = "CWP State(s): " + ", ".join(cwp_states)
        textAnnotationElem = ET.Element("bpmn:textAnnotation")
        textAnnotationElem.set("id", annotationID)
        textAnnotationElem.append(textElement)
        collab.append(textAnnotationElem)
        x, y, width, height = self.findStateAssociationLocation(cwp_states=cwp_states)

        diag = self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns)
        plane = diag.find("bpmndi:BPMNPlane", self.ns)
        labelElem = ET.Element("bpmndi:BPMNLabel")
        boundsElem = ET.Element("dc:Bounds")
        boundsElem.set("x", x)
        boundsElem.set("y", y)
        boundsElem.set("width", width)
        boundsElem.set("height", height)
        shapeElem = ET.Element("bpmndi:BPMNShape")
        if changed:
            shapeElem.set("color:border-color", color)
        shapeElem.set("id", "{}_di".format(annotationID))
        shapeElem.set("bpmnElement", "{}".format(annotationID))
        shapeElem.append(boundsElem)
        shapeElem.append(labelElem)
        plane.append(shapeElem)

    def createInterestingAnnotation(self, text):
        collab = self.elementTree.getroot().find("bpmn:collaboration", self.ns)
        annotationID = "interestingAnnotation"
        textElement = ET.Element("bpmn:text")
        textElement.text = text
        textAnnotationElem = ET.Element("bpmn:textAnnotation")
        textAnnotationElem.set("id", annotationID)
        textAnnotationElem.append(textElement)
        collab.append(textAnnotationElem)
        x, y, width, height = self.findInterestingAnnotationLocation()

        diag = self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns)
        plane = diag.find("bpmndi:BPMNPlane", self.ns)
        labelElem = ET.Element("bpmndi:BPMNLabel")
        boundsElem = ET.Element("dc:Bounds")
        boundsElem.set("x", x)
        boundsElem.set("y", y)
        boundsElem.set("width", width)
        boundsElem.set("height", height)
        shapeElem = ET.Element("bpmndi:BPMNShape")
        shapeElem.set("color:border-color", "red")
        shapeElem.set("id", "{}_di".format(annotationID))
        shapeElem.set("bpmnElement", "{}".format(annotationID))
        shapeElem.append(boundsElem)
        shapeElem.append(labelElem)
        plane.append(shapeElem)

    def findStateAssociationLocation(self, cwp_states):
        collab = self.elementTree.getroot().find("bpmn:collaboration", self.ns)
        participant = collab.find("bpmn:participant", self.ns)
        participantID = participant.get("id")
        diag = self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns)
        plane = diag.find("bpmndi:BPMNPlane", self.ns)
        participantDI = plane.find(
            "bpmndi:BPMNShape[@bpmnElement='{}']".format(participantID.strip()), self.ns
        )
        bounds = participantDI.find("dc:Bounds", self.ns)
        participantX = bounds.get("x")
        participantY = bounds.get("y")
        participantWidth = bounds.get("width")
        return (
            str(int(participantX) + int(participantWidth) / 2),
            str(int(participantY) - 25),
            str(100 + ((150) * len(cwp_states))),
            "25",
        )

    def findVarAssociationLocation(self, varOffset):
        collab = self.elementTree.getroot().find("bpmn:collaboration", self.ns)
        participant = collab.find("bpmn:participant", self.ns)
        participantID = participant.get("id")
        diag = self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns)
        plane = diag.find("bpmndi:BPMNPlane", self.ns)
        participantDI = plane.find(
            "bpmndi:BPMNShape[@bpmnElement='{}']".format(participantID.strip()), self.ns
        )
        bounds = participantDI.find("dc:Bounds", self.ns)
        participantX = bounds.get("x")
        participantY = bounds.get("y")
        participantWidth = bounds.get("width")
        return (
            str(int(participantX) + int(participantWidth)),
            str(int(participantY) + 25 * varOffset),
            "200",
            "25",
        )

    def findInterestingAnnotationLocation(self):
        collab = self.elementTree.getroot().find("bpmn:collaboration", self.ns)
        participant = collab.find("bpmn:participant", self.ns)
        participantID = participant.get("id")
        diag = self.elementTree.getroot().find("bpmndi:BPMNDiagram", self.ns)
        plane = diag.find("bpmndi:BPMNPlane", self.ns)
        participantDI = plane.find(
            "bpmndi:BPMNShape[@bpmnElement='{}']".format(participantID.strip()), self.ns
        )
        bounds = participantDI.find("dc:Bounds", self.ns)
        participantX = bounds.get("x")
        participantY = bounds.get("y")
        return str(int(participantX)), str(int(participantY) - 25), "500", "25"
