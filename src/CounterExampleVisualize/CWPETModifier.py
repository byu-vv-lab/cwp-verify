import xml.etree.ElementTree as ET


class CWPETModifier:
    def __init__(self, elementTree: ET.ElementTree):
        self.elementTree = elementTree
        self.root = self.elementTree.getroot()

    def color_active_edges(self, edgeIdList, edgeLabelIdList):
        diagram = self.root.find("diagram")
        mxGraphModel = diagram.find("mxGraphModel")
        root = mxGraphModel.find("root")
        for edgeId in edgeIdList:
            edgeElement = root.find("mxCell[@id='{}']".format(edgeId))
            style = edgeElement.get("style")
            edgeElement.set("style", style + "fillColor=#00ff00;strokeColor=#00ff00;")
        for edgeLabelId in edgeLabelIdList:
            edgeLabelElement = root.find("mxCell[@id='{}']".format(edgeLabelId))
            value = edgeLabelElement.get("value")
            edgeLabelElement.set(
                "value",
                "&lt;font color=&quot;#00FF00&quot;&gt;" + value + "&lt;/font&gt;",
            )

    def color_active_states(self, stateIdList, color):
        if color == "green":
            fillColor = "d5e8d4"
            strokeColor = "82b366"
        elif color == "red":
            fillColor = "f22727"
            strokeColor = "ad0202"
        diagram = self.root.find("diagram")
        mxGraphModel = diagram.find("mxGraphModel")
        root = mxGraphModel.find("root")
        for stateId in stateIdList:
            stateElement = root.find("mxCell[@id='{}']".format(stateId))
            style = stateElement.get("style")
            stateElement.set(
                "style",
                style
                + "fillColor=#{fill};strokeColor=#{stroke};".format(
                    fill=fillColor, stroke=strokeColor
                ),
            )
            value = stateElement.get("value")
            stateElement.set("value", value)

    def add_step_num_annotation(self, stepNum):
        diagram = self.root.find("diagram")
        mxGraphModel = diagram.find("mxGraphModel")
        dy = int(mxGraphModel.get("dy"))
        root = mxGraphModel.find("root")
        myMxCellAttrib = {
            "id": "CFvAYnAbzG3v0uSF8fSO-1",
            "value": "",
            "style": "rounded=0;whiteSpace=wrap;html=1;fillColor=#dae8fc;strokeColor=#6c8ebf;",
            "vertex": "1",
            "parent": "1",
        }
        if stepNum > 99:
            myMxCellAttrib["value"] = "STEP NUMBER {:03d}".format(stepNum)
        elif stepNum > 9:
            myMxCellAttrib["value"] = "STEP NUMBER {:02d}".format(stepNum)
        else:
            myMxCellAttrib["value"] = "STEP NUMBER {:01d}".format(stepNum)

        myMxCell = ET.Element("mxCell", myMxCellAttrib)
        myMxGeometryAttrib = {
            "x": "0",
            "y": "{}".format(dy),
            "width": "140",
            "height": "60",
            "as": "geometry",
        }
        myMxGeometry = ET.Element("mxGeometry", myMxGeometryAttrib)

        myMxCell.append(myMxGeometry)
        root.append(myMxCell)
