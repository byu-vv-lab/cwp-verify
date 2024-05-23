from abc import ABC
import xml.etree.ElementTree as ET


# Class representing a label
class Label:
    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return self.text


# Class representing a conditional label
class CondLabel:
    def __init__(self, expTree):
        self.root = expTree

    def __repr__(self):
        return str(self.root)


# Class representing a flow
class Flow:
    def __init__(self, label, toNode=None, fromNode=None, id=None):
        self.label = label
        self.toNode = toNode
        self.fromNode = fromNode
        self.id = id
        self.seen = False  # Used in traversal

    def setToNode(self, toNode):
        self.toNode = toNode

    def setFromNode(self, fromNode):
        self.fromNode = fromNode

    def __repr__(self):
        return "Label: %s | Destination: %s\n" % (str(self.label), self.toNode.label)

    def accept(self, visitor):
        visitor.visit_flow(self)


# Class representing a message
class Msg:
    def __init__(self, label, fromNode=None, toNode=None, id=None):
        self.label = label
        self.fromNode = fromNode
        self.toNode = toNode
        self.id = id
        self.seen = False  # Used in traversal

    def setToNode(self, toNode):
        self.toNode = toNode

    def setFromNode(self, fromNode):
        self.fromNode = fromNode

    def __repr__(self):
        return "Label: %s | Destination: %s\n" % (self.label, self.toNode.label)

    def accept(self, visitor):
        visitor.visit_msg(self)


# Class representing a generic node
class Node:
    def __init__(
        self,
        label=Label("Empty"),
        inFlows=None,
        outFlows=None,
        inMsgs=None,
        outMsgs=None,
        id=None,
    ):
        if inFlows is None:
            self.inFlows = []
        else:
            self.inFlows = inFlows
        if outFlows is None:
            self.outFlows = []
        else:
            self.outFlows = outFlows
        if inMsgs is None:
            self.inMsgs = []
        else:
            self.inMsgs = inMsgs
        if outMsgs is None:
            self.outMsgs = []
        else:
            self.outMsgs = outMsgs
        self.label = label
        self.seen = False  # Used in traversal
        self.id = id

    def setOutFlows(self, outFlows):
        self.outFlows = outFlows

    def addOutFlow(self, flow):
        self.outFlows.append(flow)

    def addOutMsg(self, msg):
        self.outMsgs.append(msg)

    def addInFlow(self, flow):
        self.inFlows.append(flow)

    def addInMsg(self, msg):
        self.inMsgs.append(msg)

    def __repr__(self):
        return "Name: %s \n\tInFlows: %s \n\tOutFlows: %s\n\tID: %s" % (
            str(self.label),
            str(self.inFlows),
            str(self.outFlows),
            str(self.id),
        )


# Class representing an event node
class EventNode(Node):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_event_node(self)


# Class representing an activity node
class ActivityNode(Node):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_activity_node(self)


# Class representing a start node
class StartNode(Node):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_start_node(self)


# Class representing a gateway node
class gatewayNode(Node):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_gateway_node(self)


# Class representing an XOR gateway node
class XorGatewayNode(gatewayNode):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_xor_gateway_node(self)


# Class representing a parallel gateway join node
class ParallelGatewayJoinNode(gatewayNode):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_parallel_gateway_join_node(self)


# Class representing a parallel gateway fork node
class ParallelGatewayForkNode(gatewayNode):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_parallel_gateway_fork_node(self)


# Class representing an end node
class EndNode(Node):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_end_node(self)


# Abstract class representing an intermediate node
class IntermediateNode(Node, ABC):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)


# Class representing a message intermediate node
class MsgIntermediateNode(IntermediateNode):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_msg_intermediate_node(self)


# Class representing a timer intermediate node
class TimerIntermediateNode(IntermediateNode):
    def __init__(
        self, label, inFlows=None, outFlows=None, inMsgs=None, outMsgs=None, id=None
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor):
        visitor.visit_timer_intermediate_node(self)


# Class representing a process
class Process:
    def __init__(self, name, startStateList=None):
        if startStateList is None:
            self.startStateList = []
        else:
            self.startStateList = startStateList
        self.name = name

    def addStartState(self, startState):
        self.startStateList.append(startState)

    def accept(self, visitor):
        visitor.visit_process(self)

    def __repr__(self):
        ret = self.name
        ret += "\n"
        for startState in self.startStateList:
            ret += str(startState)
            ret += "\n"
        return ret


# Class representing a model
class Model:
    def __init__(self, processList=None, rawIngestRef=None):
        if processList is None:
            self.processList = []
        else:
            self.processList = processList
        self.rawIngestRef = rawIngestRef

    def addProcess(self, process):
        self.processList.append(process)

    def accept(self, visitor):
        visitor.visit_model(self)

    def exportXML(self, outputFile):
        if isinstance(self.rawIngestRef, ET.ElementTree):
            self.rawIngestRef.write(outputFile, encoding="UTF-8", xml_declaration=True)
        else:
            return

    def __repr__(self):
        ret = ""
        for process in self.processList:
            ret += str(process)
            ret += "\n"
        return ret


if __name__ == "__main__":
    pass
