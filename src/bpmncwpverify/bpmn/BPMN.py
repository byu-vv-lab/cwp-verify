from typing import Optional, List
from abc import ABC, abstractmethod
import xml.etree.ElementTree as ET


class BPMN_Visitor(ABC):
    @abstractmethod
    def visit_process(self, element: "Process") -> None:
        pass

    @abstractmethod
    def visit_flow(self, element: "Flow") -> None:
        pass

    @abstractmethod
    def visit_msg(self, element: "Msg") -> None:
        pass

    @abstractmethod
    def visit_activity_node(self, element: "ActivityNode") -> None:
        pass

    @abstractmethod
    def visit_start_node(self, element: "StartNode") -> None:
        pass

    @abstractmethod
    def visit_xor_gateway_node(self, element: "XorGatewayNode") -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway_join_node(
        self, element: "ParallelGatewayJoinNode"
    ) -> None:
        pass

    @abstractmethod
    def visit_gateway_node(self, element: "GatewayNode") -> None:
        pass

    @abstractmethod
    def visit_parallel_gateway_fork_node(
        self, element: "ParallelGatewayForkNode"
    ) -> None:
        pass

    @abstractmethod
    def visit_end_node(self, element: "EndNode") -> None:
        pass

    @abstractmethod
    def visit_event_node(self, element: "EventNode") -> None:
        pass

    @abstractmethod
    def visit_msg_intermediate_node(self, element: "MsgIntermediateNode") -> None:
        pass

    @abstractmethod
    def visit_timer_intermediate_node(self, element: "TimerIntermediateNode") -> None:
        pass

    @abstractmethod
    def visit_model(self, element: "Model") -> None:
        pass


# Class representing a label
class Label:
    def __init__(self, text: str):
        self.text = text

    def __repr__(self) -> str:
        return self.text


# Class representing a flow
class Flow:
    def __init__(
        self,
        label: str,
        toNode: Optional["Node"] = None,
        fromNode: Optional["Node"] = None,
        id: Optional[str] = None,
    ):
        self.label = label
        self.toNode = toNode
        self.fromNode = fromNode
        self.id = id
        self.seen = False  # Used in traversal

    def setToNode(self, toNode: "Node") -> None:
        self.toNode = toNode

    def setFromNode(self, fromNode: "Node") -> None:
        self.fromNode = fromNode

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_flow(self)


# Class representing a message
class Msg:
    def __init__(
        self,
        label: str,
        toNode: Optional["Node"] = None,
        fromNode: Optional["Node"] = None,
        id: Optional[str] = None,
    ):
        self.label = label
        self.toNode = toNode
        self.fromNode = fromNode
        self.id = id
        self.seen = False  # Used in traversal

    def setToNode(self, toNode: "Node") -> None:
        self.toNode = toNode

    def setFromNode(self, fromNode: "Node") -> None:
        self.fromNode = fromNode

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_msg(self)


# Class representing a generic node
class Node:
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
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

    def setOutFlows(self, outFlows: List[Flow]) -> None:
        self.outFlows = outFlows

    def addOutFlow(self, flow: Flow) -> None:
        self.outFlows.append(flow)

    def addOutMsg(self, msg: Msg) -> None:
        self.outMsgs.append(msg)

    def addInFlow(self, flow: Flow) -> None:
        self.inFlows.append(flow)

    def addInMsg(self, msg: Msg) -> None:
        self.inMsgs.append(msg)

    def accept(self, visitor: BPMN_Visitor) -> None:
        pass

    def __repr__(self) -> str:
        return "Name: %s \n\tInFlows: %s \n\tOutFlows: %s\n\tID: %s" % (
            str(self.label),
            str(self.inFlows),
            str(self.outFlows),
            str(self.id),
        )


# Class representing an event node
class EventNode(Node):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_event_node(self)


# Class representing an activity node
class ActivityNode(Node):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_activity_node(self)


# Class representing a start node
class StartNode(Node):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_start_node(self)


# Class representing a gateway node
class GatewayNode(Node):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_gateway_node(self)


# Class representing an XOR gateway node
class XorGatewayNode(GatewayNode):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_xor_gateway_node(self)


# Class representing a parallel gateway join node
class ParallelGatewayJoinNode(GatewayNode):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_parallel_gateway_join_node(self)


# Class representing a parallel gateway fork node
class ParallelGatewayForkNode(GatewayNode):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_parallel_gateway_fork_node(self)


# Class representing an end node
class EndNode(Node):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_end_node(self)


# Abstract class representing an intermediate node
class IntermediateNode(Node, ABC):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)


# Class representing a message intermediate node
class MsgIntermediateNode(IntermediateNode):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_msg_intermediate_node(self)


# Class representing a timer intermediate node
class TimerIntermediateNode(IntermediateNode):
    def __init__(
        self,
        label: Label = Label("Empty"),
        inFlows: Optional[List[Flow]] = None,
        outFlows: Optional[List[Flow]] = None,
        inMsgs: Optional[List[Msg]] = None,
        outMsgs: Optional[List[Msg]] = None,
        id: Optional[str] = None,
    ):
        super().__init__(label, inFlows, outFlows, inMsgs, outMsgs, id)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_timer_intermediate_node(self)


# Class representing a process
class Process:
    def __init__(self, name: str, startStateList: Optional[List[StartNode]] = None):
        if startStateList is None:
            self.startStateList = []
        else:
            self.startStateList = startStateList
        self.name = name

    def addStartState(self, startState: StartNode) -> None:
        self.startStateList.append(startState)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_process(self)


# Class representing a model
class Model:
    def __init__(
        self,
        processList: Optional[List[Process]] = None,
        rawIngestRef: Optional[ET.ElementTree] = None,
    ):
        if processList is None:
            self.processList = []
        else:
            self.processList = processList
        self.rawIngestRef = rawIngestRef

    def addProcess(self, process: Process) -> None:
        self.processList.append(process)

    def accept(self, visitor: BPMN_Visitor) -> None:
        visitor.visit_model(self)

    def exportXML(self, outputFile: str) -> None:
        if isinstance(self.rawIngestRef, ET.ElementTree):
            self.rawIngestRef.write(outputFile, encoding="UTF-8", xml_declaration=True)


if __name__ == "__main__":
    pass
