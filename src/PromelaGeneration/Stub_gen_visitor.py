"""#########################################

Class and methods to generate a workflow model in Promela
using a BPMN object.

###########################################"""

from BPMN_Visitor.BPMN_Visitor import BPMN_visitor
from bpmn.BPMN import (
    Flow,
    Msg,
    EventNode,
    ActivityNode,
    Node,
    StartNode,
    XorGatewayNode,
    ParallelGatewayJoinNode,
    ParallelGatewayForkNode,
    EndNode,
    MsgIntermediateNode,
    TimerIntermediateNode,
    Model,
    Process,
)


class Stub_gen_visitor(BPMN_visitor):
    def __init__(self, varList, modifiesClauses):
        self.behaviorModelText = ""
        self.varList = varList
        self.modifiesClauses = modifiesClauses

    def genBehaviorModel(self, placeName, updateState=False):
        ret = ""
        if updateState:
            varsToModify = self.modifiesClauses.get(placeName, [])
        ret += "//{}\n".format(placeName)
        ret += "inline {x}_BehaviorModel(){{\n".format(x=placeName)
        if updateState:
            for varName in varsToModify:
                var = [var for var in self.varList if var.bpmn == varName][0]
                possibleVals = var.possibleValues
                ret += "\tif\n"
                for val in possibleVals:
                    ret += "\t\t:: true -> {var} = {val}\n".format(var=varName, val=val)
                ret += "\tfi\n"
            ret += "\tupdateState()\n"
        else:
            ret += "\tskip\n"
        ret += "}\n\n"
        return ret

    def visit_node(self, element: Node) -> None:
        if element.seen:
            return
        element.seen = True
        updateState = False
        if isinstance(element, ActivityNode):
            updateState = True
        self.behaviorModelText += self.genBehaviorModel(
            self.getLocation(element), updateState=updateState
        )
        for flow in element.outFlows:
            flow.accept(self)

    def visit_flow(self, element: Flow) -> None:
        if element.seen:
            return
        element.seen = True
        target = element.toNode
        target.accept(self)

    def visit_msg(self, element: Msg) -> None:
        if element.seen:
            return
        element.seen = True
        self.flowPlaces.append(element.label)

    def visit_event_node(self, element: EventNode) -> None:
        self.visit_node(element)

    def visit_activity_node(self, element: ActivityNode) -> None:
        self.visit_node(element)

    def visit_xor_gateway_node(self, element: XorGatewayNode) -> None:
        self.visit_node(element)

    def visit_parallel_gateway_join_node(
        self, element: ParallelGatewayJoinNode
    ) -> None:
        self.visit_node(element)

    def visit_parallel_gateway_fork_node(
        self, element: ParallelGatewayForkNode
    ) -> None:
        self.visit_node(element)

    def visit_timer_intermediate_node(self, element: TimerIntermediateNode) -> None:
        self.visit_node(element)

    def visit_msg_intermediate_node(self, element: MsgIntermediateNode) -> None:
        self.visit_node(element)

    def visit_start_node(self, element: StartNode) -> None:
        self.visit_node(element)

    def visit_end_node(self, element: EndNode) -> None:
        if element.seen:
            return
        self.behaviorModelText += self.genBehaviorModel(
            self.getLocation(element), updateState=False
        )
        element.seen = True

    def visit_process(self, element: Process) -> None:
        for startNode in element.startStateList:
            startNode.accept(self)

    def visit_model(self, element: Model) -> None:
        for process in element.processList:
            process.accept(self)

    def getLocation(self, element, flowOrMsg=None):
        if flowOrMsg:
            return element.label + "_FROM_" + flowOrMsg.fromNode.label
        else:
            return element.label

    def __repr__(self):
        return self.behaviorModelText


if __name__ == "__main__":
    pass
