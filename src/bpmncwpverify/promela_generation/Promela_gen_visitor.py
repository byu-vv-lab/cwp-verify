"""
#########################################

Class and methods to generate a workflow model in Promela
using a BPMN object. 

###########################################
"""

from ..bpmn.bpmn_visitor import BPMN_Visitor
from ..bpmn.BPMN import Flow, Msg, EventNode, ActivityNode, Node, StartNode, XorGatewayNode, ParallelGatewayJoinNode, ParallelGatewayForkNode, EndNode, MsgIntermediateNode, TimerIntermediateNode, Model, Process
from ..xml_ingest.BPMNXMLIngestor import BPMNXMLIngestor
import sys

class Promela_gen_visitor(BPMN_Visitor):
    tokenHelpers = """#define hasToken(place) (place != 0)

#define putToken(place) place = 1

#define consumeToken(place) place = 0

"""


    tempHelpers = ''
    def __init__(self, printfOn):
        self.printfOn = printfOn
        self.tempHelpers = self.tempHelpers
        self.helperFuncs = self.tokenHelpers
        self.constantsText = ""
        self.placesText = ""
        self.behaviorModelText = ""
        self.workflowText = ""
        self.initText = ""
        self.constantsIndent = 0
        self.placesIndent = 0
        self.behaviorModelIndent = 0
        self.workflowIndent = 0
        self.initIndent = 0
        self.flowPlaces = []
    
    def genLogCounterExamplePath(self, elementId) -> String:
        ret = ""
        if self.printfOn:
            ret += "\t\t\tprintf(\"###COUNTEREXAMPLE PATH OUTPUT###\\n\")\n"
            ret += "\t\t\tprintf(\"traversed element ID: {x}\\n\")\n".format(x = elementId)
            ret += "\t\t\tlogState()\n"
            ret += "\t\t\tprintf(\"###END OUTPUT###\\n\")\n"
        return ret

    def createOption(self, guard, consumeLocations, behaviorInline, putConditions, putLocations, putFlowIDs, elementID, type="") -> String:
        ret = ":: atomic {{ {x} -> \n".format(x = guard)
        ret += "\t\t{x}\n".format(x = behaviorInline)
        ret += "\t\td_step {\n"
        for location in consumeLocations:
            ret += "\t\t\tconsumeToken({x})\n".format(x = location)
        if "ParallelFALSE" in type:
            ret += "\t\t\tif\n"
            ret += "\t\t\t:: (locked[me]) -> locked[me] = false; unlock()\n"
            ret += "\t\t\t:: (!locked[me]) -> locked[me] = true; lock(me)\n"
            ret += "\t\t\tfi\n"
            
        ret += self.genLogCounterExamplePath(elementID)
        if type == "XOR":
            ret += "\t\t\tif\n"
            for condition, location, id in zip(putConditions, putLocations, putFlowIDs):
                ret += "\t\t\t\t:: {x} -> putToken({y})\n".format(x = condition, y = location)
                ret += self.genLogCounterExamplePath(id)
            ret += "\t\t\tfi\n"
        else:
            for location, id in zip(putLocations, putFlowIDs):
                ret += "\t\t\tputToken({x})\n".format(x = location)
                ret += self.genLogCounterExamplePath(id)
        if "ParallelFALSE" in type:
            ret += "\t\t\tif\n"
            ret += "\t\t\t:: (!locked[me]) -> printf(\"###END PARALLEL GATEWAY###\\n\")\n"
            ret += "\t\t\t:: (locked[me]) -> printf(\"###START PARALLEL GATEWAY###\\n\")\n"
            ret += "\t\t\tfi\n"
        ret += "\t\t}\n"
        ret += "\t}"
        return ret

    def writePlacesLines(self, text):
        self.placesText += ('\t'*self.placesIndent).join(("\n"+text.lstrip()).splitlines(True))

    def writeConstantsLines(self, text):
        self.constantsText += ('\t'*self.constantsIndent).join(("\n"+text.lstrip()).splitlines(True))

    def writeBehaviorModelLines(self, text):
        self.behaviorModelText += ('\t'*self.behaviorModelIndent).join(("\n"+text.lstrip()).splitlines(True))

    def writeInitLines(self, text):
        self.initText += ('\t'*self.initIndent).join(("\n"+text.lstrip()).splitlines(True))
        
    def writeWorkflowLines(self, text):
        self.workflowText += ('\t'*self.workflowIndent).join(("\n"+text.lstrip()).splitlines(True))


    def genXORHasOptionMacro(self, gateway:XorGatewayNode) -> None:
        macro = "#define {}_hasOption \\\n".format(gateway.label)
        conditions = [str(flow.label) for flow in gateway.outFlows]
        macro += "(\\\n\t"
        macro += "||\\\n\t".join(conditions)
        macro += "\\\n)\n"
        self.writeConstantsLines(macro)

    def genActivationOption(self, element:Node, startGuard = "", type = "") -> None:
        guard = "("
        consumeLocations = []
        putLocations = []
        behaviorInline = "skip"
        if type == "XOR":
            putConditions = []
        else:
            putConditions = None
        putFlowIDs = []
        elementID = element.id
        if type == "Task-END":
            consumeLocations.append(self.getLocation(element))
            guard += "hasToken({})".format(self.getLocation(element))
        else:
            for flow in element.inFlows:
                consumeLocations.append(self.getLocation(element, flow))
            if element.inFlows:
                guard += "( "
                if type == "Parallel-join":
                    guard += "&&".join(["hasToken({})".format(self.getLocation(element, loc)) for loc in element.inFlows])
                else:
                    guard += "||".join(["hasToken({})".format(self.getLocation(element, loc)) for loc in element.inFlows])
                guard += " )\n"
        if type != "Task":
            for msg in element.inMsgs:
                consumeLocations.append(self.getLocation(element, msg))
            if element.inMsgs:
                if element.inFlows or type == "Task-END":
                    guard += "&&"
                guard += "( "
                guard += "&&".join(["hasToken({})".format(self.getLocation(element, loc)) for loc in element.inMsgs])
                guard += " )\n"
        if type == "XOR":
            guard += "\t&&"
            guard += "\t({}_hasOption)".format(element.label)
        guard += ")"
        if type != "Task-END":
            behaviorInline = "{x}_BehaviorModel()".format(x = element.label)
        if type == "Task":
            putFlowIDs.append(elementID)
            putLocations.append(self.getLocation(element))
            for msg in element.outMsgs:
                putFlowIDs.append(msg.id)
                putLocations.append(self.getLocation(msg.toNode, msg))
        else:
            for flow in element.outFlows:
                putFlowIDs.append(flow.id)
                putLocations.append(self.getLocation(flow.toNode, flow))
                if type == "XOR":
                    putConditions.append(flow.label)
            if type != "Task-END":
                for msg in element.outMsgs:
                    putFlowIDs.append(msg.id)
                    putLocations.append(self.getLocation(msg.toNode, msg))
        if startGuard:
            guard = startGuard
            consumeLocations.append(self.getLocation(element))
        self.writeWorkflowLines(self.createOption(guard, consumeLocations, behaviorInline, putConditions, putLocations, putFlowIDs, elementID, type))

    def genPlaces(self, element:Node) -> None:
        if not element.inFlows and not element.inMsgs:
            self.flowPlaces.append(self.getLocation(element))
        else:
            for flow in element.inFlows:
                self.flowPlaces.append(self.getLocation(element, flow))
            for msg in element.inMsgs:
                self.flowPlaces.append(self.getLocation(element, msg))
        if isinstance(element, ActivityNode):
            self.flowPlaces.append(self.getLocation(element))

    def visit_node(self, element:Node) -> None:
        if element.seen:
            return
        element.seen = True
        self.genPlaces(element)
        self.genActivationOption(element)
        for flow in element.outFlows:
            flow.accept(self)

    def visit_flow(self, element:Flow) -> None:
        if element.seen:
            return
        element.seen = True
        target = element.toNode
        target.accept(self)

    def visit_msg(self, element:Msg) -> None:
        if element.seen:
            return
        element.seen = True
        self.flowPlaces.append(element.label)

    def visit_event_node(self, element:EventNode) -> None:
        self.visit_node(element)

    def visit_activity_node(self, element:ActivityNode) -> None:
        if element.seen:
            return
        element.seen = True
        self.genPlaces(element)
        self.genActivationOption(element, type="Task")
        self.genActivationOption(element, type="Task-END")
        for flow in element.outFlows:
            flow.accept(self)

    def visit_xor_gateway_node(self, element:XorGatewayNode) -> None:
        if element.seen:
            return
        element.seen = True
        self.genPlaces(element)
        if len(element.outFlows) == 1:
            self.genActivationOption(element, type="XOR-JOIN")
        else:
            self.genXORHasOptionMacro(element)
            self.genActivationOption(element, type="XOR")
        for flow in element.outFlows:
            flow.accept(self)
    
    def visit_parallel_gateway_join_node(self, element: ParallelGatewayJoinNode) -> None:
        if element.seen:
            return
        element.seen = True
        self.genPlaces(element)
        self.genActivationOption(element, type="Parallel-join")
        for flow in element.outFlows:
            flow.accept(self)
    
    def visit_parallel_gateway_fork_node(self, element: ParallelGatewayForkNode) -> None:
        if element.seen:
            return
        element.seen = True
        self.genPlaces(element)
        self.genActivationOption(element, type="Parallel-fork")
        for flow in element.outFlows:
            flow.accept(self)

    def visit_timer_intermediate_node(self, element:TimerIntermediateNode) -> None:
        self.visit_node(element)

    def visit_msg_intermediate_node(self, element:MsgIntermediateNode) -> None:
        self.visit_node(element)
        
    def visit_start_node(self, element:StartNode) -> None:
        if element.seen:
            return
        element.seen = True
        if element.inMsgs:
            self.genPlaces(element)
            self.genActivationOption(element)
        else:
            self.genPlaces(element)
            guard = "(hasToken({}))".format(element.label)
            self.genActivationOption(element, startGuard=guard)
        for flow in element.outFlows:
            flow.accept(self)


    def visit_end_node(self, element:EndNode) -> None:
        if element.seen:
            print("already seen this end node")
            return
        element.seen = True
        self.genPlaces(element)
        self.genActivationOption(element)

    def visit_process(self, element:Process) -> None:
        self.writeWorkflowLines("proctype {x}() {{".format(x = element.name))
        self.workflowIndent += 1
        #self.writeWorkflowLines("updateState()")
        self.writeWorkflowLines("pid me = _pid")
        for startNode in element.startStateList:
            if not startNode.inMsgs:
                self.writeWorkflowLines("putToken({x})".format(x = startNode.label))
        self.writeWorkflowLines("do")
        #self.workflowIndent += 1
        #self.writeWorkflowLines(":: true ->")
        #self.writeWorkflowLines("if")
        #self.writeWorkflowLines(":: (!mutex[me]) -> ")
        #self.workflowIndent += 1
        #self.writeWorkflowLines("if")
        for startNode in element.startStateList:
            startNode.accept(self)
        #self.writeWorkflowLines("fi")
        #self.workflowIndent -= 1
        #self.writeWorkflowLines("fi")
        #self.workflowIndent -= 1
        self.writeWorkflowLines("od")
        self.workflowIndent -= 1
        self.writeWorkflowLines("}")

    def visit_model(self, element:Model) -> None:
        #self.writeConstantsLines("#define NUM_PROCS {}".format(len(element.processList)))
        #self.writeConstantsLines("bool mutex[NUM_PROCS] = false")
        #self.writeConstantsLines("bool locked[NUM_PROCS] = false")
        #mutexUnlockText = "inline unlock(){\n"
        #mutexLockText = "inline lock(proc){\n"
        #for i in range(len(element.processList)):
            #mutexUnlockText += "\tmutex[{}] = 0\n".format(i)
            #mutexLockText += "\tmutex[{}] = 1\n".format(i)
        #mutexLockText += "\tmutex[proc] = 0\n"
        #mutexUnlockText += "}"
        #mutexLockText += "}"
        #self.writeConstantsLines(mutexUnlockText)
        #self.writeConstantsLines(mutexLockText)
        initLines = "init {\n"
        initLines += "\tatomic{\n"
        initLines += "\t\tupdateState()\n"
        for process in element.processList:
            initLines += "\t\trun {}()\n".format(process.name)
        initLines += "\t}\n"
        initLines += "}\n\n"
        self.writeInitLines(initLines)
        for process in element.processList:
            process.accept(self)
        for place in self.flowPlaces:
            self.writePlacesLines("bit {x} = 0".format(x = str(place)))

    def getLocation(self, element, flowOrMsg = None):
        if flowOrMsg:
            return element.label + "_FROM_" + flowOrMsg.fromNode.label
        else:
            if isinstance(element, ActivityNode):
                return element.label + "_END"
            else:
                return element.label
        
    def __repr__(self):
        return self.constantsText + "\n\n" + self.tempHelpers + "\n\n" + self.helperFuncs + "\n\n" + self.placesText + "\n\n" + self.behaviorModelText + "\n\n" + self.initText + "\n\n" + self.workflowText + "\n\n"


def main(argv):
    BPMNNamespaceMap = {'bpmn': "http://www.omg.org/spec/BPMN/20100524/MODEL"}
    ingestor = BPMNXMLIngestor(BPMNNamespaceMap)
    ingestor.parseInput(argv)
    BPMNModel = ingestor.processXML()
    myVisitor = Promela_gen_visitor()
    BPMNModel.accept(myVisitor)
    myVisitor.behaviorModelText = ingestor.createInlineStubFile()
    with open(ingestor.outputfile, 'w+') as f:
        f.write(str(myVisitor))

if __name__ == "__main__":
    main(sys.argv[1:])