"""#########################################

Class and methods to generate LTL properties,
helper function, and macros from a CWP object

###########################################"""

from CWP.CWP import CWP, CWPState


class LTLGenerator:
    def __init__(self, cwp: CWP = None, varList=None, debug=False, printfOn=False):
        self.cwp = cwp
        self.output_str = ""
        self.tab = 0
        self.output_file = ""
        self.debug = debug
        self.printfOn = printfOn
        if varList:
            self.varList = varList
            self.cwpVocabList = [var.cwp for var in varList]
        else:
            self.varList = []
            self.cwpVocabList = []
        self.propertyList: list[str] = []

    def generate_all(self):
        self.generate_helper_functions()
        self.generate_LTL()

    def generate_helper_functions(self):
        self.writeLine("")
        self.writeLine("")
        self.writeVarDecl()
        self.writeLine("")
        self.writeLine("")
        self.writeVariableRangeInvariants()
        self.writeLine("")
        self.writeLine("")
        self.writeInitStates()
        self.writeLine("")
        self.writeLine("")
        self.writeEdgeDefinitions()
        self.writeLine("")
        self.writeLine("")
        self.writeUpdateState()
        self.writeLine("")
        self.writeLine("")
        if self.printfOn:
            self.writeLogStateInline()
            self.writeLine("")
            self.writeLine("")

    def generate_LTL(self):
        self.writeGlobalProperties()
        self.writeLine("")
        self.writeLine("")
        for state in self.cwp.states:
            self.writeStateProperties(state)
            self.writeLine("")
            self.writeLine("")
        self.writeLine("")
        self.writeLine("")
        self.writeLine("")

    def writeVarDecl(self):
        self.writeLine("//**********VARIABLE DECLARATION************//")
        for var in self.varList:
            if var.type == "mtype" and var.isConstant:
                self.writeLine(
                    "{type} = {{{name}}}".format(type=var.type, name=var.bpmn)
                )
            else:
                self.writeLine(
                    "{type} {name} = {initial}".format(
                        type=var.type, name=var.bpmn, initial=var.initValue
                    )
                )

    def writeInitStates(self):
        self.writeLine("//**********STATE VARIABLE DECLARATION************//")
        for state in self.cwp.states:
            if "init" in state.name.lower():
                self.writeLine("bit {name} = 1".format(name=state.name))
            else:
                self.writeLine("bit {name} = 0".format(name=state.name))

    def writeEdgeDefinitions(self):
        self.writeLine("//**********EDGE DECLARATION************//")
        for edge in self.cwp.edges:
            self.writeLine("bit {name} = 0".format(name=edge.name))

    def writeUpdateState(self):
        self.writeLine("//**********UPDATE STATE INLINE************//")
        self.writeLine("inline updateState() {")
        self.tab += 1
        self.writeLine("d_step {")
        self.tab += 1
        # self.writeLine("if")
        # self.writeLine(":: (!locked[_pid]) ->")
        # self.tab += 1
        self.writeRefreshEdges()
        self.writeRefreshStates()
        self.writeVariableRangeAssertions()
        # self.tab -= 1
        # self.writeLine(":: else -> skip")
        # self.writeLine("fi")
        self.tab -= 1
        self.writeLine("}")
        self.tab -= 1
        self.writeLine("}")

    def writeVariableRangeInvariants(self):
        self.writeLine("//**********Variable Range Invariants************//")
        for var in self.varList:
            if var.isConstant:
                continue
            else:
                cwp = var.cwp
                invariant = "("
                for value in var.possibleValues:
                    if isinstance(value, int) or isinstance(value, str):
                        invariant += "({cwp} == {value}) || ".format(
                            cwp=cwp, value=value
                        )
                    else:
                        valRange = value
                        invariant += "({cwp} >= {min} && {cwp} <= {max}) || ".format(
                            cwp=cwp, min=valRange.min, max=valRange.max
                        )

                invariant = invariant[:-4]
                invariant += ")"
                self.writeLine("#define {}Invariant {}".format(cwp, invariant))

    def writeVariableRangeAssertions(self):
        for var in self.varList:
            if var.isConstant:
                continue
            else:
                self.writeLine("assert({cwp}Invariant)".format(cwp=var.cwp))

    def writeRefreshEdges(self):
        for edge in self.cwp.edges:
            self.writeLine("if")
            self.writeLine(":: ({}) -> ".format(edge.label))
            self.tab += 1
            self.writeLine("{} = 1".format(edge.name))
            self.tab -= 1
            self.writeLine(":: else -> ")
            self.tab += 1
            self.writeLine("{} = 0".format(edge.name))
            self.tab -= 1
            self.writeLine("fi")

    def writeRefreshStates(self):
        for state in self.cwp.states:
            self.writeLine("{} = ".format(state.name))
            self.tab += 1
            self.writeLine("(")
            self.tab += 1

            # USE ONE OF THE FOLLOWING TWO

            # Conjunction of incoming
            if state.inEdges:
                self.writeLine(
                    "(" + " && ".join([edge.name for edge in state.inEdges]) + ")"
                )

            # Disjunction of incoming
            # self.writeLine("(" + " || ".join(state.inEdges) + ")")

            # Conjuncted with
            if state.inEdges and state.outEdges:
                self.writeLine("&&")

            # Negated Disjunction of outgoing
            if state.outEdges:
                self.writeLine(
                    "(! (" + " || ".join([edge.name for edge in state.outEdges]) + "))"
                )

            self.tab -= 1
            self.writeLine(")")
            self.tab -= 1

    def writeGlobalProperties(self):
        self.writeLine("//**********GLOBAL PROPERTIES************//")
        self.writeInaStateProperty()
        self.writeFairProperty()

    def writeInaStateProperty(self):
        self.propertyList.append("alwaysInAState")
        self.writeLine(
            "#define inAState "
            + " \\\n || ".join([state.name for state in self.cwp.states])
        )
        self.writeLine("ltl alwaysInAState {(always (inAState))}")

    def writeFairProperty(self):
        self.propertyList.append("fairPathExists")
        if self.debug:
            self.writeLine("#define fair (true)")
        else:
            self.writeLine(
                "#define fair (eventually ("
                + " || ".join([state.name for state in self.cwp.endStates])
                + "))"
            )
        self.writeLine("ltl fairPathExists {(always (! fair))}")

    def writeStateProperties(self, state: CWPState):
        self.writeLine(
            "//**********{} STATE PROPERTIES************//".format(state.name)
        )
        self.writeExistsProperty(state)
        self.writeMutexProperty(state)
        self.writeEdgesProperty(state)

    def writeExistsProperty(self, state: CWPState):
        self.propertyList.append("{}Exists".format(state.name))
        self.writeLine(
            "ltl {name}Exists {{(fair implies (always (! {name})))}}".format(
                name=state.name
            )
        )

    def writeMutexProperty(self, state: CWPState):
        self.propertyList.append("{}Mutex".format(state.name))
        self.writeLine("ltl {}Mutex {{".format(state.name))
        self.tab += 1
        self.writeLine("(")
        self.tab += 1
        self.writeLine("always (")
        self.tab += 1
        self.writeLine("{} implies (".format(state.name))
        self.tab += 1
        self.writeLine("{}".format(state.name))
        joinString = (")\n" + "\t" * self.tab) + "&& (! "
        self.writeLine(
            "&& (! "
            + joinString.join([x.name for x in self.cwp.states if x is not state])
            + ")"
        )
        self.tab -= 1
        self.writeLine(")")
        self.tab -= 1
        self.writeLine(")")
        self.tab -= 1
        self.writeLine(")")
        self.tab -= 1
        self.writeLine("}")

    def writeLogStateInline(self):
        if self.printfOn:
            self.writeLine("//**********LOG STATE************//")
        else:
            self.writeLine("//***********LOG STATE FILLER*******//")

        self.writeLine("inline logState(){")
        self.tab += 1

        if self.printfOn:
            self.writeLine('printf("******************************\\n")')
        else:
            self.writeLine("skip")

        for state in self.cwp.states:
            self.writeLogState(state)
        for edge in self.cwp.edges:
            self.writeLogEdge(edge)
        for var in self.varList:
            if not var.isConstant:
                self.writeLogVar(var)
        if self.printfOn:
            self.writeLine('printf("******************************\\n")')
        else:
            self.writeLine("skip")
        self.tab -= 1
        self.writeLine("}")

    def writeLogVar(self, var):
        if self.printfOn:
            self.writeLine('printf("**VAR {bpmn} = ")'.format(bpmn=var.bpmn))
            self.writeLine("printm({})".format(var.bpmn))
            self.writeLine('printf("\\n")')
        else:
            self.writeLine("skip")
            self.writeLine("skip")
            self.writeLine("skip")

    def writeLogState(self, state):
        self.writeLine("if")
        self.writeLine(":: ({}) -> ".format(state.name))
        self.tab += 1
        if self.printfOn:
            self.writeLine(
                'printf("**STATE {name}({id})\\n")'.format(
                    name=state.name, id=state.idRef
                )
            )
        else:
            self.writeLine("skip")
        self.tab -= 1
        self.writeLine(":: else -> skip")
        self.writeLine("fi")

    def writeLogEdge(self, edge):
        if self.printfOn:
            self.writeLine(
                'printf("**EDGE {id}({labelId}) = %d\\n", {name})'.format(
                    id=edge.idRef, labelId=edge.labelIdRef, name=edge.name
                )
            )
        else:
            self.writeLine("skip")

    def writeEdgesProperty(self, state: CWPState):
        self.propertyList.append("{}Edges".format(state.name))
        outStates = [edge.dest for edge in state.outEdges]
        self.writeLine("ltl {}Edges {{".format(state.name))
        self.tab += 1
        self.writeLine("(")
        self.tab += 1
        self.writeLine("fair implies (")
        self.tab += 1
        self.writeLine("always (")
        self.tab += 1
        self.writeLine("{} implies (".format(state.name))
        self.tab += 1
        if outStates:
            self.writeLine("{} until (".format(state.name))
            self.tab += 1
            joinString = "\n" + ("\t" * self.tab) + "|| "
            self.writeLine(joinString.join([s.name for s in outStates]))
            self.tab -= 1
            self.writeLine(")")
        else:
            self.writeLine("always {}".format(state.name))
        self.tab -= 1
        self.writeLine(")")
        self.tab -= 1
        self.writeLine(")")
        self.tab -= 1
        self.writeLine(")")
        self.tab -= 1
        self.writeLine(")")
        self.tab -= 1
        self.writeLine("}")

    def writeLine(self, line):
        self.output_str += "\t" * self.tab
        self.output_str += line
        self.output_str += "\n"
