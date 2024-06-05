class CWP:
    def __init__(self):
        self.states = []
        self.aps = []
        self.edges = []
        self.endStates = []

    def addState(self, state):
        self.states.append(state)

    def addEdge(self, edge):
        self.edges.append(edge)

    def addAP(self, ap: str):
        self.aps.append(ap)

    def calcEndStates(self):
        self.endStates = []
        for state in self.states:
            if not state.outEdges:
                self.endStates.append(state)

    def isEdgeFrom(self, fromState, toState):
        for edge in self.edges:
            if not edge.source or not edge.dest:
                continue
            if edge.source.name == fromState and edge.dest.name == toState:
                return True
        return False


class CWPState:
    def __init__(self, name="", idRef=""):
        # Name of the state. Should consist of alphanumeric characters only
        # Should not begin with a number. Suggest to end with "state"
        self.name = name

        # A reference to the ID of the object in the imported source file.
        self.idRef = idRef

        self.inEdges = []

        self.outEdges = []

    def addInEdge(self, edge):
        self.inEdges.append(edge)

    def addOutEdge(self, edge):
        self.outEdges.append(edge)


class CWPEdge:
    def __init__(self, label="", name="", idRef="", labelIdRef=""):
        # Name of the edge. Will be used for macros in LTL generation
        # Should begin with a letter and only use alphanumeric characters
        self.name = name

        # Label of the edge. Currently, the label is used directly as the
        # definition of the edge. It must be a valid Promela logical expression.
        self.label = label

        # A reference to the ID of the object in the imported source file.
        self.idRef = idRef
        self.labelIdRef = labelIdRef

        self.source = None
        self.dest = None

    def setSource(self, state):
        self.source = state

    def setDest(self, state):
        self.dest = state
