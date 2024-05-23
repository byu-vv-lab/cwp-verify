import CWP.CWP as cwp
import pickle


class WideScaling:
    def __init__(self, numActors=5, outputFile=None):
        self.numActors = numActors
        if outputFile is None:
            self.outputFile = "./../../assets/examples/wideScaling{}/cwp.pickle".format(
                numActors
            )
        else:
            self.outputFile = outputFile
        self.cwpModel = cwp.CWP()

    def genFile(self):
        initState = cwp.CWPState("Init State")
        goalState = cwp.CWPState("Goal State")
        edgeLabel = "&&".join(
            ["fin{}==True".format(actor + 1) for actor in range(self.numActors)]
        )
        print(edgeLabel)
        edge = cwp.CWPEdge(edgeLabel, "edge1")

        initState.addOutEdge(edge)
        goalState.addInEdge(edge)
        edge.setSource(initState)
        edge.setDest(goalState)

        with open(self.outputFile, "w+b") as f:
            pickle.dump(self.cwpModel, f)


if __name__ == "__main__":
    ws5 = WideScaling()
    ws5.genFile()
