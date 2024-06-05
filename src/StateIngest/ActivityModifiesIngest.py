class ActivityModifiesIngestor:
    def __init__(self, inputFile=None):
        self.inputFile = inputFile
        self.clauses = {}

    def ingest(self):
        with open(self.inputFile, "r") as f:
            lines = f.readlines()
            for line in lines:
                tokens = line.split()
                if len(tokens) > 0:
                    activityID = tokens[0]
                    modifiedVars = tokens[1:]
                    self.clauses[activityID] = modifiedVars
