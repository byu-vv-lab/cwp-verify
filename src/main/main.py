##########################################
# Main entry point into the project
# Options:
#
# #########################################

import shutil
import os
import sys
import pickle
import time
import getopt

# Importing necessary modules from the project
from StateIngest.StateIngestor import StateIngestor
from XMLIngest.BPMNXMLIngestor import BPMNXMLIngestor
from XMLIngest.CWPXMLIngestor import CWPXMLIngestor
from PromelaGeneration.LTL_gen import LTLGenerator
from PromelaGeneration.Promela_gen_visitor import Promela_gen_visitor
from StateIngest.ActivityModifiesIngest import ActivityModifiesIngestor
from CounterExampleVisualize.CounterExampleXMLGenerator import (
    CounterExampleXMLGenerator,
)
from PromelaGeneration.Stub_gen_visitor import Stub_gen_visitor


def visualizeProperty(exampleName, propertyName):
    # Function to visualize a specific property for a given example
    exAssetsDir = os.path.abspath("../assets/examples/{}".format(exampleName))
    exOutputDir = os.path.abspath("../output/examples/{}".format(exampleName))
    propDir = os.path.join(exOutputDir, "counterExamples", propertyName)
    if not os.path.exists(exOutputDir):
        os.makedirs(exOutputDir, exist_ok=True)
    if os.path.join(exAssetsDir, "state.txt").is_file():
        stateInput = os.path.join(exAssetsDir, "state.txt")
    if os.path.join(exAssetsDir, "workflow.bpmn").is_file():
        bpmnInput = os.path.join(exAssetsDir, "workflow.bpmn")
        pickledWorkflow = False
    elif os.path.join(exAssetsDir, "workflow.pickle").is_file():
        bpmnInput = os.path.join(exAssetsDir, "workflow.pickle")
        pickledWorkflow = True
    if os.path.join(exAssetsDir, "cwp.xml").is_file():
        cwpInput = os.path.join(exAssetsDir, "cwp.xml")
        pickledCWP = False
    elif os.path.join(exAssetsDir, "cwp.pickle").is_file():
        cwpInput = os.path.join(exAssetsDir, "cwp.pickle")
        pickledCWP = True
    varList = ingestState(stateInput)
    processCounterExampleDir(
        propDir, bpmnInput, cwpInput, varList, pickledWorkflow, pickledCWP
    )


def processCounterExampleDir(
    dir, bpmnInput, cwpInput, varList, pickledWorkflow, pickledCWP
):
    # Function to process the counterexample directory and generate images
    trailFile = os.path.join(dir, "trail.txt")
    generator = CounterExampleXMLGenerator(
        counterExampleFile=trailFile,
        bpmnFile=bpmnInput,
        cwpFile=cwpInput,
        varList=varList,
        premadeBPMN=pickledWorkflow,
        premadeCWP=pickledCWP,
    )
    generator.genCounterExampleImages()
    print("Writing counterexample files for: {}\n".format(dir))
    cmd = "docker run -it -e DRAWIO_DESKTOP_COMMAND_TIMEOUT='10000s' -w /data -v {dir}:/data rlespinasse/drawio-desktop-headless -x -f png ./".format(
        dir=dir
    )
    os.system(cmd)
    for subdir2, _, files in os.walk(dir):
        for file in files:
            file = os.path.join(subdir2, file)
            if file.endswith(".bpmn"):
                cmd = "bpmn-to-image {file}:{output}".format(
                    file=file, output=file + ".png"
                )
                os.system(cmd)

        cmd = "convert {subdir}/*.bpmn.png {subdir}/BPMNerror.pdf".format(
            subdir=subdir2
        )
        os.system(cmd)
        cmd = "convert {subdir}/*.cwp.png {subdir}/CWPerror.pdf".format(subdir=subdir2)
        os.system(cmd)
    print("Done!\n")


def ingestState(file):
    # Function to ingest state from a file
    stateIngestor = StateIngestor(inputFile=file)
    stateIngestor.ingestState()
    return stateIngestor.varList


def runExample(
    name,
    pickledCWP=False,
    pickledWorkflow=False,
    debug=False,
    skipCEGeneration=False,
    bfs=False,
    approxShortestPath=False,
    shortestPath=False,
):
    # Function to run an example
    st = time.time()
    outStr = ""
    exAssetsDir = os.path.abspath("../assets/examples/{}".format(name))
    exOutputDir = os.path.abspath("../output/examples/{}".format(name))
    if not os.path.exists(exOutputDir):
        os.makedirs(exOutputDir, exist_ok=True)

    if pickledWorkflow:
        bpmnInput = "{}/workflow.pickle".format(exAssetsDir)
    else:
        bpmnInput = "{}/workflow.bpmn".format(exAssetsDir)
    if pickledCWP:
        cwpInput = "{}/cwp.pickle".format(exAssetsDir)
    else:
        cwpInput = "{}/cwp.xml".format(exAssetsDir)

    outFile = "{}/model.pml".format(exOutputDir)
    "{}/printfModel.pml".format(exOutputDir)
    stateFile = "{}/state.txt".format(exAssetsDir)
    behaviorModelFile = "{}/behaviorModels.pml".format(exAssetsDir)
    modifiesFile = "{}/modifies.txt".format(exAssetsDir)
    timingResultsFile = "{}/timing.txt".format(exOutputDir)
    purgeDirectory(exOutputDir)

    counterExampleDir = "{}/counterExamples".format(exOutputDir)
    if not os.path.exists(counterExampleDir):
        os.mkdir(counterExampleDir)
    modelGenerationST = time.time()
    sys.setrecursionlimit(2000)
    propertyList, varList = genPromelaFile(
        bpmnInput,
        cwpInput,
        stateFile,
        outFile,
        modifiesFile,
        behaviorModelFile,
        outStr,
        pickledCWP,
        pickledWorkflow,
        debug,
        printfOn=True,
    )

    modelGenerationET = time.time()
    modelGenerationTT = modelGenerationET - modelGenerationST
    propertyFile = "{}/properties.txt".format(exAssetsDir)
    with open(propertyFile, "w+") as f:
        f.writelines("\n".join(propertyList))
    if not os.path.exists(behaviorModelFile):
        return
    verificationST = time.time()
    print("Beginning Verification for Example: {}".format(name))
    if bfs:
        flags = "-bfs"
    elif shortestPath:
        flags = "-i"
    elif approxShortestPath:
        flags = "-I"
    else:
        flags = ""
    cmd = "./Util/verify.sh {name} {flags}".format(name=name, flags=flags)
    os.system(cmd)
    print("Verification Finished\n")
    verificationET = time.time()
    verificationTT = verificationET - verificationST

    if pickledCWP or pickledWorkflow or skipCEGeneration:
        counterExampleTT = 0
        print("skipping counterExample Visualization\n")
    else:
        counterexampleST = time.time()
        for subdir, dirs, _ in os.walk(counterExampleDir):
            for dir in dirs:
                dirPath = os.path.join(subdir, dir)
                processCounterExampleDir(
                    dirPath, bpmnInput, cwpInput, varList, pickledWorkflow, pickledCWP
                )
        counterExampleET = time.time()
        counterExampleTT = counterExampleET - counterexampleST
    et = time.time()
    total_time = et - st

    with open(timingResultsFile, "w+") as f:
        print("Writing Timing File...")
        f.write(
            "Model Generation: {}\n".format(
                time.strftime("%H:%M:%S", time.gmtime(modelGenerationTT))
            )
        )
        f.write(
            "Verification: {}\n".format(
                time.strftime("%H:%M:%S", time.gmtime(verificationTT))
            )
        )
        f.write(
            "CounterExample Visualization Generation: {}\n".format(
                time.strftime("%H:%M:%S", time.gmtime(counterExampleTT))
            )
        )
        f.write(
            "Total: {}\n".format(time.strftime("%H:%M:%S", time.gmtime(total_time)))
        )
        print("Done")


def purgeDirectory(dir):
    # Function to delete and recreate a directory
    shutil.rmtree(dir)
    os.mkdir(dir)


def genPromelaFile(
    bpmnInput,
    cwpInput,
    stateFile,
    outFile,
    modifiesFile,
    behaviorModelFile,
    outStr,
    premadeCWP=False,
    premadeWorkflow=False,
    debug=False,
    printfOn=False,
):
    # Function to generate Promela file
    # STATE INGEST
    varList = ingestState(file=stateFile)

    # MODIFIES FILE INGEST
    modifiesIngest = ActivityModifiesIngestor(inputFile=modifiesFile)
    modifiesIngest.ingest()
    modifiesClauses = modifiesIngest.clauses

    # CWP PROPERTY GENERATION
    if premadeCWP:
        with open(cwpInput, "rb") as f:
            cwpModel = pickle.load(f)
    else:
        myCwpIngestor = CWPXMLIngestor(varList=varList)
        myCwpIngestor.inputfile = cwpInput
        myCwpIngestor.ingestXML()
        cwpModel = myCwpIngestor.cwp
    myLTLGen = LTLGenerator(
        cwp=cwpModel, varList=varList, debug=debug, printfOn=printfOn
    )
    myLTLGen.generate_all()
    outStr += str(myLTLGen.output_str)

    # BPMN MODEL GENERATION
    BPMNNamespaceMap = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}
    bpmnIngestor = BPMNXMLIngestor(
        ns=BPMNNamespaceMap, varList=varList, modifiesClauses=modifiesIngest.clauses
    )

    if premadeWorkflow:
        with open(bpmnInput, "rb") as f:
            BPMNModel = pickle.load(f)
        with open(bpmnInput, "rb") as f:
            BPMNModel2 = pickle.load(f)
    else:
        bpmnIngestor.inputfile = bpmnInput
        BPMNModel = bpmnIngestor.processXML()
        BPMNModel2 = bpmnIngestor.processXML()
    myVisitor = Promela_gen_visitor(printfOn=printfOn)
    stubVisitor = Stub_gen_visitor(varList=varList, modifiesClauses=modifiesClauses)
    BPMNModel.accept(myVisitor)

    BPMNModel2.accept(stubVisitor)
    if os.path.exists(behaviorModelFile):
        with open(behaviorModelFile) as f:
            myVisitor.behaviorModelText = f.read()
    else:
        myVisitor.behaviorModelText = str(stubVisitor)
    outStr += str(myVisitor)

    # WRITING IT ALL TO THE OUTPUT FILE
    with open(outFile, "w+") as f:
        f.write(outStr)

    return myLTLGen.propertyList, varList


def parse(argv):
    # Function to parse command line arguments
    preloaded, debug, skipCEGeneration, bfs, approxShortestPath, shortestPath = (
        False,
        False,
        False,
        False,
        False,
        False,
    )
    try:
        opts, args = getopt.getopt(
            argv,
            "e:pdsIi",
            [
                "example=",
                "pickled",
                "debug",
                "skipCEGeneration",
                "approxShortestPath",
                "shortestPath",
            ],
        )
    except getopt.GetoptError:
        print(
            "main.py -e <exampleName> [-p --pickled -d --debug -s --skipCEGeneration -I --approxShortestPath -i --shortestPath]"
        )
        sys.exit(2)
    exampleName = ""
    for opt, arg in opts:
        if opt in ["-e", "--example"]:
            exampleName = arg
        if opt in ["-p", "--pickled"]:
            preloaded = True
        if opt in ["-d", "--debug"]:
            debug = True
        if opt in ["-s", "--skipCEGeneration"]:
            skipCEGeneration = True
        if opt in ["-b", "--bfs"]:
            bfs = True
        if opt in ["-I", "--approxShortestPath"]:
            approxShortestPath = True
        if opt in ["-i", "--shortestPath"]:
            shortestPath = True

    return (
        exampleName,
        preloaded,
        debug,
        skipCEGeneration,
        bfs,
        approxShortestPath,
        shortestPath,
    )


def _verify(argv):
    # Main function
    # PARSING INPUT
    (
        exampleName,
        preloaded,
        debug,
        skipCEGeneration,
        bfs,
        approxShortestPath,
        shortestPath,
    ) = parse(argv)

    if exampleName:
        runExample(
            exampleName,
            pickledCWP=False,
            pickledWorkflow=preloaded,
            debug=debug,
            skipCEGeneration=skipCEGeneration,
            bfs=bfs,
            approxShortestPath=approxShortestPath,
            shortestPath=shortestPath,
        )
    else:
        print("must include example name")
