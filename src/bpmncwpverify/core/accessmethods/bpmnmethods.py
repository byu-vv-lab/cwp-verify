from typing import cast
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import State
from returns.result import Result
from returns.pipeline import is_successful
from returns.functions import not_
from bpmncwpverify.core.error import (
    Error,
)
from bpmncwpverify.core.bpmn import (
    Bpmn,
    BPMN_XML_NAMESPACE,
    MessageFlow,
)
from bpmncwpverify.builder.bpmn_builder import BpmnBuilder
from bpmncwpverify.core.accessmethods.processmethods import from_xml as process_from_xml
from bpmncwpverify.visitors.bpmn_promela_visitor import PromelaGenVisitor
from bpmncwpverify.visitors.bpmn_graph_visitor import GraphVizVisitor


def generate_promela(bpmn: Bpmn) -> str:
    promela_visitor = PromelaGenVisitor()

    bpmn.accept(promela_visitor)

    return str(promela_visitor)


def from_xml(root: Element, symbol_table: State) -> Result["Bpmn", Error]:
    ##############
    # Build and add processes
    ##############
    processes = root.findall("bpmn:process", BPMN_XML_NAMESPACE)
    bpmn_builder = BpmnBuilder()
    for process_element in processes:
        process = process_from_xml(process_element, symbol_table)
        if not_(is_successful)(process):
            return cast(Result[Bpmn, Error], process)
        bpmn_builder = bpmn_builder.with_process(process.unwrap())

    ##############
    # Build and add messages
    ##############
    collab = root.find("bpmn:collaboration", BPMN_XML_NAMESPACE)
    if collab is not None:
        # TODO: write test for messages in the bpmn diagram
        bpmn_builder = bpmn_builder.with_process_elements()
        for msg_flow in collab.findall("bpmn:messageFlow", BPMN_XML_NAMESPACE):
            source_ref, target_ref = (
                msg_flow.get("sourceRef"),
                msg_flow.get("targetRef"),
            )

            message = MessageFlow.from_xml(msg_flow)

            assert source_ref and target_ref

            bpmn_builder = bpmn_builder.with_message(message, source_ref, target_ref)

    return cast(Result[Bpmn, Error], bpmn_builder.build())


def generate_graph_viz(bpmn: Bpmn) -> None:
    for process in range(len(bpmn.processes)):
        graph_viz_visitor = GraphVizVisitor(process + 1)

        bpmn.accept(graph_viz_visitor)

        graph_viz_visitor.dot.render("graphs/bpmn_graph.gv", format="png")  # type: ignore[unused-ignore]
