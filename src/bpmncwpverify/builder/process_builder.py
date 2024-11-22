from xml.etree.ElementTree import Element
from typing import Dict, Type
from bpmncwpverify import utils
from bpmncwpverify.constants import NAMESPACES
from bpmncwpverify.core.bpmn import (
    Process,
    Bpmn,
    BpmnElement,
    Task,
    EndEvent,
    IntermediateEvent,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
    StartEvent,
    SequenceFlow,
    Node,
)
from bpmncwpverify.core.expr import ExpressionListener
from bpmncwpverify.core.state import SymbolTable
from returns.pipeline import is_successful
from returns.functions import not_


class ConcreteProcessBuilder:
    def __init__(self, bpmn: Bpmn, element: Element, symbol_table: SymbolTable) -> None:
        self._process = Process(element)
        self._bpmn = bpmn
        self._symbol_table = symbol_table

    _TAG_CLASS_MAPPING: Dict[str, Type[BpmnElement]] = {
        "task": Task,
        "startEvent": StartEvent,
        "endEvent": EndEvent,
        "exclusiveGateway": ExclusiveGatewayNode,
        "parallelGateway": ParallelGatewayNode,
        "sendTask": IntermediateEvent,
        "intermediateCatchEvent": IntermediateEvent,
        "intermediateThrowEvent": IntermediateEvent,
    }

    _FLOW_MAPPING = {"sequenceFlow": SequenceFlow}

    def _build_graph(self) -> None:
        for element_instance in self._process.all_items().values():
            for outgoing in element_instance.element.findall(
                "bpmn:outgoing", NAMESPACES
            ):
                flow_id = outgoing.text
                if not flow_id:
                    raise Exception("flow id is None")
                flow = self._process[flow_id.strip()]
                if not isinstance(flow, SequenceFlow):
                    # TODO: Make a custom error here:
                    raise Exception("flow not flow type")
                if flow is not None:
                    source_ref = self._bpmn.get_element_from_id_mapping(
                        flow.element.attrib["sourceRef"]
                    )
                    target_ref = self._bpmn.get_element_from_id_mapping(
                        flow.element.attrib["targetRef"]
                    )

                    raw_expression = flow.element.attrib.get("name", "")
                    if raw_expression:
                        expression = utils.cleanup_expression(raw_expression)
                        result = ExpressionListener.build(
                            expression, self._symbol_table
                        )
                        if not_(is_successful)(result) or result.unwrap() != "bool":
                            raise Exception(
                                f"Invalid expression: {result} while extracting expression from flow: {flow_id}"
                            )
                        flow.expression = expression

                    if isinstance(source_ref, Node) and isinstance(target_ref, Node):
                        # update flow's source_node
                        flow.source_node = source_ref
                        # update flow's target_node
                        flow.target_node = target_ref

                        if isinstance(flow, SequenceFlow):
                            # update source node's out flows array
                            source_ref.add_out_flow(flow)
                            # update target node's in flows array
                            target_ref.add_in_flow(flow)
                    else:
                        # TODO: Make a custom error here:
                        raise TypeError("toNode or fromNode is not of type Node")

    def add_element(self, element: Element) -> None:
        def get_tag_name(element: Element) -> str:
            return element.tag.partition("}")[2]

        tag_name = get_tag_name(element)

        element_class = (
            ConcreteProcessBuilder._TAG_CLASS_MAPPING.get(tag_name)
            or (
                ConcreteProcessBuilder._TAG_CLASS_MAPPING["task"]
                if "task" in tag_name.lower()
                else None
            )
            or ConcreteProcessBuilder._FLOW_MAPPING.get(tag_name)
        )

        if element_class:
            element_instance = element_class(element)
            self._process[element_instance.id] = element_instance
            self._bpmn.store_element(element_instance)

    def build(self) -> None:
        self._bpmn.processes[self._process.id] = self._process
        self._build_graph()
