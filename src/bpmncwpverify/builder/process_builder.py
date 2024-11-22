from xml.etree.ElementTree import Element
from typing import Dict, Tuple, Type
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


class ProcessBuilder:
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

    def _construct_flow_network(self) -> None:
        for element_instance in self._process.all_items().values():
            for outgoing in element_instance.element.findall(
                "bpmn:outgoing", NAMESPACES
            ):
                flow_id = self._get_flow_id(outgoing)
                flow = self._get_flow(flow_id)
                source_ref, target_ref = self._get_source_and_target_refs(flow)

                self._validate_and_set_flow_expression(flow, flow_id)
                self._link_flow_to_nodes(flow, source_ref, target_ref)

    def _get_flow_id(self, outgoing: Element) -> str:
        flow_id = outgoing.text
        if not flow_id:
            raise Exception("flow id is None")
        return flow_id.strip()

    def _get_flow(self, flow_id: str) -> SequenceFlow:
        flow = self._process[flow_id]
        if not isinstance(flow, SequenceFlow):
            raise Exception("flow not flow type")
        return flow

    def _get_source_and_target_refs(self, flow: SequenceFlow) -> Tuple[Node, Node]:
        source_ref = self._bpmn.get_element_from_id_mapping(
            flow.element.attrib["sourceRef"]
        )
        target_ref = self._bpmn.get_element_from_id_mapping(
            flow.element.attrib["targetRef"]
        )
        if not (isinstance(source_ref, Node) and isinstance(target_ref, Node)):
            raise Exception("Source ref or target ref is not of type node")
        return source_ref, target_ref

    def _validate_and_set_flow_expression(
        self, flow: SequenceFlow, flow_id: str
    ) -> None:
        raw_expression = flow.element.attrib.get("name", "")
        if raw_expression:
            expression = utils.cleanup_expression(raw_expression)
            result = ExpressionListener.build(expression, self._symbol_table)
            if not_(is_successful)(result) or result.unwrap() != "bool":
                raise Exception(
                    f"Invalid expression: {result} while extracting expression from flow: {flow_id}"
                )
            flow.expression = expression

    def _link_flow_to_nodes(
        self, flow: SequenceFlow, source_ref: Node, target_ref: Node
    ) -> None:
        if isinstance(source_ref, Node) and isinstance(target_ref, Node):
            flow.source_node = source_ref
            flow.target_node = target_ref

            source_ref.add_out_flow(flow)
            target_ref.add_in_flow(flow)
        else:
            raise TypeError("sourceRef or targetRef is not of type Node")

    def add_element(self, element: Element) -> None:
        def get_tag_name(element: Element) -> str:
            return element.tag.partition("}")[2]

        tag_name = get_tag_name(element)

        element_class = (
            ProcessBuilder._TAG_CLASS_MAPPING.get(tag_name)
            or (
                ProcessBuilder._TAG_CLASS_MAPPING["task"]
                if "task" in tag_name.lower()
                else None
            )
            or ProcessBuilder._FLOW_MAPPING.get(tag_name)
        )

        if element_class:
            element_instance = element_class(element)
            self._process[element_instance.id] = element_instance
            self._bpmn.store_element(element_instance)

    def build(self) -> None:
        self._bpmn.processes[self._process.id] = self._process
        self._construct_flow_network()
