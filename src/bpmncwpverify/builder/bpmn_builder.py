from xml.etree.ElementTree import Element
from bpmncwpverify.core.bpmn import Bpmn, MessageFlow, Node, Process
from bpmncwpverify.core.state import SymbolTable
from bpmncwpverify.visitors.bpmnchecks.bpmnvalidate import validate_bpmn
from returns.result import Result, Success, Failure
from bpmncwpverify.error import (
    BpmnMsgMissingRefError,
    BpmnMsgNodeTypeError,
    Error,
    ExceptionError,
)


class BpmnBuilder:
    def __init__(self) -> None:
        self._bpmn = Bpmn()

    def build(self) -> Result[Bpmn, Error]:
        try:
            validate_bpmn(self._bpmn)
            return Success(self._bpmn)
        except Exception as e:
            return Failure(ExceptionError(str(e)))

    def with_process(
        self, element: Element, symbol_table: SymbolTable
    ) -> Result[Process, Error]:
        from bpmncwpverify.builder.process_builder import ProcessBuilder

        process_builder = ProcessBuilder(self._bpmn, element, symbol_table)

        for element in element:
            process_builder.with_element(element)

        result: Result[Process, Error] = process_builder.build()
        return result

    def with_message(self, msg_flow: Element) -> None:
        source_ref, target_ref = (
            msg_flow.get("sourceRef"),
            msg_flow.get("targetRef"),
        )

        message = MessageFlow(msg_flow)

        if not (source_ref and target_ref):
            raise Exception(BpmnMsgMissingRefError(message.id))

        self._bpmn.add_inter_process_msg(message)
        self._bpmn.store_element(message)

        from_node, to_node = (
            self._bpmn.get_element_from_id_mapping(source_ref),
            self._bpmn.get_element_from_id_mapping(target_ref),
        )

        if isinstance(from_node, Node) and isinstance(to_node, Node):
            message.target_node, message.source_node = to_node, from_node
            from_node.add_out_msg(message)
            to_node.add_in_msg(message)
        else:
            raise Exception(BpmnMsgNodeTypeError(message.id))
