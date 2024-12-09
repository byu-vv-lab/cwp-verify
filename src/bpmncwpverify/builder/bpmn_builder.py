from xml.etree.ElementTree import Element
from bpmncwpverify.core.bpmn import Bpmn, MessageFlow, Node, Process
from bpmncwpverify.core.state import SymbolTable
from bpmncwpverify.visitors.bpmn_connectivity_visitor import BpmnConnectivityVisitor
from returns.result import Result, Success, Failure
from bpmncwpverify.error import Error, MessageError


class BpmnBuilder:
    def __init__(self) -> None:
        self._bpmn = Bpmn()

    def _msg_connects_diff_pools(self) -> None:
        for msg in self._bpmn.inter_process_msgs.values():
            for process in self._bpmn.processes.values():
                if (
                    msg.target_node.id in process.all_items()
                    and msg.source_node.id in process.all_items()
                ):
                    raise Exception(
                        MessageError(
                            msg.id,
                            "A message flow cannot connect nodes in the same pool.",
                        )
                    )

    def build(self) -> Result[Bpmn, Error]:
        try:
            visitor = BpmnConnectivityVisitor()

            self._bpmn.accept(visitor)

            # Check to make sure messages do not connect nodes from same pool:
            self._msg_connects_diff_pools()

            return Success(self._bpmn)
        except Exception as e:
            return Failure(e)

    def add_process(
        self, element: Element, symbol_table: SymbolTable
    ) -> Result[Process, Error]:
        from bpmncwpverify.builder.process_builder import ProcessBuilder

        process_builder = ProcessBuilder(self._bpmn, element, symbol_table)

        for element in element:
            process_builder.add_element(element)

        return process_builder.build()

    def add_message(self, msg_flow: Element) -> None:
        source_ref, target_ref = (
            msg_flow.get("sourceRef"),
            msg_flow.get("targetRef"),
        )

        if not (source_ref and target_ref):
            raise Exception("source ref or target ref not included with message")

        message = MessageFlow(msg_flow)
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
            raise TypeError("to_node or from_node is not of type Node")
