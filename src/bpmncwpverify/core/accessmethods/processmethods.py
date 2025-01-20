from typing import cast
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import State
from returns.result import Result
from bpmncwpverify.core.error import (
    Error,
)

from bpmncwpverify.builder.process_builder import ProcessBuilder
from bpmncwpverify.core.bpmn import Process, get_element_type, BPMN_XML_NAMESPACE


def from_xml(
    element: Element,
    symbol_table: State,
) -> Result["Process", Error]:
    builder = ProcessBuilder(element, symbol_table)

    for sub_element in element:
        tag = sub_element.tag.partition("}")[2]

        result = get_element_type(tag)

        class_object = result.from_xml(sub_element)
        builder = builder.with_element(class_object)

    for seq_flow in element.findall("bpmn:sequenceFlow", BPMN_XML_NAMESPACE):
        builder = builder.with_process_flow(
            seq_flow.attrib["id"],
            seq_flow.attrib["sourceRef"],
            seq_flow.attrib["targetRef"],
            seq_flow.attrib.get("name", ""),
        )

    return cast(Result[Process, Error], builder.build())
