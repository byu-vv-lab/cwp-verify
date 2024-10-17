from ..bpmn.BPMN import Bpmn
from defusedxml.ElementTree import parse


class BPMNXMLIngestor:
    @staticmethod
    def get_bpmn_from_xml(xml_file: str) -> Bpmn:
        tree = parse(xml_file)

        root = tree.getroot()
        print(root)

        return Bpmn()
