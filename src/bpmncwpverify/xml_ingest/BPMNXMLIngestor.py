from ..bpmn.BPMN import Bpmn


class BPMNXMLIngestor:
    @staticmethod
    def get_bpmn_from_xml(xml: str) -> Bpmn:
        return Bpmn()
