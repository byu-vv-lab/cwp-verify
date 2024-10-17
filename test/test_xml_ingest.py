# type: ignore
from bpmncwpverify.xml_ingest.BPMNXMLIngestor import get_bpmn_from_xml


def test_get_root():
    get_bpmn_from_xml("/workspaces/bpmn_cwp_verify/test/example/workflow.bpmn")
