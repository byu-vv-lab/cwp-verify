# type: ignore
from bpmncwpverify.xml_ingest.bpmn_xml_ingestor import get_bpmn_from_xml
from bpmncwpverify.bpmn.BPMN import Bpmn


def test_get_root():
    bpmn: Bpmn = get_bpmn_from_xml(
        "/workspaces/bpmn_cwp_verify/test/example/workflow.bpmn"
    )

    assert len(bpmn.processes) == 1

    process = bpmn.processes[0]

    assert process.id == "Process_1xbpt9j"

    gateway_element = process.elements.get("Gateway_12r266n")
    assert gateway_element is not None
    assert gateway_element.name == "both"

    assert len(gateway_element.in_flows) == 2
    assert len(gateway_element.out_flows) == 2
    assert "Flow_08e7qxg" in {flow.id for flow in gateway_element.in_flows}
    assert "Flow_1wl740o" in {flow.id for flow in gateway_element.in_flows}
    assert "Flow_1kx5xjv" in {flow.id for flow in gateway_element.out_flows}
    assert "Flow_13xpfx7" in {flow.id for flow in gateway_element.out_flows}
