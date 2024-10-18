# type: ignore
from bpmncwpverify.xml_ingest.bpmn_xml_ingestor import get_bpmn_from_xml
from bpmncwpverify.bpmn.BPMN import Bpmn, ParallelGatewayNode


def test_get_root():
    bpmn: Bpmn = get_bpmn_from_xml(
        "/workspaces/bpmn_cwp_verify/test/example/workflow.bpmn"
    )

    assert len(bpmn.processes) == 1

    process = bpmn.processes[0]

    assert process.id == "Process_1xbpt9j"

    # Gateways
    gateway_12r266n = process.elements.get("Gateway_12r266n")
    assert isinstance(gateway_12r266n, ParallelGatewayNode)
    assert gateway_12r266n is not None
    assert gateway_12r266n.name == "both"
    assert len(gateway_12r266n.in_flows) == 2
    assert len(gateway_12r266n.out_flows) == 2
    assert "Flow_08e7qxg" in {flow.id for flow in gateway_12r266n.in_flows}
    assert "Flow_1wl740o" in {flow.id for flow in gateway_12r266n.in_flows}
    assert "Flow_1kx5xjv" in {flow.id for flow in gateway_12r266n.out_flows}
    assert "Flow_13xpfx7" in {flow.id for flow in gateway_12r266n.out_flows}

    gateway_0s1i42o = process.elements.get("Gateway_0s1i42o")
    assert gateway_0s1i42o is not None
    assert gateway_0s1i42o.name == "end both"
    assert len(gateway_0s1i42o.in_flows) == 2
    assert len(gateway_0s1i42o.out_flows) == 1
    assert "Flow_14s5onf" in {flow.id for flow in gateway_0s1i42o.in_flows}
    assert "Flow_1oezfcg" in {flow.id for flow in gateway_0s1i42o.in_flows}
    assert "Flow_0feadgd" in {flow.id for flow in gateway_0s1i42o.out_flows}

    gateway_1pm4ghz = process.elements.get("Gateway_1pm4ghz")
    assert gateway_1pm4ghz is not None
    assert gateway_1pm4ghz.name == "payment and terms agreed"
    assert len(gateway_1pm4ghz.in_flows) == 3
    assert len(gateway_1pm4ghz.out_flows) == 5
    assert "Flow_0feadgd" in {flow.id for flow in gateway_1pm4ghz.in_flows}
    assert "Flow_127sd29" in {flow.id for flow in gateway_1pm4ghz.in_flows}
    assert "Flow_00oxr95" in {flow.id for flow in gateway_1pm4ghz.in_flows}
    assert "Flow_0yqye0v" in {flow.id for flow in gateway_1pm4ghz.out_flows}
    assert "Flow_0diuub0" in {flow.id for flow in gateway_1pm4ghz.out_flows}
    assert "Flow_0q6dz8p" in {flow.id for flow in gateway_1pm4ghz.out_flows}
    assert "Flow_0koz64j" in {flow.id for flow in gateway_1pm4ghz.out_flows}
    assert "Flow_08e7qxg" in {flow.id for flow in gateway_1pm4ghz.out_flows}

    gateway_000lymc = process.elements.get("Gateway_000lymc")
    assert gateway_000lymc is not None
    assert gateway_000lymc.name == "both1"
    assert len(gateway_000lymc.in_flows) == 1
    assert len(gateway_000lymc.out_flows) == 2
    assert "Flow_0ct87dl" in {flow.id for flow in gateway_000lymc.in_flows}
    assert "Flow_0jmvvxc" in {flow.id for flow in gateway_000lymc.out_flows}
    assert "Flow_1y66pph" in {flow.id for flow in gateway_000lymc.out_flows}

    gateway_0cy7rs7 = process.elements.get("Gateway_0cy7rs7")
    assert gateway_0cy7rs7 is not None
    assert gateway_0cy7rs7.name == "end both1"
    assert len(gateway_0cy7rs7.in_flows) == 2
    assert len(gateway_0cy7rs7.out_flows) == 1
    assert "Flow_1sx1rdt" in {flow.id for flow in gateway_0cy7rs7.in_flows}
    assert "Flow_0znbe82" in {flow.id for flow in gateway_0cy7rs7.in_flows}
    assert "Flow_1cm84v3" in {flow.id for flow in gateway_0cy7rs7.out_flows}

    # Activities
    activity_1unsjkg = process.elements.get("Activity_1unsjkg")
    assert activity_1unsjkg is not None
    assert activity_1unsjkg.name == "2-Buyer and Seller negotiate terms"
    assert len(activity_1unsjkg.in_flows) == 1
    assert len(activity_1unsjkg.out_flows) == 1
    assert "Flow_1kx5xjv" in {flow.id for flow in activity_1unsjkg.in_flows}
    assert "Flow_1oezfcg" in {flow.id for flow in activity_1unsjkg.out_flows}

    activity_1t579ox = process.elements.get("Activity_1t579ox")
    assert activity_1t579ox is not None
    assert activity_1t579ox.name == "3-Buyer and Seller negotiate price"
    assert len(activity_1t579ox.in_flows) == 1
    assert len(activity_1t579ox.out_flows) == 1
    assert "Flow_13xpfx7" in {flow.id for flow in activity_1t579ox.in_flows}
    assert "Flow_14s5onf" in {flow.id for flow in activity_1t579ox.out_flows}

    activity_1qm7qck = process.elements.get("Activity_1qm7qck")
    assert activity_1qm7qck is not None
    assert activity_1qm7qck.name == "1-Buyer sees desired backpack and meets Seller"
    assert len(activity_1qm7qck.in_flows) == 1
    assert len(activity_1qm7qck.out_flows) == 1
    assert "Flow_0oiwgjd" in {flow.id for flow in activity_1qm7qck.in_flows}
    assert "Flow_1wl740o" in {flow.id for flow in activity_1qm7qck.out_flows}

    activity_1qqx4aq = process.elements.get("Activity_1qqx4aq")
    assert activity_1qqx4aq is not None
    assert activity_1qqx4aq.name == "7a-Buyer hands cash payment to Seller"
    assert len(activity_1qqx4aq.in_flows) == 1
    assert len(activity_1qqx4aq.out_flows) == 1
    assert "Flow_0jmvvxc" in {flow.id for flow in activity_1qqx4aq.in_flows}
    assert "Flow_0znbe82" in {flow.id for flow in activity_1qqx4aq.out_flows}

    activity_1rfm4sh = process.elements.get("Activity_1rfm4sh")
    assert activity_1rfm4sh is not None
    assert activity_1rfm4sh.name == "7b-Seller hands Backpack to Buyer"
    assert len(activity_1rfm4sh.in_flows) == 1
    assert len(activity_1rfm4sh.out_flows) == 1
    assert "Flow_1y66pph" in {flow.id for flow in activity_1rfm4sh.in_flows}
    assert "Flow_1sx1rdt" in {flow.id for flow in activity_1rfm4sh.out_flows}

    # End event
    end_event_0wqympo = process.elements.get("Event_0wqympo")
    assert end_event_0wqympo is not None
    assert end_event_0wqympo.name == "Purchase Failed"
    assert len(end_event_0wqympo.in_flows) == 1
    assert "Flow_0diuub0" in {flow.id for flow in end_event_0wqympo.in_flows}

    end_event_1y6wxsp = process.elements.get("Event_1y6wxsp")
    assert end_event_1y6wxsp is not None
    assert end_event_1y6wxsp.name == "Purchase Completed"
    assert len(end_event_1y6wxsp.in_flows) == 1
    assert "Flow_1cm84v3" in {flow.id for flow in end_event_1y6wxsp.in_flows}

    # Start event
    start_event_1y8wbre = process.elements.get("StartEvent_1y8wbre")
    assert start_event_1y8wbre is not None
    assert start_event_1y8wbre.name == "Start7"
    assert len(start_event_1y8wbre.out_flows) == 1
    assert len(start_event_1y8wbre.in_flows) == 0
    assert "Flow_0oiwgjd" in {flow.id for flow in start_event_1y8wbre.out_flows}
