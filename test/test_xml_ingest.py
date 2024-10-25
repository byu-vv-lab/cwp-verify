# type: ignore
from unittest.mock import MagicMock
from returns.pipeline import is_successful
from bpmncwpverify.promela_gen_visitor import PromelaGenVisitor
from bpmncwpverify.BPMN import (
    Bpmn,
    ParallelGatewayNode,
)
import os

# List of flows with their source and target node IDs
current_directory = os.path.dirname(os.path.abspath(__file__))

workflow_bpmn_path = os.path.join(current_directory, "example", "workflow.bpmn")
flows_to_test = [
    ("Flow_08e7qxg", "Gateway_1pm4ghz", "Gateway_12r266n", True),
    ("Flow_1wl740o", "Activity_1qm7qck", "Gateway_12r266n", False),
    ("Flow_1kx5xjv", "Gateway_12r266n", "Activity_1unsjkg", False),
    ("Flow_13xpfx7", "Gateway_12r266n", "Activity_1t579ox", False),
    ("Flow_1oezfcg", "Activity_1unsjkg", "Gateway_0s1i42o", False),
    ("Flow_14s5onf", "Activity_1t579ox", "Gateway_0s1i42o", False),
    ("Flow_0feadgd", "Gateway_0s1i42o", "Gateway_1pm4ghz", False),
    ("Flow_127sd29", "Activity_1bckz5y", "Gateway_1pm4ghz", True),
    ("Flow_00oxr95", "Activity_1mktua2", "Gateway_1pm4ghz", True),
    ("Flow_0yqye0v", "Gateway_1pm4ghz", "Activity_0a5xzqf", False),
    ("Flow_0diuub0", "Gateway_1pm4ghz", "Event_0wqympo", False),
    ("Flow_0q6dz8p", "Gateway_1pm4ghz", "Activity_1bckz5y", False),
    ("Flow_0koz64j", "Gateway_1pm4ghz", "Activity_1mktua2", False),
    ("Flow_0ct87dl", "Activity_0a5xzqf", "Gateway_000lymc", False),
    ("Flow_0jmvvxc", "Gateway_000lymc", "Activity_1qqx4aq", False),
    ("Flow_1y66pph", "Gateway_000lymc", "Activity_1rfm4sh", False),
    ("Flow_0znbe82", "Activity_1qqx4aq", "Gateway_0cy7rs7", False),
    ("Flow_1sx1rdt", "Activity_1rfm4sh", "Gateway_0cy7rs7", False),
    ("Flow_1cm84v3", "Gateway_0cy7rs7", "Event_1y6wxsp", False),
    ("Flow_0oiwgjd", "StartEvent_1y8wbre", "Activity_1qm7qck", False),
]


def assert_flow(process, flow_id, source_id, target_id, is_back_edge):
    flow = process.flows.get(flow_id)
    assert flow is not None, f"Flow {flow_id} not found"
    assert flow.is_back_edge == is_back_edge
    assert flow.source_node.id == source_id, f"Flow {flow_id} source node mismatch"
    assert flow.target_node.id == target_id, f"Flow {flow_id} target node mismatch"


def test_xml_parser():
    bpmn: Bpmn = Bpmn.from_xml(workflow_bpmn_path)

    assert is_successful(bpmn)

    bpmn = bpmn.unwrap()

    assert len(bpmn.processes) == 1

    process = bpmn.processes[0]

    assert process.id == "Process_1xbpt9j"

    # Gateways
    gateway_12r266n = process["Gateway_12r266n"]
    assert isinstance(gateway_12r266n, ParallelGatewayNode)
    assert gateway_12r266n is not None
    assert gateway_12r266n.name == "both"
    assert len(gateway_12r266n.in_flows) == 2
    assert len(gateway_12r266n.out_flows) == 2
    assert "Flow_08e7qxg" in {flow.id for flow in gateway_12r266n.in_flows}
    assert "Flow_1wl740o" in {flow.id for flow in gateway_12r266n.in_flows}
    assert "Flow_1kx5xjv" in {flow.id for flow in gateway_12r266n.out_flows}
    assert "Flow_13xpfx7" in {flow.id for flow in gateway_12r266n.out_flows}

    gateway_0s1i42o = process["Gateway_0s1i42o"]
    assert gateway_0s1i42o is not None
    assert gateway_0s1i42o.name == "end both"
    assert len(gateway_0s1i42o.in_flows) == 2
    assert len(gateway_0s1i42o.out_flows) == 1
    assert "Flow_14s5onf" in {flow.id for flow in gateway_0s1i42o.in_flows}
    assert "Flow_1oezfcg" in {flow.id for flow in gateway_0s1i42o.in_flows}
    assert "Flow_0feadgd" in {flow.id for flow in gateway_0s1i42o.out_flows}

    gateway_1pm4ghz = process["Gateway_1pm4ghz"]
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

    gateway_000lymc = process["Gateway_000lymc"]
    assert gateway_000lymc is not None
    assert gateway_000lymc.name == "both1"
    assert len(gateway_000lymc.in_flows) == 1
    assert len(gateway_000lymc.out_flows) == 2
    assert "Flow_0ct87dl" in {flow.id for flow in gateway_000lymc.in_flows}
    assert "Flow_0jmvvxc" in {flow.id for flow in gateway_000lymc.out_flows}
    assert "Flow_1y66pph" in {flow.id for flow in gateway_000lymc.out_flows}

    gateway_0cy7rs7 = process["Gateway_0cy7rs7"]
    assert gateway_0cy7rs7 is not None
    assert gateway_0cy7rs7.name == "end both1"
    assert len(gateway_0cy7rs7.in_flows) == 2
    assert len(gateway_0cy7rs7.out_flows) == 1
    assert "Flow_1sx1rdt" in {flow.id for flow in gateway_0cy7rs7.in_flows}
    assert "Flow_0znbe82" in {flow.id for flow in gateway_0cy7rs7.in_flows}
    assert "Flow_1cm84v3" in {flow.id for flow in gateway_0cy7rs7.out_flows}

    # Activities
    activity_1unsjkg = process["Activity_1unsjkg"]
    assert activity_1unsjkg is not None
    assert activity_1unsjkg.name == "2-Buyer and Seller negotiate terms"
    assert len(activity_1unsjkg.in_flows) == 1
    assert len(activity_1unsjkg.out_flows) == 1
    assert "Flow_1kx5xjv" in {flow.id for flow in activity_1unsjkg.in_flows}
    assert "Flow_1oezfcg" in {flow.id for flow in activity_1unsjkg.out_flows}

    activity_1t579ox = process["Activity_1t579ox"]
    assert activity_1t579ox is not None
    assert activity_1t579ox.name == "3-Buyer and Seller negotiate price"
    assert len(activity_1t579ox.in_flows) == 1
    assert len(activity_1t579ox.out_flows) == 1
    assert "Flow_13xpfx7" in {flow.id for flow in activity_1t579ox.in_flows}
    assert "Flow_14s5onf" in {flow.id for flow in activity_1t579ox.out_flows}

    activity_1qm7qck = process["Activity_1qm7qck"]
    assert activity_1qm7qck is not None
    assert activity_1qm7qck.name == "1-Buyer sees desired backpack and meets Seller"
    assert len(activity_1qm7qck.in_flows) == 1
    assert len(activity_1qm7qck.out_flows) == 1
    assert "Flow_0oiwgjd" in {flow.id for flow in activity_1qm7qck.in_flows}
    assert "Flow_1wl740o" in {flow.id for flow in activity_1qm7qck.out_flows}

    activity_1qqx4aq = process["Activity_1qqx4aq"]
    assert activity_1qqx4aq is not None
    assert activity_1qqx4aq.name == "7a-Buyer hands cash payment to Seller"
    assert len(activity_1qqx4aq.in_flows) == 1
    assert len(activity_1qqx4aq.out_flows) == 1
    assert "Flow_0jmvvxc" in {flow.id for flow in activity_1qqx4aq.in_flows}
    assert "Flow_0znbe82" in {flow.id for flow in activity_1qqx4aq.out_flows}

    activity_1rfm4sh = process["Activity_1rfm4sh"]
    assert activity_1rfm4sh is not None
    assert activity_1rfm4sh.name == "7b-Seller hands Backpack to Buyer"
    assert len(activity_1rfm4sh.in_flows) == 1
    assert len(activity_1rfm4sh.out_flows) == 1
    assert "Flow_1y66pph" in {flow.id for flow in activity_1rfm4sh.in_flows}
    assert "Flow_1sx1rdt" in {flow.id for flow in activity_1rfm4sh.out_flows}

    # End event
    end_event_0wqympo = process["Event_0wqympo"]
    assert end_event_0wqympo is not None
    assert end_event_0wqympo.name == "Purchase Failed"
    assert len(end_event_0wqympo.in_flows) == 1
    assert "Flow_0diuub0" in {flow.id for flow in end_event_0wqympo.in_flows}

    end_event_1y6wxsp = process["Event_1y6wxsp"]
    assert end_event_1y6wxsp is not None
    assert end_event_1y6wxsp.name == "Purchase Completed"
    assert len(end_event_1y6wxsp.in_flows) == 1
    assert "Flow_1cm84v3" in {flow.id for flow in end_event_1y6wxsp.in_flows}

    # Start event
    start_event_1y8wbre = process["StartEvent_1y8wbre"]
    assert "StartEvent_1y8wbre" in process._start_states
    assert start_event_1y8wbre is not None
    assert start_event_1y8wbre.name == "Start7"
    assert len(start_event_1y8wbre.out_flows) == 1
    assert len(start_event_1y8wbre.in_flows) == 0
    assert "Flow_0oiwgjd" in {flow.id for flow in start_event_1y8wbre.out_flows}

    # Flows
    for flow_id, source_id, target_id, is_back_edge in flows_to_test:
        assert_flow(process, flow_id, source_id, target_id, is_back_edge)


def test_flow_traversal():
    bpmn: Bpmn = Bpmn.from_xml(workflow_bpmn_path)
    visitor = PromelaGenVisitor()

    assert is_successful(bpmn)

    bpmn = bpmn.unwrap()

    for node_id, node in bpmn.processes[0].all_items().items():
        node.accept = MagicMock(wraps=node.accept)

    for flow in bpmn.processes[0].flows.values():
        flow.accept = MagicMock(wraps=flow.accept)

    bpmn.accept(visitor)
    EXPECTED_CALL_COUNT = 1
    for node_id, node in bpmn.processes[0].all_items().items():
        assert node.accept.call_count == EXPECTED_CALL_COUNT

    for flow in bpmn.processes[0].flows.values():
        assert flow.accept.call_count == EXPECTED_CALL_COUNT
