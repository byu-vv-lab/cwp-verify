# type: ignore
from bpmncwpverify.visitors import PromelaGenVisitor
from bpmncwpverify.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.state import SymbolTable
import inspect
from returns.pipeline import is_successful
from unittest.mock import MagicMock
from bpmncwpverify.bpmn import (
    Bpmn,
    EndEvent,
    ExclusiveGatewayNode,
    ParallelGatewayNode,
    StartEvent,
    Task,
)
import os


def generate_mock_cwp():
    cwp = Cwp()

    edges_attr = [
        {
            "id": "-KwNMsgkI5d_Im8GLqs--2",
            "name": "EdgeA",
            "source": "BR_N0rfb46-SebA63Yol-1",
            "is_leaf": False,
            "dest": "-KwNMsgkI5d_Im8GLqs--1",
            "expression": "terms != pending || paymentOffered != pendingPayment",
            "parent_id": "-KwNMsgkI5d_Im8GLqs--5",
        },
        {
            "id": "BR_N0rfb46-SebA63Yol-10",
            "name": "EdgeB",
            "source": "BR_N0rfb46-SebA63Yol-8",
            "is_leaf": False,
            "dest": "BR_N0rfb46-SebA63Yol-7",
            "expression": "paymentOwner == sellerName && backpackOwner == buyerName",
            "parent_id": "BR_N0rfb46-SebA63Yol-21",
        },
        {
            "id": "-KwNMsgkI5d_Im8GLqs--3",
            "name": "EdgeC",
            "source": "-KwNMsgkI5d_Im8GLqs--1",
            "is_leaf": False,
            "dest": "BR_N0rfb46-SebA63Yol-8",
            "expression": "terms == agreed && paymentOffered == paymentAmount",
            "parent_id": "-KwNMsgkI5d_Im8GLqs--7",
        },
        {
            "id": "-KwNMsgkI5d_Im8GLqs--4",
            "name": "EdgeD",
            "source": "-KwNMsgkI5d_Im8GLqs--1",
            "is_leaf": False,
            "dest": "BR_N0rfb46-SebA63Yol-6",
            "expression": "terms == noRetry || paymentOffered == noRetryPayment",
            "parent_id": "-KwNMsgkI5d_Im8GLqs--6",
        },
        {
            "id": "-KwNMsgkI5d_Im8GLqs--8",
            "name": "EdgeE",
            "source": None,
            "is_leaf": False,
            "dest": "BR_N0rfb46-SebA63Yol-1",
            "expression": "paymentOwner == buyerName && backpackOwner == sellerName",
            "parent_id": "-KwNMsgkI5d_Im8GLqs--9",
        },
    ]

    states_attr = [
        {
            "id": "BR_N0rfb46-SebA63Yol-1",
            "out_edges": ["-KwNMsgkI5d_Im8GLqs--2"],
            "in_edges": ["-KwNMsgkI5d_Im8GLqs--8"],
            "name": "Init_Purchase_Pending",
        },
        {
            "id": "BR_N0rfb46-SebA63Yol-6",
            "out_edges": [],
            "in_edges": ["-KwNMsgkI5d_Im8GLqs--4"],
            "name": "Purchase_Failed",
        },
        {
            "id": "BR_N0rfb46-SebA63Yol-7",
            "out_edges": [],
            "in_edges": ["BR_N0rfb46-SebA63Yol-10"],
            "name": "Ownerships_Switched",
        },
        {
            "id": "BR_N0rfb46-SebA63Yol-8",
            "out_edges": ["BR_N0rfb46-SebA63Yol-10"],
            "in_edges": ["-KwNMsgkI5d_Im8GLqs--3"],
            "name": "Purchase_Agreed",
        },
        {
            "id": "-KwNMsgkI5d_Im8GLqs--1",
            "out_edges": ["-KwNMsgkI5d_Im8GLqs--3", "-KwNMsgkI5d_Im8GLqs--4"],
            "in_edges": ["-KwNMsgkI5d_Im8GLqs--2"],
            "name": "Negotiations",
        },
    ]

    start_edge = "-KwNMsgkI5d_Im8GLqs--8"

    states = {}
    edges = {}
    for edge in edges_attr:
        new_edge = CwpEdge(MagicMock(), edge["name"])
        for key, val in edge.items():
            setattr(new_edge, key, val)
        edges[edge["id"]] = new_edge

    for state in states_attr:
        mock_element = MagicMock()
        mock_element.get.side_effect = lambda var: {
            "id": state["id"],
            "value": state["name"],
        }[var]
        new_state = CwpState(mock_element)
        for key, val in state.items():
            if key == "out_edges" or key == "in_edges":
                for idx in range(len(val)):
                    val[idx] = edges[val[idx]]
            setattr(new_state, key, val)
        states[state["id"]] = new_state

    for edge in edges_attr:
        edges[edge["id"]].source = (
            states[edge["source"]] if edge["source"] is not None else None
        )
        edges[edge["id"]].dest = (
            states[edge["dest"]] if edge["dest"] is not None else None
        )

    cwp.edges = edges
    cwp.states = states
    cwp.start_edge = edges[start_edge]
    cwp.end_states = [itm for itm in states.values() if len(itm.out_edges) == 0]

    return cwp


def generate_mock_bpmn():
    pass


# List of flows with their source and target node IDs
current_directory = os.path.dirname(os.path.abspath(__file__))

flows_to_test = [
    ("Flow_08e7qxg", "Gateway_1pm4ghz", "Gateway_12r266n", True),
    ("Flow_1wl740o", "Activity_1qm7qck", "Gateway_12r266n", False),
    ("Flow_1kx5xjv", "Gateway_12r266n", "Activity_1unsjkg", False),
    ("Flow_13xpfx7", "Gateway_12r266n", "Activity_1t579ox", False),
    ("Flow_1oezfcg", "Activity_1unsjkg", "Gateway_0s1i42o", False),
    ("Flow_14s5onf", "Activity_1t579ox", "Gateway_0s1i42o", True),
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
    ("Flow_1sx1rdt", "Activity_1rfm4sh", "Gateway_0cy7rs7", True),
    ("Flow_1cm84v3", "Gateway_0cy7rs7", "Event_1y6wxsp", False),
    ("Flow_0oiwgjd", "StartEvent_1y8wbre", "Activity_1qm7qck", False),
]


def assert_flow(process, flow_id, source_id, target_id, is_leaf):
    flow = process[flow_id]
    assert flow is not None, f"Flow {flow_id} not found"
    assert flow.is_leaf == is_leaf
    assert flow.source_node.id == source_id, f"Flow {flow_id} source node mismatch"
    assert flow.target_node.id == target_id, f"Flow {flow_id} target node mismatch"


def test_xml_parser():
    workflow_bpmn_path = os.path.join(current_directory, "resources", "workflow.bpmn")
    bpmn: Bpmn = Bpmn.from_xml(workflow_bpmn_path)

    assert is_successful(bpmn)

    bpmn = bpmn.unwrap()

    assert len(bpmn.processes) == 1

    process = bpmn.processes["Process_1xbpt9j"]

    # Gateways
    gateway_12r266n = process["Gateway_12r266n"]
    assert isinstance(gateway_12r266n, ParallelGatewayNode)
    assert gateway_12r266n is not None
    assert gateway_12r266n.id == "Gateway_12r266n"
    assert gateway_12r266n.name == "both"
    assert len(gateway_12r266n.in_flows) == 2
    assert len(gateway_12r266n.out_flows) == 2
    assert "Flow_08e7qxg" in {flow.id for flow in gateway_12r266n.in_flows}
    assert "Flow_1wl740o" in {flow.id for flow in gateway_12r266n.in_flows}
    assert "Flow_1kx5xjv" in {flow.id for flow in gateway_12r266n.out_flows}
    assert "Flow_13xpfx7" in {flow.id for flow in gateway_12r266n.out_flows}

    gateway_0s1i42o = process["Gateway_0s1i42o"]
    assert isinstance(gateway_0s1i42o, ParallelGatewayNode)
    assert gateway_0s1i42o is not None
    assert gateway_0s1i42o.id == "Gateway_0s1i42o"
    assert gateway_0s1i42o.name.lower() == "end both"
    assert len(gateway_0s1i42o.in_flows) == 2
    assert len(gateway_0s1i42o.out_flows) == 1
    assert "Flow_14s5onf" in {flow.id for flow in gateway_0s1i42o.in_flows}
    assert "Flow_1oezfcg" in {flow.id for flow in gateway_0s1i42o.in_flows}
    assert "Flow_0feadgd" in {flow.id for flow in gateway_0s1i42o.out_flows}

    gateway_1pm4ghz = process["Gateway_1pm4ghz"]
    assert isinstance(gateway_1pm4ghz, ExclusiveGatewayNode)
    assert gateway_1pm4ghz is not None
    assert gateway_1pm4ghz.id == "Gateway_1pm4ghz"
    assert gateway_1pm4ghz.name.lower() == "payment and terms agreed"
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
    assert isinstance(gateway_000lymc, ParallelGatewayNode)
    assert gateway_000lymc is not None
    assert gateway_000lymc.id == "Gateway_000lymc"
    assert gateway_000lymc.name.lower() == "both1"
    assert len(gateway_000lymc.in_flows) == 1
    assert len(gateway_000lymc.out_flows) == 2
    assert "Flow_0ct87dl" in {flow.id for flow in gateway_000lymc.in_flows}
    assert "Flow_0jmvvxc" in {flow.id for flow in gateway_000lymc.out_flows}
    assert "Flow_1y66pph" in {flow.id for flow in gateway_000lymc.out_flows}

    gateway_0cy7rs7 = process["Gateway_0cy7rs7"]
    assert isinstance(gateway_0cy7rs7, ParallelGatewayNode)
    assert gateway_0cy7rs7 is not None
    assert gateway_0cy7rs7.id == "Gateway_0cy7rs7"
    assert gateway_0cy7rs7.name == "end both1"
    assert len(gateway_0cy7rs7.in_flows) == 2
    assert len(gateway_0cy7rs7.out_flows) == 1
    assert "Flow_1sx1rdt" in {flow.id for flow in gateway_0cy7rs7.in_flows}
    assert "Flow_0znbe82" in {flow.id for flow in gateway_0cy7rs7.in_flows}
    assert "Flow_1cm84v3" in {flow.id for flow in gateway_0cy7rs7.out_flows}

    # Activities
    activity_1unsjkg = process["Activity_1unsjkg"]
    assert isinstance(activity_1unsjkg, Task)
    assert activity_1unsjkg is not None
    assert activity_1unsjkg.id == "Activity_1unsjkg"
    assert len(activity_1unsjkg.in_flows) == 1
    assert len(activity_1unsjkg.out_flows) == 1
    assert "Flow_1kx5xjv" in {flow.id for flow in activity_1unsjkg.in_flows}
    assert "Flow_1oezfcg" in {flow.id for flow in activity_1unsjkg.out_flows}

    activity_1t579ox = process["Activity_1t579ox"]
    assert isinstance(activity_1t579ox, Task)
    assert activity_1t579ox is not None
    assert activity_1t579ox.id == "Activity_1t579ox"
    assert len(activity_1t579ox.in_flows) == 1
    assert len(activity_1t579ox.out_flows) == 1
    assert "Flow_13xpfx7" in {flow.id for flow in activity_1t579ox.in_flows}
    assert "Flow_14s5onf" in {flow.id for flow in activity_1t579ox.out_flows}

    activity_1qm7qck = process["Activity_1qm7qck"]
    assert isinstance(activity_1qm7qck, Task)
    assert activity_1qm7qck is not None
    assert activity_1qm7qck.id == "Activity_1qm7qck"
    assert len(activity_1qm7qck.in_flows) == 1
    assert len(activity_1qm7qck.out_flows) == 1
    assert "Flow_0oiwgjd" in {flow.id for flow in activity_1qm7qck.in_flows}
    assert "Flow_1wl740o" in {flow.id for flow in activity_1qm7qck.out_flows}

    activity_1qqx4aq = process["Activity_1qqx4aq"]
    assert isinstance(activity_1qqx4aq, Task)
    assert activity_1qqx4aq is not None
    assert activity_1qqx4aq.id == "Activity_1qqx4aq"
    assert len(activity_1qqx4aq.in_flows) == 1
    assert len(activity_1qqx4aq.out_flows) == 1
    assert "Flow_0jmvvxc" in {flow.id for flow in activity_1qqx4aq.in_flows}
    assert "Flow_0znbe82" in {flow.id for flow in activity_1qqx4aq.out_flows}

    activity_1rfm4sh = process["Activity_1rfm4sh"]
    assert isinstance(activity_1rfm4sh, Task)
    assert activity_1rfm4sh is not None
    assert activity_1rfm4sh.id == "Activity_1rfm4sh"
    assert len(activity_1rfm4sh.in_flows) == 1
    assert len(activity_1rfm4sh.out_flows) == 1
    assert "Flow_1y66pph" in {flow.id for flow in activity_1rfm4sh.in_flows}
    assert "Flow_1sx1rdt" in {flow.id for flow in activity_1rfm4sh.out_flows}

    # End event
    end_event_0wqympo = process["Event_0wqympo"]
    assert isinstance(end_event_0wqympo, EndEvent)
    assert end_event_0wqympo is not None
    assert end_event_0wqympo.id == "Event_0wqympo"
    assert end_event_0wqympo.name == "Purchase Failed"
    assert len(end_event_0wqympo.in_flows) == 1
    assert "Flow_0diuub0" in {flow.id for flow in end_event_0wqympo.in_flows}

    end_event_1y6wxsp = process["Event_1y6wxsp"]
    assert isinstance(end_event_1y6wxsp, EndEvent)
    assert end_event_1y6wxsp is not None
    assert end_event_1y6wxsp.id == "Event_1y6wxsp"
    assert end_event_1y6wxsp.name == "Purchase Completed"
    assert len(end_event_1y6wxsp.in_flows) == 1
    assert "Flow_1cm84v3" in {flow.id for flow in end_event_1y6wxsp.in_flows}

    # Start event
    start_event_1y8wbre = process["StartEvent_1y8wbre"]
    assert isinstance(start_event_1y8wbre, StartEvent)
    assert "StartEvent_1y8wbre" in process._start_states
    assert start_event_1y8wbre is not None
    assert start_event_1y8wbre.id == "StartEvent_1y8wbre"
    assert start_event_1y8wbre.name == "Start7"
    assert len(start_event_1y8wbre.out_flows) == 1
    assert len(start_event_1y8wbre.in_flows) == 0
    assert "Flow_0oiwgjd" in {flow.id for flow in start_event_1y8wbre.out_flows}

    # Flows
    for flow_id, source_id, target_id, is_leaf in flows_to_test:
        assert_flow(process, flow_id, source_id, target_id, is_leaf)


def test_bpmn_negotiation_example():
    workflow_bpmn_path = os.path.join(
        current_directory, "resources", "negotiation_workflow.bpmn"
    )
    bpmn: Bpmn = Bpmn.from_xml(workflow_bpmn_path)

    assert is_successful(bpmn)

    bpmn = bpmn.unwrap()

    assert len(bpmn.processes) == 2  # Adjusted for two processes in the BPMN

    message_flow_1 = bpmn.inter_process_msgs["Flow_0kf1yna"]
    message_flow_2 = bpmn.inter_process_msgs["Flow_12pmiyg"]

    assert (
        message_flow_1.source_node == bpmn.id_to_element["Event_077ds7t"]
        and message_flow_1.target_node == bpmn.id_to_element["Event_12hk9dy"]
    )
    assert (
        message_flow_2.source_node == bpmn.id_to_element["Event_1bjnzhv"]
        and message_flow_2.target_node == bpmn.id_to_element["Event_1bjiart"]
    )

    # Process definitions
    process_seller = bpmn.processes["Process_0rj28v9"]
    process_buyer = bpmn.processes["Process_1s89g0k"]

    # Check Seller Process details
    assert process_seller.id == "Process_0rj28v9"

    # Gateways in the Seller Process
    gateway_19rrbaq = process_seller["Gateway_19rrbaq"]
    assert gateway_19rrbaq is not None
    assert len(gateway_19rrbaq.in_flows) == 1
    assert len(gateway_19rrbaq.out_flows) == 3
    assert "Flow_148fc62" in {flow.id for flow in gateway_19rrbaq.in_flows}
    assert "Flow_1oqcb06" in {flow.id for flow in gateway_19rrbaq.out_flows}
    assert "Flow_06pe7pl" in {flow.id for flow in gateway_19rrbaq.out_flows}
    assert "Flow_02ll0st" in {flow.id for flow in gateway_19rrbaq.out_flows}

    gateway_0u0isqu = process_seller["Gateway_0u0isqu"]
    assert gateway_0u0isqu is not None
    assert len(gateway_0u0isqu.in_flows) == 2
    assert len(gateway_0u0isqu.out_flows) == 1
    assert "Flow_0dz3g7n" in {flow.id for flow in gateway_0u0isqu.in_flows}
    assert "Flow_0dzr23i" in {flow.id for flow in gateway_0u0isqu.in_flows}
    assert "Flow_1s2qyvr" in {flow.id for flow in gateway_0u0isqu.out_flows}

    # Activity in the Seller Process
    activity_1scn3b9 = process_seller["Activity_1scn3b9"]
    assert activity_1scn3b9 is not None
    assert len(activity_1scn3b9.in_flows) == 1
    assert len(activity_1scn3b9.out_flows) == 1
    assert "Flow_1oqcb06" in {flow.id for flow in activity_1scn3b9.in_flows}
    assert "Flow_118z6yg" in {flow.id for flow in activity_1scn3b9.out_flows}

    # Check Buyer Process details
    assert process_buyer.id == "Process_1s89g0k"

    # Gateways in the Buyer Process
    gateway_11xlm5f = process_buyer["Gateway_11xlm5f"]
    assert gateway_11xlm5f is not None
    assert len(gateway_11xlm5f.in_flows) == 1
    assert len(gateway_11xlm5f.out_flows) == 2
    assert "Flow_1fn0zow" in {flow.id for flow in gateway_11xlm5f.in_flows}
    assert "Flow_1st238k" in {flow.id for flow in gateway_11xlm5f.out_flows}
    assert "Flow_1ovjxev" in {flow.id for flow in gateway_11xlm5f.out_flows}

    # Activity in the Buyer Process
    activity_0i65ruv = process_buyer["Activity_0i65ruv"]
    assert activity_0i65ruv is not None
    assert len(activity_0i65ruv.in_flows) == 1
    assert len(activity_0i65ruv.out_flows) == 1
    assert "Flow_0otejpj" in {flow.id for flow in activity_0i65ruv.in_flows}
    assert "Flow_13sbxtx" in {flow.id for flow in activity_0i65ruv.out_flows}

    # Flows
    flows_to_test = {
        "Process_0rj28v9": [  # Seller Process
            ("Flow_1s2qyvr", "Gateway_0u0isqu", "Event_1bjiart", False),
            ("Flow_148fc62", "Event_1bjiart", "Gateway_19rrbaq", False),
            ("Flow_1oqcb06", "Gateway_19rrbaq", "Activity_1scn3b9", False),
            ("Flow_06pe7pl", "Gateway_19rrbaq", "Activity_1lot59i", False),
            ("Flow_02ll0st", "Gateway_19rrbaq", "Gateway_0inpbbk", True),
            ("Flow_118z6yg", "Activity_1scn3b9", "Gateway_0inpbbk", False),
            ("Flow_10b3hfw", "Activity_1lot59i", "Gateway_18cjano", False),
            ("Flow_1ijs0v1", "Gateway_18cjano", "Event_0cdrzde", False),
            ("Flow_009ceeg", "Gateway_18cjano", "Event_1qy951k", False),
            ("Flow_0dz3g7n", "StartEvent_1", "Gateway_0u0isqu", False),
            ("Flow_1yplman", "Gateway_0inpbbk", "Event_077ds7t", False),
            ("Flow_0dzr23i", "Event_077ds7t", "Gateway_0u0isqu", True),
        ],
        "Process_1s89g0k": [  # Buyer Process
            ("Flow_0cathr3", "Event_1qaneqr", "Activity_00vetyp", False),
            ("Flow_0otejpj", "Gateway_1rw6qx7", "Activity_0i65ruv", False),
            ("Flow_13sbxtx", "Activity_0i65ruv", "Gateway_0yn154w", True),
            ("Flow_03hgyjm", "Gateway_1rw6qx7", "Activity_1fb434c", False),
            ("Flow_1fn0zow", "Activity_1fb434c", "Gateway_11xlm5f", False),
            ("Flow_01rjqfb", "Event_1bjnzhv", "Event_12hk9dy", False),
            ("Flow_14lc2wt", "Event_12hk9dy", "Gateway_1rw6qx7", False),
            ("Flow_1st238k", "Gateway_11xlm5f", "Event_0fouhsy", False),
            ("Flow_1ovjxev", "Gateway_11xlm5f", "Event_14cr1sx", False),
            ("Flow_1x38j0r", "Gateway_1rw6qx7", "Gateway_0yn154w", True),
            ("Flow_093mxld", "Activity_00vetyp", "Gateway_0yn154w", False),
            ("Flow_0cam1do", "Gateway_0yn154w", "Event_1bjnzhv", False),
        ],
    }

    for process_id, process in bpmn.processes.items():
        for flow_id, source_id, target_id, is_leaf in flows_to_test[process_id]:
            assert_flow(process, flow_id, source_id, target_id, is_leaf)


def test_flow_traversal():
    workflow_bpmn_path = os.path.join(current_directory, "resources", "workflow.bpmn")
    bpmn: Bpmn = Bpmn.from_xml(workflow_bpmn_path)

    visitor = PromelaGenVisitor()
    process_id = "Process_1xbpt9j"

    for name, method in inspect.getmembers(visitor, predicate=inspect.ismethod):
        signature = inspect.signature(method)

        return_annotation = signature.return_annotation

        if return_annotation is bool:
            setattr(visitor, name, MagicMock(return_value=True))
        else:
            setattr(visitor, name, MagicMock(return_value=None))

    assert is_successful(bpmn)

    bpmn = bpmn.unwrap()

    for node_id, node in bpmn.processes[process_id].all_items().items():
        node.accept = MagicMock(wraps=node.accept)

    for flow in bpmn.processes[process_id].get_flows().values():
        flow.accept = MagicMock(wraps=flow.accept)

    bpmn.accept(visitor)
    EXPECTED_CALL_COUNT = (
        1  # We expect each accept method of each element to be called once
    )
    for node_id, node in bpmn.processes[process_id].all_items().items():
        assert node.accept.call_count == EXPECTED_CALL_COUNT

    for flow in bpmn.processes[process_id].get_flows().values():
        assert flow.accept.call_count == EXPECTED_CALL_COUNT


def test_promela_generation():
    workflow_bpmn_path = os.path.join(
        current_directory, "resources", "negotiation_workflow.bpmn"
    )
    bpmn: Bpmn = Bpmn.from_xml(workflow_bpmn_path)

    assert is_successful(bpmn)

    bpmn = bpmn.unwrap()

    output_str: str = bpmn.generate_promela()

    with open("promela.pml", "w") as f:
        f.write(output_str)


def test_cwp_model_gen():
    cwp_path = os.path.join(current_directory, "resources", "cwp.xml")
    cwp = Cwp.from_xml(cwp_path)

    assert is_successful(cwp)

    cwp = cwp.unwrap()

    mapping = {
        "paymentOwner == buyerName && backpackOwner == sellerName": "Init_Purchase_Pending",
        "terms == noRetry || paymentOffered == noRetryPayment": "Purchase_Failed",
        "terms == agreed && paymentOffered == paymentAmount": "Purchase_Agreed",
        "paymentOwner == sellerName && backpackOwner == buyerName": "Ownerships_Switched",
        "terms != pending || paymentOffered != pendingPayment": "Negotiations",
    }

    for itm in cwp.edges.values():
        assert itm.expression in mapping
        assert itm.dest.name == mapping[itm.expression]


def test_cwp_ltl_gen():
    cwp_path = os.path.join(current_directory, "resources", "cwp.xml")
    cwp = Cwp.from_xml(cwp_path)

    assert is_successful(cwp)

    cwp = cwp.unwrap()

    state_path = os.path.join(current_directory, "resources", "negotiation_state.txt")

    with open(state_path, "r") as r:
        file_content = r.read()

    symbol_table = SymbolTable.build(file_content)

    if not is_successful(symbol_table):
        raise Exception("building symbol table failed")

    output_str = cwp.generate_ltl(symbol_table.unwrap())

    with open("cwp.pml", "w") as f:
        f.write(output_str)


def test_promela_and_ltl():
    cwp_path = os.path.join(current_directory, "resources", "cwp.xml")
    cwp = Cwp.from_xml(cwp_path)

    assert is_successful(cwp)

    cwp = cwp.unwrap()

    state_path = os.path.join(current_directory, "resources", "negotiation_state.txt")

    with open(state_path, "r") as r:
        file_content = r.read()

    symbol_table = SymbolTable.build(file_content)

    if not is_successful(symbol_table):
        raise Exception("building symbol table failed")

    output_str = cwp.generate_ltl(symbol_table.unwrap())

    with open("promela_ltl.pml", "w") as f:
        f.write(output_str)


def test_cwp_thing():
    generate_mock_cwp()
