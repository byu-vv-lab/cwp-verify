# type: ignore
from bpmncwpverify.visitors import CwpLtlVisitor, PromelaGenVisitor
from bpmncwpverify.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.state import SymbolTable
import inspect
from returns.pipeline import is_successful
from unittest.mock import MagicMock, patch, call
from bpmncwpverify.bpmn import (
    Bpmn,
    ExclusiveGatewayNode,
    ParallelGatewayNode,
    EndEvent,
    SequenceFlow,
    StartEvent,
    Process,
    Task,
)
import os


flows_to_test = {
    "Flow_08e7qxg": {
        "source": "Gateway_1pm4ghz",
        "dest": "Gateway_12r266n",
        "is_leaf": True,
    },
    "Flow_1wl740o": {
        "source": "Activity_1qm7qck",
        "dest": "Gateway_12r266n",
        "is_leaf": False,
    },
    "Flow_1kx5xjv": {
        "source": "Gateway_12r266n",
        "dest": "Activity_1unsjkg",
        "is_leaf": False,
    },
    "Flow_13xpfx7": {
        "source": "Gateway_12r266n",
        "dest": "Activity_1t579ox",
        "is_leaf": False,
    },
    "Flow_1oezfcg": {
        "source": "Activity_1unsjkg",
        "dest": "Gateway_0s1i42o",
        "is_leaf": False,
    },
    "Flow_14s5onf": {
        "source": "Activity_1t579ox",
        "dest": "Gateway_0s1i42o",
        "is_leaf": True,
    },
    "Flow_0feadgd": {
        "source": "Gateway_0s1i42o",
        "dest": "Gateway_1pm4ghz",
        "is_leaf": False,
    },
    "Flow_127sd29": {
        "source": "Activity_1bckz5y",
        "dest": "Gateway_1pm4ghz",
        "is_leaf": True,
    },
    "Flow_00oxr95": {
        "source": "Activity_1mktua2",
        "dest": "Gateway_1pm4ghz",
        "is_leaf": True,
    },
    "Flow_0yqye0v": {
        "source": "Gateway_1pm4ghz",
        "dest": "Activity_0a5xzqf",
        "is_leaf": False,
    },
    "Flow_0diuub0": {
        "source": "Gateway_1pm4ghz",
        "dest": "Event_0wqympo",
        "is_leaf": False,
    },
    "Flow_0q6dz8p": {
        "source": "Gateway_1pm4ghz",
        "dest": "Activity_1bckz5y",
        "is_leaf": False,
    },
    "Flow_0koz64j": {
        "source": "Gateway_1pm4ghz",
        "dest": "Activity_1mktua2",
        "is_leaf": False,
    },
    "Flow_0ct87dl": {
        "source": "Activity_0a5xzqf",
        "dest": "Gateway_000lymc",
        "is_leaf": False,
    },
    "Flow_0jmvvxc": {
        "source": "Gateway_000lymc",
        "dest": "Activity_1qqx4aq",
        "is_leaf": False,
    },
    "Flow_1y66pph": {
        "source": "Gateway_000lymc",
        "dest": "Activity_1rfm4sh",
        "is_leaf": False,
    },
    "Flow_0znbe82": {
        "source": "Activity_1qqx4aq",
        "dest": "Gateway_0cy7rs7",
        "is_leaf": False,
    },
    "Flow_1sx1rdt": {
        "source": "Activity_1rfm4sh",
        "dest": "Gateway_0cy7rs7",
        "is_leaf": True,
    },
    "Flow_1cm84v3": {
        "source": "Gateway_0cy7rs7",
        "dest": "Event_1y6wxsp",
        "is_leaf": False,
    },
    "Flow_0oiwgjd": {
        "source": "StartEvent_1y8wbre",
        "dest": "Activity_1qm7qck",
        "is_leaf": False,
    },
}

element_mapping = {
    "Gateway_12r266n": {
        "class_name": ParallelGatewayNode,
        "id": "Gateway_12r266n",
        "name": "both",
        "in_flows": ["Flow_08e7qxg", "Flow_1wl740o"],
        "out_flows": ["Flow_1kx5xjv", "Flow_13xpfx7"],
    },
    "Gateway_0s1i42o": {
        "class_name": ParallelGatewayNode,
        "id": "Gateway_0s1i42o",
        "name": "end both",
        "in_flows": ["Flow_14s5onf", "Flow_1oezfcg"],
        "out_flows": ["Flow_0feadgd"],
    },
    "Gateway_1pm4ghz": {
        "class_name": ExclusiveGatewayNode,
        "id": "Gateway_1pm4ghz",
        "name": "payment and terms agreed",
        "in_flows": ["Flow_0feadgd", "Flow_127sd29", "Flow_00oxr95"],
        "out_flows": [
            "Flow_0yqye0v",
            "Flow_0diuub0",
            "Flow_0q6dz8p",
            "Flow_0koz64j",
            "Flow_08e7qxg",
        ],
    },
    "Gateway_000lymc": {
        "class_name": ParallelGatewayNode,
        "id": "Gateway_000lymc",
        "name": "both1",
        "in_flows": ["Flow_0ct87dl"],
        "out_flows": ["Flow_0jmvvxc", "Flow_1y66pph"],
    },
    "Gateway_0cy7rs7": {
        "class_name": ParallelGatewayNode,
        "id": "Gateway_0cy7rs7",
        "name": "end both1",
        "in_flows": ["Flow_1sx1rdt", "Flow_0znbe82"],
        "out_flows": ["Flow_1cm84v3"],
    },
    "Activity_1unsjkg": {
        "class_name": Task,
        "name": "2-Buyer and Seller negotiate terms",
        "id": "Activity_1unsjkg",
        "in_flows": ["Flow_1kx5xjv"],
        "out_flows": ["Flow_1oezfcg"],
    },
    "Activity_1t579ox": {
        "class_name": Task,
        "name": "3-Buyer and Seller negotiate price",
        "id": "Activity_1t579ox",
        "in_flows": ["Flow_13xpfx7"],
        "out_flows": ["Flow_14s5onf"],
    },
    "Activity_1qm7qck": {
        "class_name": Task,
        "name": "1-Buyer sees desired backpack and meets Seller",
        "id": "Activity_1qm7qck",
        "in_flows": ["Flow_0oiwgjd"],
        "out_flows": ["Flow_1wl740o"],
    },
    "Activity_1qqx4aq": {
        "class_name": Task,
        "name": "7a-Buyer hands cash payment to Seller",
        "id": "Activity_1qqx4aq",
        "in_flows": ["Flow_0jmvvxc"],
        "out_flows": ["Flow_0znbe82"],
    },
    "Activity_1rfm4sh": {
        "class_name": Task,
        "name": "7b-Seller hands Backpack to Buyer",
        "id": "Activity_1rfm4sh",
        "in_flows": ["Flow_1y66pph"],
        "out_flows": ["Flow_1sx1rdt"],
    },
    "Activity_1bckz5y": {
        "class_name": Task,
        "id": "Activity_1bckz5y",
        "name": "4-Buyer and Seller repeat price negotiation",
        "in_flows": ["Flow_0q6dz8p"],
        "out_flows": ["Flow_127sd29"],
    },
    "Activity_1mktua2": {
        "class_name": Task,
        "id": "Activity_1bckz5y",
        "name": "5-Buyer and Seller repeat terms negotiation",
        "in_flows": ["Flow_0koz64j"],
        "out_flows": ["Flow_00oxr95"],
    },
    "Activity_0a5xzqf": {
        "class_name": Task,
        "id": "Activity_0a5xzqf",
        "name": "6-Buyer and Seller shake hands",
        "in_flows": ["Flow_0yqye0v"],
        "out_flows": ["Flow_0ct87dl"],
    },
    "Event_0wqympo": {
        "class_name": EndEvent,
        "id": "Event_0wqympo",
        "name": "Purchase Failed",
        "in_flows": ["Flow_0diuub0"],
        "out_flows": [],
    },
    "Event_1y6wxsp": {
        "class_name": EndEvent,
        "id": "Event_1y6wxsp",
        "name": "Purchase Completed",
        "in_flows": ["Flow_1cm84v3"],
        "out_flows": [],
    },
    "StartEvent_1y8wbre": {
        "class_name": StartEvent,
        "id": "StartEvent_1y8wbre",
        "name": "Start7",
        "in_flows": [],
        "out_flows": ["Flow_0oiwgjd"],
    },
}


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
    bpmn = Bpmn()

    process_id = "Process_1xbpt9j"
    mock_element = MagicMock()
    mock_element.get.side_effect = lambda var: {
        "id": process_id,
    }[var]
    bpmn.processes = {"Process_1xbpt9j": Process(mock_element)}

    for id, attributes in element_mapping.items():
        mock_element = MagicMock()
        mock_element.get.side_effect = lambda var: {
            "id": id,
        }[var]

        new_element = attributes["class_name"](mock_element)
        for attr, value in attributes.items():
            if attr != "class_name":
                setattr(new_element, attr, value)

        bpmn.processes[process_id]._elements[id] = new_element

    for flow_id, flow in flows_to_test.items():
        mock_element = MagicMock()
        mock_element.get.side_effect = lambda var: {
            "id": id,
        }[var]

        new_element = SequenceFlow(mock_element)
        new_element.source_node = bpmn.processes[process_id]._elements[flow["source"]]
        new_element.target_node = bpmn.processes[process_id]._elements[flow["dest"]]
        new_element.is_leaf = flow["is_leaf"]
        bpmn.processes[process_id]._flows[flow_id] = new_element

    return bpmn


# List of flows with their source and target node IDs
current_directory = os.path.dirname(os.path.abspath(__file__))


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

    for element_id, bpmn_element in element_mapping.items():
        cur_element = process[element_id]
        assert cur_element.id == element_id
        assert cur_element.name == bpmn_element.get("name")
        assert {flow.id for flow in cur_element.in_flows} == {
            flow for flow in bpmn_element["in_flows"]
        }
        assert {flow.id for flow in cur_element.out_flows} == {
            flow for flow in bpmn_element["out_flows"]
        }

    # Flows
    for flow_id, values in flows_to_test.items():
        assert_flow(
            process, flow_id, values["source"], values["dest"], values["is_leaf"]
        )


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


def test_cwp_write_init_states():
    with patch.object(CwpLtlVisitor, "write_line") as mock_write:
        symbol_table = MagicMock()
        instance = CwpLtlVisitor(symbol_table)

        instance.cwp = type("", (), {})()
        instance.cwp.states = {
            "state1": type("", (), {"name": "init_state1"}),
            "state2": type("", (), {"name": "normal_state2"}),
        }

        instance.write_init_states()

        expected_calls = [
            call("\n\n//**********STATE VARIABLE DECLARATION************//"),
            call("bit init_state1 = 1"),
            call("bit normal_state2 = 0"),
        ]
        mock_write.assert_has_calls(expected_calls)


def test_cwp_write_exists_properties():
    state = MagicMock()
    state.name = "TestState"

    with patch.object(CwpLtlVisitor, "write_line") as mock_write:
        symbol_table = MagicMock()
        visitor = CwpLtlVisitor(symbol_table)
        visitor.property_list = []

        visitor.write_exists_property(state)

        assert "{}Exists".format(state.name) in visitor.property_list

        expected_call = call(
            "ltl TestStateExists {(fair implies (always (! TestState)))}"
        )

        mock_write.assert_has_calls([expected_call])


def test_cwp_mutex_property():
    state = MagicMock()
    state.name = "TestState"

    dummy_cwp = type("DummyCwp", (), {})()
    dummy_cwp.states = {
        "TestState": state,
        "OtherState1": MagicMock(name="OtherState1"),
        "OtherState2": MagicMock(name="OtherState2"),
        "OtherState3": MagicMock(name="OtherState3"),
    }
    dummy_cwp.states["OtherState1"].name = "OtherState1"
    dummy_cwp.states["OtherState2"].name = "OtherState2"
    dummy_cwp.states["OtherState3"].name = "OtherState3"

    with patch.object(CwpLtlVisitor, "write_line") as mock_write:
        symbol_table = MagicMock()
        visitor = CwpLtlVisitor(symbol_table)
        visitor.property_list = []
        visitor.cwp = dummy_cwp
        visitor.tab = 0

        visitor.write_mutex_property(state)

        assert "{}Mutex".format(state.name) in visitor.property_list

        expected_calls = [
            call("ltl TestStateMutex {"),
            call("("),
            call("always ("),
            call("TestState implies ("),
            call("TestState"),
            call(
                "&& (! OtherState1)\n\t\t\t\t&& (! OtherState2)\n\t\t\t\t&& (! OtherState3)"
            ),
            call(")"),
            call(")"),
            call(")"),
            call("}"),
        ]
        mock_write.assert_has_calls(expected_calls)

        assert visitor.tab == 0
