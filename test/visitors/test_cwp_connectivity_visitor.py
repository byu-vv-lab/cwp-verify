from xml.etree.ElementTree import Element
from bpmncwpverify.core.cwp import Cwp, CwpState, CwpEdge
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor


def test_cwp_connectivity():
    cwp = Cwp()
    visitor = CwpConnectivityVisitor()

    cwp.states = {
        f"state{i}": CwpState(Element(f"state{i}", attrib={"id": f"state{i}"}))
        for i in range(10)
    }
    cwp.edges = {
        f"edge{i}": CwpEdge(Element(f"edge{i}", attrib={"id": f"edge{i}"}), f"edge{i}")
        for i in range(9)
    }
    for i, edge in enumerate(cwp.edges.values()):
        edge.dest = cwp.states[f"state{i + 1}"]
        cwp.states[f"state{i}"].out_edges = [edge]

    cyclic_edge = CwpEdge(Element("edge9", attrib={"id": "edge9"}), "edge9")
    cyclic_edge.dest = cwp.states["state1"]
    cwp.states["state9"].out_edges.append(cyclic_edge)
    cwp.edges["edge9"] = cyclic_edge

    cwp.start_states = {"state0": cwp.states.pop("state0")}

    cwp.accept(visitor)

    assert all(state in visitor.visited for state in cwp.states.values())
    assert cwp.edges["edge9"].is_leaf
