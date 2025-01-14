# type: ignore
from xml.etree.ElementTree import Element
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import CwpEdge, CwpState
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor


def test_cwp_connectivity():
    builder = CwpBuilder()
    for i in range(10):
        builder.with_state(
            CwpState(Element(f"state{i}", attrib={"id": f"state{i}", "style": "test"}))
        )
    cur_let = "A"
    for i in range(9):
        builder.with_edge(
            CwpEdge(
                Element(
                    f"edge{i}",
                    attrib={
                        "id": f"edge{i}",
                    },
                ),
                chr(ord(cur_let) + i),
            ),
            f"state{i}",
            f"state{i + 1}",
        )

    builder.with_edge(
        CwpEdge(Element("edge9", attrib={"id": "edge9"}), "Z"),
        "state8",
        "state1",
    )
    cwp = builder.build().unwrap()
    visitor = CwpConnectivityVisitor()

    cwp.accept(visitor)

    assert all(state in visitor.visited for state in cwp.states.values())
    assert cwp.edges["edge9"].is_leaf
