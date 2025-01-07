# type: ignore
from xml.etree.ElementTree import Element
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor


def test_cwp_connectivity(mocker):
    builder = CwpBuilder()
    for i in range(10):
        builder.with_state(
            Element(f"state{i}", attrib={"id": f"state{i}", "style": "test"})
        )
    for i in range(9):
        builder.with_edge(
            Element(
                f"edge{i}",
                attrib={
                    "id": f"edge{i}",
                    "target": f"state{i + 1}",
                    "source": f"state{i}",
                },
            )
        )

    builder.with_edge(
        Element("edge9", attrib={"id": "edge9", "target": "state1", "source": "state8"})
    )
    cwp = builder.build().unwrap()
    visitor = CwpConnectivityVisitor()

    cwp.accept(visitor)

    assert all(state in visitor.visited for state in cwp.states.values())
    assert cwp.edges["edge9"].is_leaf
