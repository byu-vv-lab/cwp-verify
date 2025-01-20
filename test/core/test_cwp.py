# type: ignore
from xml.etree.ElementTree import Element, SubElement

from bpmncwpverify.core.error import (
    CwpMultStartStateError,
    CwpNoEndStatesError,
    CwpNoStartStateError,
    Error,
)
from returns.functions import not_
from bpmncwpverify.core.state import State
from returns.pipeline import is_successful
from bpmncwpverify.core.accessmethods.cwpmethods import from_xml


def get_root_mx_root():
    root = Element("mxfile")

    diagram = SubElement(root, "diagram")

    mx_graph_model = SubElement(diagram, "mxGraphModel")

    mx_root = SubElement(mx_graph_model, "root")

    return root, mx_root


def build_symbol_table(code):
    symbol_table = State.from_str(code)
    assert is_successful(symbol_table)
    return symbol_table.unwrap()


def add_mx_cell(mx_root, **attributes):
    SubElement(mx_root, "mxCell", attrib=attributes)


def setup_cwp_and_assert(xml_root, symbol_table, success=True, failure_message=Error):
    cwp = from_xml(xml_root, symbol_table)
    if success:
        assert is_successful(cwp)
        return cwp.unwrap()
    else:
        assert not_(is_successful)(cwp)
        assert isinstance(cwp.failure(), failure_message)
    return cwp


def test_valid_cwp_end_start_events():
    symbol_table = build_symbol_table("var x: int = 0")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="End", style="state", vertex="1")
    add_mx_cell(mx_root, id="e1", source="s1", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    cwp = setup_cwp_and_assert(root, symbol_table)
    assert len(cwp.edges) == 1
    assert cwp.start_state.id == "s1"
    assert len(cwp.states) == 1


def test_invalid_cwp_missing_start_event():
    symbol_table = build_symbol_table("var x: int = 0")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="state", style="state", vertex="1")

    setup_cwp_and_assert(
        root, symbol_table, success=False, failure_message=CwpNoStartStateError
    )


def test_invalid_cwp_not_connected():
    symbol_table = build_symbol_table("var x: int = 0")
    root, mx_root = get_root_mx_root()

    # First disconnected component
    add_mx_cell(mx_root, id="s1", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="End", style="state", vertex="1")
    add_mx_cell(mx_root, id="e1", source="s1", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    # Second disconnected component
    add_mx_cell(mx_root, id="s3", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s4", value="End", style="state", vertex="1")
    add_mx_cell(mx_root, id="e2", source="s3", target="s4", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e2", vertex="1"
    )

    setup_cwp_and_assert(
        root,
        symbol_table,
        success=False,
        failure_message=CwpMultStartStateError,
    )


def test_invalid_cwp_no_end_state():
    symbol_table = build_symbol_table("var x: int = 0")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="middle1", style="state", vertex="1")
    add_mx_cell(mx_root, id="s3", value="middle2", style="state", vertex="1")

    add_mx_cell(mx_root, id="e1", source="s1", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    add_mx_cell(mx_root, id="e2", source="s2", target="s3", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr2", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    add_mx_cell(mx_root, id="e3", source="s3", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr3", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    setup_cwp_and_assert(
        root,
        symbol_table,
        success=False,
        failure_message=CwpNoEndStatesError,
    )
