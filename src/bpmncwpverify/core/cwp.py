from typing import Dict, List, Optional
from xml.etree.ElementTree import Element
from defusedxml.ElementTree import parse
import re
from bpmncwpverify.core.state import SymbolTable
from returns.result import Result
from bpmncwpverify.error import Error


class Cwp:
    def __init__(self) -> None:
        self.states: Dict[str, CwpState] = {}
        self.edges: Dict[str, CwpEdge] = {}
        self.start_states: Dict[str, CwpState] = {}
        self.end_states: List[CwpState] = []

    @staticmethod
    def from_xml(xml_file: str, symbol_table: SymbolTable) -> Result["Cwp", Error]:
        from bpmncwpverify.builder.cwp_builder import CwpBuilder

        tree = parse(xml_file)
        root = tree.getroot()
        builder = CwpBuilder(symbol_table)

        diagram = root.find("diagram")
        mx_graph_model = diagram.find("mxGraphModel")
        mx_root = mx_graph_model.find("root")
        mx_cells = mx_root.findall("mxCell")

        for itm in mx_cells:
            if itm.get("vertex"):
                builder.add_state(itm)
            elif itm.get("edge"):
                builder.add_edge(itm)

        return builder.build()

    def accept(self, visitor: "CwpVisitor") -> None:
        result = visitor.visit_cwp(self)
        if result:
            for state in self.start_states.values():
                state.accept(visitor)
        visitor.end_visit_cwp(self)

    def generate_graph_viz(self) -> None:
        from bpmncwpverify.visitors.cwp_graph_visitor import CwpGraphVizVisitor

        graph_viz_visitor = CwpGraphVizVisitor()

        self.accept(graph_viz_visitor)

        graph_viz_visitor.dot.render("graphs/cwp_graph.gv", format="png")

    def generate_ltl(self, symbol_table: SymbolTable) -> str:
        from bpmncwpverify.visitors.cwp_ltl_visitor import CwpLtlVisitor

        ltl_visitor = CwpLtlVisitor(symbol_table)

        self.accept(ltl_visitor)

        output_str = ltl_visitor.output_str

        return "".join(output_str)


class CwpState:
    def __init__(self, state: Element) -> None:
        id = state.get("id")
        name = state.get("value")
        if id is None:
            raise Exception("id not in cwp state")
        if name is None:
            name = id
        self.name: str
        self.id = id
        self.out_edges: List[CwpEdge] = []
        self.in_edges: List[CwpEdge] = []
        self.cleanup_name(name)

    def accept(self, visitor: "CwpVisitor") -> None:
        result = visitor.visit_state(self)
        if result:
            for edge in self.out_edges:
                edge.accept(visitor)
        visitor.end_visit_state(self)

    def cleanup_name(self, name: str) -> None:
        name = re.sub("[?,+=/]", "", name)
        name = re.sub("-", " ", name)
        name = re.sub(r"\s+", "_", name)

        name = re.sub("</?div>", "", name)

        self.name = name.strip()


class CwpEdge:
    # TODO: Make sure this static class variable won't modify anything weirdly

    def __init__(self, edge: Element, name: str) -> None:
        id = edge.get("id")
        if id is None:
            raise Exception("No ID for edge or no targetRef")
        self.id = id
        self.name = name
        self.expression: str
        self.parent_id: str

        self.source: Optional[CwpState] = None
        self.dest: CwpState
        self.is_leaf = False

    def set_source(self, state: CwpState) -> None:
        self.source = state

    def set_dest(self, state: CwpState) -> None:
        self.dest = state

    def accept(self, visitor: "CwpVisitor") -> None:
        if visitor.visit_edge(self):
            self.dest.accept(visitor)
        visitor.end_visit_edge(self)


class CwpVisitor:
    def visit_state(self, state: CwpState) -> bool:
        return True

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> bool:
        return True

    def end_visit_edge(self, edge: CwpEdge) -> None:
        pass

    def visit_cwp(self, model: Cwp) -> bool:
        return True

    def end_visit_cwp(self, model: Cwp) -> None:
        pass
