from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.state import SymbolTable
from bpmncwpverify.error import Error
from returns.result import Result, Success, Failure
from defusedxml.ElementTree import parse
from returns.pipeline import is_successful
from returns.functions import not_


def create_promela(
    cwpfile: str, bpmnfile: str, symbol_table: SymbolTable
) -> Result[str, Error]:
    try:
        bpmn_root = parse(bpmnfile).getroot()
        cwp_root = parse(cwpfile).getroot()

        cwp = Cwp.from_xml(cwp_root, symbol_table)
        if not_(is_successful)(cwp):
            return cwp
        bpmn = Bpmn.from_xml(bpmn_root, symbol_table)
        if not_(is_successful)(bpmn):
            return bpmn

        ltl = cwp.unwrap().generate_ltl(symbol_table)
        prom = bpmn.unwrap().generate_promela()

        return Success(ltl + prom)
    except Exception as e:
        return Failure(e)


def write_promela(file_name: str, promela: str) -> Result[str, Error]:
    with open(file_name, "w") as f:
        f.write(promela)

    return Success("Successfully generated promela")
