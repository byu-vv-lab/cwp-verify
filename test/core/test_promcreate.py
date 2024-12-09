from bpmncwpverify.core.promcreate import create_promela
from returns.result import Success, Failure
from returns.pipeline import is_successful


def test_create_promela_success(mocker):
    symbol_table = mocker.MagicMock()

    mock_parse = mocker.patch("bpmncwpverify.core.promcreate.parse")
    mock_cwp = mocker.patch("bpmncwpverify.core.promcreate.Cwp")
    mock_bpmn = mocker.patch("bpmncwpverify.core.promcreate.Bpmn")

    mock_bpmn_root = mocker.MagicMock()
    mock_cwp_root = mocker.MagicMock()
    mock_parse.side_effect = [
        mocker.MagicMock(getroot=lambda: mock_cwp_root),
        mocker.MagicMock(getroot=lambda: mock_bpmn_root),
    ]

    mock_cwp_instance = mocker.MagicMock()
    mock_bpmn_instance = mocker.MagicMock()
    mock_cwp.from_xml.return_value = Success(mock_cwp_instance)
    mock_bpmn.from_xml.return_value = Success(mock_bpmn_instance)

    mock_cwp_instance.generate_ltl.return_value = "ltl_code"
    mock_bpmn_instance.generate_promela.return_value = "promela_code"

    result = create_promela("cwp_file.xml", "bpmn_file.xml", symbol_table)

    assert is_successful(result)
    assert result.unwrap() == "ltl_codepromela_code"


def test_create_promela_failure_cwp(mocker):
    symbol_table = mocker.MagicMock()

    mock_parse = mocker.patch("bpmncwpverify.core.promcreate.parse")
    mock_cwp = mocker.patch("bpmncwpverify.core.promcreate.Cwp")

    mock_cwp_root = mocker.MagicMock()
    mock_parse.return_value.getroot.return_value = mock_cwp_root

    mock_cwp.from_xml.return_value = Failure("CWP parsing failed")

    result = create_promela("cwp_file.xml", "bpmn_file.xml", symbol_table)

    assert result.failure() == "CWP parsing failed"


def test_create_promela_failure_bpmn(mocker):
    symbol_table = mocker.MagicMock()

    mock_parse = mocker.patch("bpmncwpverify.core.promcreate.parse")
    mock_cwp = mocker.patch("bpmncwpverify.core.promcreate.Cwp")
    mock_bpmn = mocker.patch("bpmncwpverify.core.promcreate.Bpmn")

    mock_cwp_root = mocker.MagicMock()
    mock_parse.return_value.getroot.return_value = mock_cwp_root

    mock_cwp_instance = mocker.MagicMock()
    mock_cwp.from_xml.return_value = Success(mock_cwp_instance)

    mock_bpmn.from_xml.return_value = Failure("BPMN parsing failed")

    result = create_promela("cwp_file.xml", "bpmn_file.xml", symbol_table)

    assert result.failure() == "BPMN parsing failed"


def test_create_promela_exception(mocker):
    symbol_table = mocker.MagicMock()

    mocker.patch(
        "bpmncwpverify.core.promcreate.parse", side_effect=Exception("Parse error")
    )

    result = create_promela("cwp_file.xml", "bpmn_file.xml", symbol_table)

    assert result.failure().args[0] == "Parse error"
