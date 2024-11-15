from bpmncwpverify.bpmn import Activity, SequenceFlow, MessageFlow
from bpmncwpverify.visitors import PromelaGenVisitor
import pytest


@pytest.fixture
def promela_gen_visitor():
    return PromelaGenVisitor()


def test_write_places_lines(promela_gen_visitor):
    promela_gen_visitor.write_places_lines("    Sample text for places")

    assert promela_gen_visitor.places_text == "\nSample text for places"


def test_write_constants_lines(promela_gen_visitor):
    promela_gen_visitor.write_constants_lines("    Sample text for constants")

    assert promela_gen_visitor.constants_text == "\nSample text for constants"


def test_write_behavior_model_lines(promela_gen_visitor):
    promela_gen_visitor.write_behavior_model_lines("    Sample text for behavior model")

    assert promela_gen_visitor.behavior_model_text == "\nSample text for behavior model"


def test_write_init_lines(promela_gen_visitor):
    promela_gen_visitor.write_init_lines("    Sample text for init")

    assert promela_gen_visitor.init_text == "\nSample text for init"


def test_write_workflow_lines(promela_gen_visitor):
    promela_gen_visitor.write_workflow_lines("    Sample text for workflow")

    assert promela_gen_visitor.workflow_text == "\nSample text for workflow"


def test_gen_excl_gw_has_option_macro(mocker):
    visitor = PromelaGenVisitor()
    mock_write_constants_lines = mocker.patch.object(visitor, "write_constants_lines")

    gateway = mocker.MagicMock()
    gateway.name = "TestGateway"
    gateway.out_flows = [mocker.MagicMock(), mocker.MagicMock(), mocker.MagicMock()]
    gateway.out_flows[0].name = "Flow1"
    gateway.out_flows[1].name = "Flow2"
    gateway.out_flows[2].name = "Flow3"

    visitor.gen_excl_gw_has_option_macro(gateway)

    expected_macro = (
        "#define TestGateway_hasOption \\\n"
        "(\\\n\tFlow1||\\\n\tFlow2||\\\n\tFlow3\\\n)\n"
    )

    mock_write_constants_lines.assert_called_once_with(expected_macro)


@pytest.mark.parametrize(
    "element_name, element_type, flow_source_name, expected_result",
    [
        ("TestElement", None, "SourceNode", "TestElement_FROM_SourceNode"),
        ("TestActivity", "Activity", None, "TestActivity_END"),
        ("TestElement", None, None, "TestElement"),
    ],
)
def test_get_location(
    mocker, element_name, element_type, flow_source_name, expected_result
):
    if element_type == "Activity":
        element = mocker.MagicMock(spec=Activity)
    else:
        element = mocker.MagicMock()
    element.name = element_name

    flow_or_msg = None
    if flow_source_name:
        flow_or_msg = mocker.MagicMock()
        flow_or_msg.source_node.name = flow_source_name

    visitor = PromelaGenVisitor()

    result = visitor.get_location(element, flow_or_msg)

    assert result == expected_result


def test_gen_places_no_flows_or_msgs(mocker, promela_gen_visitor):
    mock_promela_visitor = promela_gen_visitor
    mock_promela_visitor.flow_places = []

    mock_element = mocker.MagicMock()
    mock_element.in_flows = []
    mock_element.in_msgs = []

    mock_get_location = mocker.patch.object(
        mock_promela_visitor, "get_location", return_value="Location_1"
    )

    mock_promela_visitor.gen_places(mock_element)

    mock_get_location.assert_called_once_with(mock_element)
    assert mock_promela_visitor.flow_places == ["Location_1"]


def test_gen_places_with_flows_and_msgs(mocker, promela_gen_visitor):
    mock_promela_visitor = promela_gen_visitor
    mock_promela_visitor.flow_places = []

    mock_element = mocker.MagicMock()
    mock_element.in_flows = ["flow1", "flow2"]
    mock_element.in_msgs = ["msg1"]

    mock_get_location = mocker.patch.object(
        mock_promela_visitor,
        "get_location",
        side_effect=["Location_flow1", "Location_flow2", "Location_msg1"],
    )

    mock_promela_visitor.gen_places(mock_element)

    mock_get_location.assert_any_call(mock_element, "flow1")
    mock_get_location.assert_any_call(mock_element, "flow2")
    mock_get_location.assert_any_call(mock_element, "msg1")
    assert mock_promela_visitor.flow_places == [
        "Location_flow1",
        "Location_flow2",
        "Location_msg1",
    ]


def test_gen_places_with_activity(mocker, promela_gen_visitor):
    mock_promela_visitor = promela_gen_visitor
    mock_promela_visitor.flow_places = []

    mock_activity_element = mocker.MagicMock(spec=Activity)
    mock_activity_element.in_flows = []
    mock_activity_element.in_msgs = []

    mock_get_location = mocker.patch.object(
        mock_promela_visitor, "get_location", return_value="Activity_Location"
    )

    mock_promela_visitor.gen_places(mock_activity_element)

    assert mock_get_location.call_count == 2
    mock_get_location.assert_called_with(mock_activity_element)
    assert mock_promela_visitor.flow_places == [
        "Activity_Location",
        "Activity_Location",
    ]


@pytest.mark.parametrize(
    "guard, consume_locations, behavior_inline, put_conditions, put_locations, put_flow_ids, type, expected_result",
    [
        (
            "guard_condition",
            ["loc1", "loc2"],
            "behavior_code",
            [],
            ["put_loc1", "put_loc2"],
            ["flow_id1", "flow_id2"],
            "",
            ":: atomic { guard_condition -> \n\t\tbehavior_code\n\t\td_step {\n\t\t\tconsume_token(loc1)\n\t\t\tconsume_token(loc2)\n\t\t\tput_token(put_loc1)\n\t\t\tput_token(put_loc2)\n\t\t}\n\t}",
        ),
        (
            "guard_condition",
            ["loc1"],
            "behavior_code",
            [],
            ["put_loc1"],
            ["flow_id1"],
            "ParallelFALSE",
            ':: atomic { guard_condition -> \n\t\tbehavior_code\n\t\td_step {\n\t\t\tconsume_token(loc1)\n\t\t\tif\n\t\t\t:: (locked[me]) -> locked[me] = false; unlock()\n\t\t\t:: (!locked[me]) -> locked[me] = true; lock(me)\n\t\t\tfi\n\t\t\tput_token(put_loc1)\n\t\t\tif\n\t\t\t:: (!locked[me]) -> printf("###END PARALLEL GATEWAY###\\n")\n\t\t\t:: (locked[me]) -> printf("###START PARALLEL GATEWAY###\\n")\n\t\t\tfi\n\t\t}\n\t}',
        ),
        (
            "guard_condition",
            ["loc1"],
            "behavior_code",
            ["cond1", "cond2"],
            ["put_loc1", "put_loc2"],
            ["flow_id1", "flow_id2"],
            "XOR",
            ":: atomic { guard_condition -> \n\t\tbehavior_code\n\t\td_step {\n\t\t\tconsume_token(loc1)\n\t\t\tif\n\t\t\t\t:: cond1 -> put_token(put_loc1)\n\t\t\t\t:: cond2 -> put_token(put_loc2)\n\t\t\tfi\n\t\t}\n\t}",
        ),
    ],
)
def test_create_option(
    guard,
    consume_locations,
    behavior_inline,
    put_conditions,
    put_locations,
    put_flow_ids,
    type,
    expected_result,
):
    visitor = PromelaGenVisitor()

    result = visitor.create_option(
        guard,
        consume_locations,
        behavior_inline,
        put_conditions,
        put_locations,
        put_flow_ids,
        type,
    )

    assert result == expected_result


@pytest.mark.parametrize(
    "option_type, start_guard, in_flows, in_msgs, out_flows, out_msgs, expected_guard, expected_behavior_inline",
    [
        (
            "Task-END",
            "",
            [],
            [],
            [],
            [],
            "(hasToken(ElementNameLocation))",
            "skip",
        ),
        (
            "Parallel-join",
            "",
            ["flow1", "flow2"],
            [],
            [],
            [],
            "(( hasToken(flow1Location) && hasToken(flow2Location) )\n)",
            "ElementName_BehaviorModel()",
        ),
        (
            "XOR",
            "",
            ["flow1"],
            [],
            ["out_flow1"],
            [],
            "(( hasToken(flow1Location) )\n\t&&\t(ElementName_hasOption))",
            "ElementName_BehaviorModel()",
        ),
    ],
)
def test_gen_activation_option(
    mocker,
    option_type,
    start_guard,
    in_flows,
    in_msgs,
    out_flows,
    out_msgs,
    expected_guard,
    expected_behavior_inline,
):
    visitor = PromelaGenVisitor()
    mock_create_option = mocker.patch.object(
        visitor, "create_option", return_value="GeneratedOption"
    )
    mock_write_workflow_lines = mocker.patch.object(visitor, "write_workflow_lines")
    mocker.patch.object(
        visitor,
        "get_location",
        side_effect=lambda elem,
        flow=None: f"{flow.name if flow else elem.name}Location",
    )

    element = mocker.MagicMock()
    element.id = "ElementID"
    element.name = "ElementName"
    element.in_flows = [
        SequenceFlow(mocker.MagicMock(attrib={"id": f"{flow}_id", "name": flow}))
        for flow in in_flows
    ]
    element.in_msgs = [
        MessageFlow(mocker.MagicMock(attrib={"name": msg})) for msg in in_msgs
    ]
    element.out_flows = []
    for flow in out_flows:
        mock_flow = SequenceFlow(
            mocker.MagicMock(attrib={"id": f"{flow}_id", "name": flow})
        )
        mock_flow.target_node = mocker.MagicMock()
        mock_flow.target_node.name = "targetNode"
        element.out_flows.append(mock_flow)
    element.out_msgs = []
    for msg in out_msgs:
        mock_msg = MessageFlow(mocker.MagicMock(id=f"{msg}_id"))
        mock_msg.target_node = mocker.MagicMock()
        mock_msg.target_node.name = "targetNode"
        element.out_msgs.append(mock_msg)

    visitor.gen_activation_option(
        element, start_guard=start_guard, option_type=option_type
    )

    expected_consume_locations = [f"{flow}Location" for flow in in_flows + in_msgs] + (
        [f"{element.name}Location"] if option_type == "Task-END" else []
    )

    expected_put_locations = [f"{flow.name}Location" for flow in element.out_flows] + [
        "targetNodeLocation" for msg in out_msgs
    ]
    expected_put_flow_ids = [flow.id for flow in element.out_flows] + [
        msg.id for msg in element.out_msgs
    ]
    expected_put_conditions = (
        [flow for flow in out_flows] if option_type == "XOR" else []
    )

    mock_create_option.assert_called_once_with(
        expected_guard,
        expected_consume_locations,
        expected_behavior_inline,
        expected_put_conditions,
        expected_put_locations,
        expected_put_flow_ids,
        option_type,
    )

    mock_write_workflow_lines.assert_called_once_with("GeneratedOption")


def test_gen_behavior_model():
    visitor = PromelaGenVisitor()

    place_name = "TestPlace"

    expected_result = (
        "//TestPlace\n" "inline TestPlace_BehaviorModel(){\n" "\tskip\n" "}\n\n"
    )

    result = visitor.gen_behavior_model(place_name)

    assert result == expected_result
