import re


def cleanup_expression(expression: str) -> str:
    expression = re.sub(r"&amp;", "&", expression)
    expression = re.sub(r"&lt;", "<", expression)
    expression = re.sub(r"&gt;", ">", expression)

    expression = re.sub(r"</?div>", "", expression)
    expression = re.sub(r"<br>", " ", expression)

    expression = re.sub(r"\s*(==|!=|&&|\|\|)\s*", r" \1 ", expression)

    expression = re.sub(r"\s+", " ", expression)

    return expression.strip()
