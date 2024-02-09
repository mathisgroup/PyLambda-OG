import pytest
import PyLambda_OG as PL

def test_expression_1():
    val = PL.reduce_lambda("\\x1.x1")
    assert val == "\\x1.x1"

def test_expression_2():
    val = PL.reduce_lambda("\\x2.x2")
    assert val == "\\x1.x1"

def test_expression_TT():
    val = PL.reduce_lambda("(\\x.\\y.x)\\z.\\w.z")
    assert val == "\\x1.\\x2.\\x3.x2" # Is this right??