import ctypes
import os

_lambda = ctypes.CDLL(os.path.abspath(os.path.join(__file__,'../../LambdaC/lambda.so')))
_lambda.reduce_expression.argtypes = (ctypes.c_char_p,)
_lambda.reduce_expression.restype = ctypes.c_char_p

def reduce_lambda(expr):
    full_exprs = f"eval {expr};"
    result = _lambda.reduce_expression(ctypes.c_char_p(bytes(full_exprs, 'utf-8')))
    str_result = str(result, 'utf-8')

    return str_result

if __name__ == "__main__":
    expr = " x"
    print(reduce_lambda(expr))