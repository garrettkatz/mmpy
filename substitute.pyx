# cythonize -i -3 substitute.pyx

"""
symbols[n]: nth token in symbol string
substitution[v]: symbol string to put in place of symbol v
returns result[n]: nth token after substitutions applied
"""
def substitute(list symbols, dict substitution):
    cdef tuple result = ()
    for symbol in symbols:
        if symbol in substitution: result += substitution[symbol]
        else: result += (symbol,)
    return result


