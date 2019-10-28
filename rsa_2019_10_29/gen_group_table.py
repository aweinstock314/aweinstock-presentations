import operator
import os

def table(symbol, n, f):
    #s = '\\(\\begin{array}{c|' + 'c'*n + '}\n'
    s = '\\(\\begin{array}{p{3mm}|' + 'p{2mm}'*n + '}\n'
    symbol = '\\(%s\\)' % (symbol,)
    s += ' & '.join([symbol] + [str(i) for i in range(n)]) + '\\\\\\hline\n'
    for i in range(n):
        s += ' & '.join([str(i)] + [str(f(i, j)%n) for j in range(n)]) + '\\\\\n'
    s += '\\end{array}\\)'
    return s

def gentable(fname, *args):
    with open('tables/%s' % fname, 'w') as f:
        f.write(table(*args))

if not os.path.exists('tables'):
    os.mkdir('tables')

gentable('add_mod_7.tex', '+', 7, operator.add)
gentable('mul_mod_7.tex', '*', 7, operator.mul)
gentable('add_mod_8.tex', '+', 8, operator.add)
gentable('mul_mod_8.tex', '*', 8, operator.mul)
gentable('mul_mod_13.tex', '*', 13, operator.mul)
gentable('exp_mod_13.tex', 'x^y', 13, pow)
