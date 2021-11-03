# -*- coding: utf-8 -*-
"""
Created on Wed Oct 20 01:40:27 2021

@author: chote
"""
# -*- coding: utf-8 -*-
"""
Created on Tue Oct 19 22:49:05 2021

@author: chote
"""

"""
python 3.9
Формулы содержат только коньюнкции, дизьюнкции и литералы, записываются в 
виде кортежей f = (a,b), где
a - тип связки логической ('var', '|', '!', '&')
b - аргументы формулы. Сам является формулой, либо, если f имеет тип 'var', 
    является одной из переменных. Если тип f - '&' или '|', то 2 аргумента.
Переменные задаются натуральными числами.

Не поддерживаются константные значения (истина-ложь).
В таком виде формулы подаются на вход преобразованию Цейтина.

Первый элемент в модели M фиктивный (None), т.к. ей не сопостовляется имя 
    переменной.

В качестве примера используется функция !(!(p&q)->!r) из дз№1 зад.4, 
    вручную раскрывая импликации -> и <-> по определению, и тут же убрав
    множественные отрицания
    !(!!(p&q)| !r) ~ !( (p&q) | !r)   (*)
    Далее эта формула в КНФ, полученная преобразованием Цейтина, подаётся 
    на вход DPLL.
"""
import numpy as np
from numpy import sign
import random


phi = ()
def search_new_var_name(oldvar, newvar):
    if(len(newvar) == 0):
        return max(oldvar) + 1
    return max(newvar) + 1
    
def erase_double_neg(d):
    if(d[0] == 'var'):
        return
    for i, v in enumerate(d):
        print(v)
        if(v[0] == 'var'):
            continue
        if(v[0] == '!' and v[1][0] == '!'):
            d[i] = v[1][1]
            erase_double_neg(d[i])
            continue
        if(v[0] == '|' or v[0] == '&'):
            erase_double_neg(d[i][1])
            continue
    return

def to_numer_diz(diz):
    if(diz[0] == 'var'):
        return diz[1]
    for i, diz in enumerate(diz):
        if(diz[0] == 'var'):
            return diz[1]
        if(diz[0] == '!'):
            return -1*to_numer_diz(diz[1][1])
        if(diz[0] == '|'):
            if(diz[1][0][0] == 'var'):
                diz[1][0] = diz[1][0][1]
            diz[1] = to_numer_diz(diz[1])
            
            
def to_numer_cnf(cnf):
    ans = []
    for i, diz in enumerate(cnf):
        if(diz[0] == '!'):
            ans += -1*diz[1][1]
            continue
        if(diz[0] == '|'):
            ans += to_numer_diz(diz[1])
    return ans

def CNF_non_rec(a,b, oldvar, newvar):
#    if()
        return
    
def CNF(a,b, oldvar, newvar):
    """
    if(a[0] == '!' and a[1][0] == '!'):
        a = (a[1][1][0], a[1][1][1])
        return CNF(a, b, oldvar, newvar)
    """
    if(a[0] == 'var'):
        return [a[1],b]
    if(a[0] == '!'):
        x,y = CNF(a[1], b, oldvar, newvar)
        return [-x, y]
    if(a[0] == '&'):
        l1, d1 = CNF(a[1][0], b, oldvar, newvar)
        l2, d2 = CNF(a[1][1], d1, oldvar, newvar)
        p = search_new_var_name(oldvar, newvar)
        newvar.append(p)
        d = []+d2
        d.append([l1, -p])
        d.append([l2, -p])
        d.append([p,-l2, -l1])
        
        return [p, d]
    
    if(a[0] == '|'):
        l1, d1 = CNF(a[1][0], b, oldvar, newvar)
        l2, d2 = CNF(a[1][1], d1, oldvar, newvar)
        p = search_new_var_name(oldvar, newvar)
        newvar.append(p)
        d = []+d2
        d.append( [-l1, p])
        d.append([-l2, p])
        d.append( [-p, l1, l2])
        return [p, d]
    
empt=[]
oldvs = [1, 2, 3]
newvs = []

tmp = ['&', 
           [
                ['var', 1], ['var', 2]
           ]
      ]

phi = ['!', [
            '|', [
                    tmp, ['!', ['var', 3]]
                 ]
            ]
      ]

l, d = CNF(phi, empt, oldvs, newvs)

def EliminateLiteral(S, lit):
    out = []
    for v in S:
        C = [s for s in v if s != lit]
        if(len(C) !=0 or len(v) <= 1):
            out.append(C)
#        if(lit not in v):
#            out.append(v)
    return out

def UnitPropogate(S, lit):
    print(f"UnitPropogate for lit {lit} and S =", S)
#    tmp = [c for c in S if lit in c]
#    tmp2 = [c for c in S if c not in tmp]
    s = [c for c in S if lit not in c]
    return EliminateLiteral(s, -lit)

def clearlyIncluding(p, S):
    for i, v in enumerate(S):
        for j in v:
            if(j == -p):
                return False
    return True

def ChooseLiteral(S):
    if(len(S) == 0):
        return None
    for diz in S:
        if(len(diz) == 0):
            continue
        lit = diz[0]
        return lit
    return None
    
def containsSimpleDiz(S):
    for i in S:
        if(len(i)==1):
            return True
    return False

def getPureLiteral(S):
    for diz in S:
        for lit in diz:
            if(clearlyIncluding(lit, S)):
                return lit
    return None
    
def getSimpleDiz(S):
    for i in S:
        if(len(i)==1):
            return i
        
def containsEmptyDiz(S):
    for v in S:
        if(len(v) == 0):
            return True
    return False

def DPLL(S, M):
    if(len(S)==0):
        return ('SAT', M)
    for diz in S:
        if(len(diz) == 0):
            return ('UNSAT', None)
    
    while(containsSimpleDiz(S) or getPureLiteral(S) != None):
        
        while(containsSimpleDiz(S)):
            diz = getSimpleDiz(S)
            if(M[abs(diz[0])] == -sign(diz[0])):
                return ('UNSAT', None)
            S = UnitPropogate(S, diz[0])
            M[abs(diz[0])] = sign(diz[0])
            print(f"Propogated for lit {diz[0]} and S =", S)
            
        print(f"S is ", S)
        if(len(S) == 0):
            return ('SAT', M)
        if(containsEmptyDiz(S)):
            return ('UNSAT', None)
        while(getPureLiteral(S) != None):
            l = getPureLiteral(S)
            out = []
            for v in S:
                if(l not in v):
                    out.append(v)
            S = out
            print(f"PURE {l} was eliminated S is ", S)
            M[abs(l)] = sign(l)
        
    '''
    for diz in S:
        for pos, lit in enumerate(diz):
            if(clearlyIncluding(lit, S)):
                S = EliminateLiteral(S, lit)
                print(f"PURE {lit} was eliminated S is ", S)
                M[abs(lit)] = sign(lit)
    '''
    if(len(S) == 0):
        return ('SAT', M)
    if(containsEmptyDiz(S)):
        return ('UNSAT', None)
    lit = ChooseLiteral(S)
    print(M)
    print(f"lit is {lit}")
    print(f"S is", S)
    M[abs(lit)] = sign(lit)
    temp = DPLL(S + [[lit]], M)
    if(temp[0] == 'SAT'):
        return ('SAT', temp[1])
    else:
        M[abs(lit)] = sign(lit)
        return DPLL(S + [[-lit]], M)
    
phi = [[1,-2], [-1,-3], [2]]
xi = [[-2, 3], [2, 4], [-4]]
M = [None]*5
S = phi+xi

atPHI = [1,2,3]
atXI  = [2,3,4]
print(f"atPhi is {atPHI}")
print(f"atXI is {atXI}")
CL = list(map(lambda c: (c, [[]]), phi))
DL = list(map(lambda c: (c, []), xi))

answer = DPLL(phi+xi, M)
print(f"\n\nS is {S}")
print(f"\n\nANSWER IS {answer}\n\n")
    
M = [None] * (len(oldvs) + len(newvs) + 1)
print(f"l&d after CNF is {[[l]]+d}\n")
answer = DPLL([[l]]+d, M)
print(f"\n\nANSWER IS {answer}\n\n")


"""
Применяю DPLL к формуле из задания 3 этой лекции.
Копировал код из задания 3 и немного изменил.
"""

import networkx as nx
import itertools
from sympy import symbols
from sympy import sympify, true, false, Or
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable
from math import *

def find_cliques_size_k(graph, clique_size):
    i = 0
    cliques = []
    for clique in nx.find_cliques(graph):
        if len(clique) == clique_size:
            i += 1
            cliques.append(clique)
        elif len(clique) > k:
            cliques += list(itertools.combinations(clique, k))
    return cliques


def make_dis_from_symbols(syms):
    out = false
    for s in syms:
        out = out | s
    return out

def make_con_from_symbols(syms):
    out = true
    for s in syms:
        out = out & s
    return out

def formula_clique_colorized_by_one_color(clique, var_to_colors_SYMS, colors):
    dises_SYM = []    
    for color in colors:
        color_vars = []
        for v in clique:
            color_vars.append(var_to_colors_SYMS[v][color])
        dis = make_dis_from_symbols(list(map(lambda x: ~x, color_vars)))
        dises_SYM.append(dis)
    return make_con_from_symbols(dises_SYM)
    

def make_formula_on_all_cliques(cliques, varlist, color_count):
    var_to_colorS_SYMS, var_to_colorS_VAR = make_colorized_syms(varlist, color_count)
    print(f"\nvar_to_colorS_SYMS  is {var_to_colorS_SYMS}\n")
    colors = range(color_count)
    
    formula = true
    
    cnf = []
    
    for clique in cliques:
        formula = formula & formula_clique_colorized_by_one_color(clique,
                                                                  var_to_colorS_SYMS,
                                                                  colors)
        for color in colors:
            color_vars = []
            for v in clique:
                color_vars.append(var_to_colorS_VAR[v][color])
            dis = list(map(lambda x: -x, color_vars))
            cnf.append(dis)
                
    print(f"formula is {formula}" )
    
    return var_to_colorS_VAR, formula, cnf
    
    
def make_colorized_syms(var_list, color_count):
    var_to_colorS_SYMS = {}
    var_to_colorS_VAR = {}
    for v in var_list:
        ss = [f"x_{v}_{i}" for i in range(color_count)]
        dim = (log10(color_count)//1 + 1)
        ints=[v + (i+1)*(1/(10**dim)) for i in range(color_count)]
        syms = list(symbols(' '.join(ss)))
        print(f"syms is {syms}")
        var_to_colorS_SYMS[v] = syms
        var_to_colorS_VAR[v] = ints
    return var_to_colorS_SYMS, var_to_colorS_VAR


G = nx.Graph()
G.add_edge(1, 2)  # default edge data=1
G.add_edge(2, 3, weight=0.9)  # specify edge data

edges = [ [ 1, 2 ],
         [ 2, 3 ],
         [ 3, 1 ],
         [ 4, 3 ],
         [ 4, 5 ],
         [ 5, 3 ] ]

k = 3;
G.add_edges_from(edges)

cliques = find_cliques_size_k(G, k)



var_to_colorS_VAR, _ , cnf = make_formula_on_all_cliques(cliques, G.nodes(), k)

M = { }
for i in  var_to_colorS_VAR.values():
    for v in i:
        M[v] = None
print(f"\nM is {M}\n")
answer = DPLL(cnf, M)
print(f"\n\nCNF is {cnf}\n")

print(f"\n\nANSWER IS {answer}\n\n")


