# -*- coding: utf-8 -*-
"""
Created on Thu Nov  4 12:40:22 2021

@author: chote
"""
#from nnf import NNF, Var, And, Or, Internal
#from nnf.util import memoize
import networkx as nx
import itertools
from itertools import combinations

from sympy import symbols
from sympy import sympify, true, false, Or, And, Not, Symbol
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable
from math import log10
from numpy import sign

from functools import reduce

"""
Применяется DPLL к формуле: верно ли, что в графе каждая клика размера 3 (треугольник)
может быть раскрашена в более чем 1 цвет.

Преобразование Цейтина применятся на промежуточных шагах к формулам:
    верно ли, что вершина раскрашена хотя бы в один из цветов,
    но не покрашена при этом во все остальные.

"""

def search_new_sym(syms):
    possible_max_int = len(syms)
    while Symbol(str(possible_max_int)) in syms:
        possible_max_int += 1
    return Symbol(str(possible_max_int))

    
def to_CNF(formula, oldsyms = None, newsyms = set()):
    #print(f"{formula} WILL BE CONVERTED")
    
    if oldsyms == None:
        oldsyms = formula.atoms()

    
    def Tseitin_transform(node, accumulator=set(), oldsym=oldsyms, newsym=newsyms):

        if isinstance(node, Symbol):
            return (node, accumulator)

        if isinstance(node, Not):
            [child] = node.args
            l, d = Tseitin_transform(child, accumulator, oldsym, newsym)
            return (~l, d)

        p = search_new_sym(oldsym | newsym)
        
        newsym.add(p)

        if isinstance(node, And):
            first = node.args[0]

            if(len(node.args) == 2):
                second = And(node.args[1])
            else:
                second = reduce(And, node.args[1:], true)
            #print(f"second is {second}")
            l1, d1 = Tseitin_transform(first, accumulator, oldsym, newsym)
            l2, d2 = Tseitin_transform(second, d1, oldsym, newsym)
            d = d2 | {Or(l1, ~p), Or(l2,~p), Or(p, ~l1, ~l2)}

        elif isinstance(node, Or):
            first = node.args[0]

            if(len(node.args) == 2):
                second = Or(node.args[1])
            else:
                second = reduce(Or, node.args[1:], false)
            #print(f"second is {second}")
            l1, d1 = Tseitin_transform(first, accumulator, oldsym, newsym)
            l2, d2 = Tseitin_transform(second, accumulator, oldsym, newsym)
            
            d = d2 | {Or(~l1, p), Or(~l2, p), Or(~p, l1, l2)}

        else:
            raise TypeError(node)

        return (p, d)
    

   
    l, d = Tseitin_transform(formula)
    out = l & reduce(And, d, true)
    print(f"to_CNF output is {out}")
    print(f"newsyms is {newsyms}")
    
    return out, newsyms

a,b,c = symbols('a b c')

f = ~(a&b | ~c)
cn =to_CNF(f)

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
#    print(f"UnitPropogate for lit {lit} and S =", S)
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
            #print(f"Propogated for lit {diz[0]} and S =", S)
            
        #print(f"S is ", S)
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
           #print(f"PURE {l} was eliminated S is ", S)
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
    #print(M)
    print(f"lit is {lit}")
    #print(f"S is", S)
    M[abs(lit)] = sign(lit)
    temp = DPLL(S + [[lit]], M)
    if(temp[0] == 'SAT'):
        return ('SAT', temp[1])
    else:
        M[abs(lit)] = sign(lit)
        return DPLL(S + [[-lit]], M)
    
    
import networkx as nx
import itertools
from sympy import symbols
from sympy import sympify, true, false, Or
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable
from itertools import combinations
from math import *

def find_subcliques_size_k(clique, sub_clique_size):
    i = 0
    subcliqueS = []
    n_edges = itertools.combinations(clique, 2)
    graph = nx.Graph()
    graph.add_nodes_from(clique)
    graph.add_edges_from(n_edges)
    
    for subclique in nx.find_cliques(graph):
        if len(subclique) == sub_clique_size:
            i += 1
            subcliqueS.append(subclique)
        elif len(subclique) > sub_clique_size:
            subcliqueS += list(itertools.combinations(subclique, k))
    return subcliqueS

def find_max_clique(graph, color_count, min_divercity_clique_size=3):
    cur_max_clique = []
    for clique in nx.find_cliques(graph):
        print(f"CLIQUE IS {clique}")
        if (len(clique) == min_divercity_clique_size and len(clique) > len(cur_max_clique)
        and check_all_subcliques_in_clique([clique], graph.nodes, color_count)):
            cur_max_clique = clique
            
        elif len(clique) > min_divercity_clique_size and len(clique) > len(cur_max_clique):
            subcliqueS = list(itertools.combinations(clique, min_divercity_clique_size))
            is_good = check_all_subcliques_in_clique(subcliqueS, graph.nodes, color_count)
            if is_good:
                cur_max_clique = clique
                
    return cur_max_clique
                
            
            
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

def formula_clique_colorized_by_one_color(clique, syms_all, var_to_colors_SYMS, colors):
    dises = []
    one_color_foreach_vert = true
    
    for v in clique:
        cnf, newsyms = to_CNF(f_vert_colorized_by_one_color(v, var_to_colors_SYMS, colors), oldsyms=syms_all) 
        #cnf = to_cnf(f_vert_colorized_by_one_color(v, var_to_colors_SYMS, colors))
        one_color_foreach_vert = one_color_foreach_vert & cnf
        syms_all |= newsyms
    
    one_color_for_triangle = true
    for color in colors:
        color_vars = true
        
        #f = true
        for v in clique:
            #f = f & f_vert_colorized_by(v, color, var_to_colors_SYMS)
            color_vars = color_vars | ~(var_to_colors_SYMS[v][color])
        one_color_for_triangle = one_color_for_triangle & color_vars
        #dis = make_dis_from_symbols(list(map(lambda x: ~x, color_vars)))
        #dises.append(dis)
        #print(f"conjunct is {to_cnf(~f)}")   
        #out = out & ~f
    #return make_con_from_symbols(dises)
    #print(f"one_color_for_triangle is {one_color_for_triangle}")
    #print(f"one_color_foreach_vert is {one_color_foreach_vert}")
    return one_color_foreach_vert & one_color_for_triangle
    
def f_vert_colorized_by_one_color(vert, var_to_colors_SYMS, colors):
    dis = false
    for color in colors:
        dis = dis | f_vert_colorized_by(vert, color, var_to_colors_SYMS)
    return dis
        
        
def f_vert_colorized_by(vert, color, var_to_colors_SYMS):
    con = true
    for i, sc in enumerate(var_to_colors_SYMS[vert]):
        if(i != color):
            con = con & (~sc)
        else:
            con = con & sc
     
    return con
    
def check_all_subcliques_in_clique(cliques, varlist, color_count):
    var_to_colors_SYMS = make_colorized_syms(varlist, color_count)
    #print(f"var_to_colors_SYMS  is {var_to_colors_SYMS}")
    colors = range(color_count)
    all_syms = []
    for v in var_to_colors_SYMS.values():
        all_syms += v
    all_syms = set(all_syms)
    print(f"ALL_SSYMS IS {all_syms}")
    
    formula = true
    
    for triangle in cliques:
        formula = formula & formula_clique_colorized_by_one_color(triangle, all_syms,
                                                                  var_to_colors_SYMS,
                                                                  colors)
    M = {float(str(list(a.atoms())[0])):None for a in all_syms}
    cnf = []
    print(f"\n\n{sorted(M.items(), key = lambda kv: kv[0])}\n\n")
    #print(f"\n\nM is {M}\n\n")
    ars = formula.args
    for disj in ars:
        dis=[]
        dis_ars = disj.args
        if isinstance(disj, Symbol):
            dis.append(float(str(list(disj.atoms())[0])))
        elif isinstance(~disj, Symbol):
            dis.append(-float(str(list(disj.atoms())[0])))
        else:
            for lit in dis_ars:
                if isinstance(lit, Not):
                    dis.append(-float(str(list(lit.atoms())[0])))
                elif isinstance(lit, Symbol):
                    dis.append(float(str(list(lit.atoms())[0])))
        cnf.append(dis)
    print(f"formula is {formula}")
    print(f"cnf is {cnf}")
    answer = DPLL(cnf, M)
    print(f"answer is {answer[0]}\n")
    #print(f"\n Model is {answer[1]}")
    
    """
    if(answer != False):
        #print(f"model is {answer}")
        return True
    else:
        return False
    """
    
    
def make_colorized_syms(var_list, color_count):
    var_to_color_var = {}
    for v in var_list:
        dim = (log10(color_count)//1 + 1)
        ss = [f"{v + (i+1)*(1/(10**dim))}" for i in range(color_count)]
        syms = list(symbols(' '.join(ss)))
        print(f"syms is {syms}")
        var_to_color_var[v] = syms
    return var_to_color_var

G = nx.Graph()
G.add_edge(1, 2)  # default edge data=1
G.add_edge(2, 3, weight=0.9)  # specify edge data

edges = [ [ 1, 2 ],
         [ 2, 3 ],
         [ 3, 1 ],
         [ 4, 3 ],
         [ 4, 5 ],
         [ 5, 3 ],
         
         [2,4],
         [4,1]
         ]

k = 3;
G.add_edges_from(edges)
cliques = find_subcliques_size_k(G, k)

(check_all_subcliques_in_clique(cliques, G.nodes, k))

