# -*- coding: utf-8 -*-
"""
Created on Mon Nov  1 15:13:28 2021

@author: chote
"""
import networkx as nx
import itertools
from sympy import symbols
from sympy import sympify, true, false, Or
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable

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


cliques = find_cliques_size_k(G, k)

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

def formula_clique_colorized_by_one_color(clique, var_to_colors_var, colors):
    dises = []
    for color in colors:
        color_vars = []
        for v in clique:
            color_vars.append(var_to_colors_var[v][color])
        dis = make_dis_from_symbols(list(map(lambda x: ~x, color_vars)))
        dises.append(dis)
    return make_con_from_symbols(dises)
    

def check_all_cliques(cliques, varlist, color_count):
    var_to_colors_var = make_colorized_syms(varlist, color_count)
    print(f"var_to_colors_var  is {var_to_colors_var}")
    colors = range(color_count)
    
    formula = true
    
    for clique in cliques:
        formula = formula & formula_clique_colorized_by_one_color(clique,
                                                                  var_to_colors_var,
                                                                  colors)
    print(f"formula is {formula}" )
    if(satisfiable(formula) != False):
        return True
    else:
        return False
    
    
def make_colorized_syms(var_list, color_count):
    var_to_color_var = {}
    for v in var_list:
        ss = [f"x_{v}_{i}" for i in range(color_count)]
        syms = list(symbols(' '.join(ss)))
        print(f"syms is {syms}")
        var_to_color_var[v] = syms
    return var_to_color_var


print(check_all_cliques(cliques, G.nodes, k))
