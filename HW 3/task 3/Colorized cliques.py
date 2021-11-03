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
from itertools import combinations


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

def formula_clique_colorized_by_one_color(clique, var_to_colors_SYMS, colors):
    dises = []
    one_color_foreach_vert = true
    
    for v in clique:
        one_color_foreach_vert = one_color_foreach_vert & f_vert_colorized_by_one_color(v, var_to_colors_SYMS, colors)
    
    one_color_for_triangle = false
    for color in colors:
        color_vars = true
        
        #f = true
        for v in clique:
            #f = f & f_vert_colorized_by(v, color, var_to_colors_SYMS)
            color_vars = color_vars & (var_to_colors_SYMS[v][color])
        one_color_for_triangle = one_color_for_triangle | color_vars
        #dis = make_dis_from_symbols(list(map(lambda x: ~x, color_vars)))
        #dises.append(dis)
        #print(f"conjunct is {to_cnf(~f)}")   
        #out = out & ~f
    #return make_con_from_symbols(dises)
    #print(f"one_color_for_triangle is {one_color_for_triangle}")
    #print(f"one_color_foreach_vert is {one_color_foreach_vert}")
    return one_color_foreach_vert & ~one_color_for_triangle
    
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
    
    formula = true
    
    for triangle in cliques:
        formula = formula & formula_clique_colorized_by_one_color(triangle,
                                                                  var_to_colors_SYMS,
                                                                  colors)
        
    #print(f"formula is {formula}")
    answer = satisfiable(formula)
    if(answer != False):
        print(f"model is {answer}")
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

print(f"max clique with constraints is {find_max_clique(G, k)}")

#print(check_all_subcliques_in_clique(cliques, G.nodes, k))
