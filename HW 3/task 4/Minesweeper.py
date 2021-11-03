# -*- coding: utf-8 -*-
"""
Created on Sun Oct 31 23:17:28 2021

@author: chote
"""

'''
Значения ячеек:
    'Mine'- помечено, что в ячейке есть мина
    0 - вокруг ячейки нет мин
    1-8 - вокруг ячейки 1-8 мин
    None - неизвестная ячейка (не вскрыта)
    
Согласно заданию, рассматриваемая ячейка в конфигурации должна иметь хотя бы 
одного соседа вскрытого. Иначе, очевидно, ячейка небезопасна.

Суть программы: 
    -берём все вскрытые ячейки.
    -для всех их соседей составляем формулы вида (x1 & x2 &...& ~xn) | (~x1 & ... & xn) |...
    -эту формулу переводим в КНФ, используя библиотеку sympy
    -при этом ведём общее множество символов пропозициональных для разных таких вскрытых ячеек
    -коньюктивно соединяем все такие КНФ
    -получим КНФ. 
    -присоединим конъюктивно ещё формулу x (или ~x), при истиности которой 
     (и всей формулы в частности) рассматриваемая ячейка - небезопасна (безопасна)
    -проверка на выполнимость (сат солвинг) испольщует некий (неуточненный) 
     сатсолвер из библиотеки sympy
'''
    
import numpy as np
import copy
from sympy.logic import SOPform
from sympy import symbols
from itertools import combinations
from sympy import sympify, true, false, Or
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable


rows = 10
cols = 10
field = np.tile(None, (rows,cols))

field =   [[None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, None],
           [None, None, None, None, None, None, None, None, None, 'Mine'],
           [None, None, None, None, None, None, None, None, 2,      1]]

checking_cell = (cols-2, rows-2) #(8, 8)
checking_cell = (cols-3, rows-2) #(7, 8)

def make_neighbour_coords(cell_coords):
    x, y = cell_coords
    return [(x-1, y), (x-1, y-1), (x-1, y+1),
           (x+1, y), (x+1, y-1), (x+1, y+1),
           (x, y-1), (x, y+1)]
    
                          
def get_neighbours_coords(cells, cell_coords):
    rws, clmns = len(cells), len(cells[0])
    x, y = cell_coords
    neighbours = make_neighbour_coords(cell_coords)
    existing_neighbours = [coords for coords in neighbours 
                           if(coords[0] < clmns and coords[0]>=0 and 
                               coords[1] < rws and coords[1]>=0)]
    return existing_neighbours

    
    
    
def potential_neighour_mines_on_non_empty_cell(cells, cell_coords):
    neighbours = get_neighbours_coords(cells, cell_coords)
    potential_mines = copy.deepcopy(neighbours)
    x, y = cell_coords
    mines_rest = cells[y][x] if cells[y][x] in range(9) else 8
    for n in neighbours:
        nx, ny = n
        if(cells[ny][nx] in range(9) or cells[ny][nx] == 'Mine'):
            potential_mines.remove(n)
            if(cells[ny][nx] == 'Mine'):
                mines_rest -= 1
            
    return potential_mines, mines_rest

def get_known_neighbours(cells, cell_coords):
    neighbours = get_neighbours_coords(cells, cell_coords)
    known_neighbours = [n for n in neighbours if cells[n[1]][n[0]] in range(9)]
    
    return known_neighbours

    
def get_all_potential_neighbours(cells):
    out = []
    info = []
    for y, row in enumerate(cells):
        for x, cell in enumerate(row):
            if(cell in range(9)):
                pmines, rest_mines = potential_neighour_mines_on_non_empty_cell(cells, (x,y))
                out += pmines
                info.append((pmines, rest_mines, (x,y)))
    out = list(set(out))
    return out, info

"""coord_list должен иметь неповторяющиеся ячейки"""
def make__symbols_on_cells_list(coord_list):
    syms_to_coords = {}
    coords_to_syms = {}
    for i, x in enumerate(coord_list):
        coords_to_syms[x] = symbols(f"x{i}")
        syms_to_coords[coords_to_syms[x]] = x
    return coords_to_syms, syms_to_coords
        

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

def make_formula_on_neighbours(potential_neighbour_syms, supposed_neighbour_syms):
    trues_formula = make_con_from_symbols(supposed_neighbour_syms)
    tmp = list(map(lambda x: ~x, 
                   [s for s in potential_neighbour_syms if s not in supposed_neighbour_syms]))
    falses_formula = make_con_from_symbols(tmp)
    return trues_formula & falses_formula


"""cell_coords должно иметь хотя бы одного вскрытого соседа, иначе очевидно, небезопасно"""
def safetly(cells, cell_coords):
    
    all_cells, info = get_all_potential_neighbours(cells)
    coords_to_syms, syms_to_coords = make__symbols_on_cells_list(all_cells)

    info_syms = [] 
    formulas = []
    print(coords_to_syms)
    print(info)
    for i in info:
        potential_mines_syms = list(map(lambda x: coords_to_syms[x], i[0]))
        
        info_syms.append((potential_mines_syms, i[1], i[2]))
        assert len(potential_mines_syms) >= i[1], "Error, potential_mines_syms < rest_mines"
        if(i[1] > 0 and len(potential_mines_syms) > 0):
            combs = combinations(potential_mines_syms, i[1])
            cons = []
            for c in combs:
                con = make_formula_on_neighbours(potential_mines_syms, c)
                cons.append(con)
            frml = make_dis_from_symbols(cons)
            formulas.append(frml)
        
        if(i[1] == 0 and len(potential_mines_syms) > 0):
            formulas.append(make_formula_on_neighbours(potential_mines_syms, []))
    
    general_formula = make_con_from_symbols(formulas)
    print(general_formula)
    general_formula_cnf = to_cnf(general_formula)
    
    sym = coords_to_syms[cell_coords]
    """Формула проверяет, находится ли в ячейке мина"""
    is_mine_formula_cnf = general_formula_cnf & sym
    if(satisfiable(is_mine_formula_cnf) != False):
        return "cell is unsafe"
    elif(satisfiable(general_formula_cnf & ~sym) != False):
        return "cell is safe"
    return "unknown, probably unsafe "

print(safetly(field, checking_cell))
        
    