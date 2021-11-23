# -*- coding: utf-8 -*-
"""
Created on Tue Nov  9 18:01:06 2021

@author: chote
"""
import networkx as nx
import itertools
from itertools import combinations
import copy

from sympy import symbols
from sympy import sympify, true, false, Or, And, Not, Symbol
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable
from math import log10

def make_proof_if_UNSAT(A, B):
    if(A&B).satisfiable:
        return None
    G = nx.DiGraph()
    Labeled
    G.add_nodes_from(A.container, attr)
    
    
    
def glob(c, A, B):
    out = false
    for i in c.args:
        if i in A.args and i in B.args:
            out = out | i
    return out

def localAnotB(c, A, B):
    out = false
    for i in c.args:
        if i in A.args and i not in B.args:
            out = out | i
    return out
'''
def p(G, clause):
    if(clause == false)
    '''
    
def Itp(G, A, B):
    return p(G, false)
    
def contains_contra(cnf, lit):
    for diz in cnf.args:
        if(len(diz.args) == 1 and diz == ~lit):
            return True
    return False

def elim_contras_con(cnf):
    for i, diz in enumerate(cnf.args):
        for j in range(i+1, len(cnf.args)):
            if cnf.args[j] == ~diz:
                return false
    return cnf

def elim_contras_disj(disj):
    for i, lit in enumerate(disj.args):
        for j in range(i+1, len(disj.args)):
            if disj.args[j] == ~lit:
                return true
    return disj


def containsEmptyDizLabeled(SL):
    for diz, label in SL:
        if(diz==false):
            return True
    return False


def clearlyIncludingLabeled(p, SL):
    for i, dizL in enumerate(SL):
        if ~dizL[0] == p:
            return False
        for j in dizL[0].args:
            if(j == ~p):
                return False
    return True

def ChooseLiteralFromLabeled(cnfL):
    if(len(cnfL) == 0):
        return None
    for diz, label in cnfL:
        if(len(diz.args) == 0):
            continue
        lit = diz.args[0]
        return lit
    return None

def getPureLiteralFromLabeled(SL):
    for diz, label in SL:
        for lit in diz.args:
            if(clearlyIncludingLabeled(lit, SL)):
                return lit
    return None
    

def getEmptyDizLabeled(SL):
    for diz, label in SL:
        if(diz == false):
            return diz,label
    
def UnitPropogate(cnfL, A, B, litL):
    print(f"UnitPropogate for ({litL[0]}, {litL[1]})\n and SL = {cnfL}")
#    tmp = [c for c in S if lit in c]
#    tmp2 = [c for c in S if c not in tmp]
    sl = []
    for diz, label in cnfL:
        if isinstance(diz, Symbol) and litL[0].equals(diz):
            continue
        if isinstance(diz, Not) and diz.equals(litL[0]):
            continue
        if litL[0] not in diz.args:
            sl.append((diz, label))
    #sl = [cl for cl in cnfL if litL[0] not in cl[0].args and litL[0].equals(cl[0])]
    return EliminateLabeledLiteral(sl, A, B, ~litL[0], litL[1])

def EliminateLabeledLiteral(SL, A, B, lit, inter2 = false):
    p = lit.atoms().pop()
    nSLs = []
    print(f"elimination for {lit} and SL = {SL} and inter2 is {inter2}")

    for diz, inter in SL:
        #if(lit in diz):
        C = false
        for a in diz.args:
            print(f"a is {a}")
            if isinstance(a, Symbol) and a==lit:
                continue
            if isinstance(a, Symbol) and (not lit.equals(a)) or not a.equals( lit ):
                print(f"Here {a}")
                C = C | a
        if len(diz.args) == 0 and not lit.equals(diz):
            C = diz
            
        print(C)
        if((p in A.atoms() and (p not in B.atoms())) or ((p not in A.atoms()) and p in B.atoms())):        
            I = copy.deepcopy(inter)
            print(f"first I is {I}")
            CI = (C, I)
            nSLs.append(CI)
        elif(p in A.atoms() and p in B.atoms()):
            I = elim_contras_con(elim_contras_disj(inter | lit) & elim_contras_disj(lit | inter2))
            print(f"second I is {I}")
            CI = (C, I)
            nSLs.append(CI)   
            
        
    print(f"nSLs is {nSLs}")
    return nSLs

def containsSimpleDizLabeled(SL):
    #print(f"trouble HERE, SL is {SL}")
    for diz, label in SL:
        #print(f"i[0] is {i[0]}")
        if(len(diz.args)==1) or isinstance(diz, Symbol):
            return True
    return False

def getSimpleDizLabeled(SL):
    for diz, label in SL:
        if(len(diz.args)==1) or isinstance(diz, Symbol):
            return (diz, label)
    
def interpolantdsDPLL(SL, A, B, M):
    if(SL == true):
        return ('SAT', M)
    for diz, label in SL:
        if(diz == false):
            return ('UNSAT', None, label)
        
    while(containsSimpleDizLabeled(SL) or getPureLiteralFromLabeled(SL) != None):        
        while(containsSimpleDizLabeled(SL)):
            pL = getSimpleDizLabeled(SL)
            
            SL = UnitPropogate(SL, A, B, pL)
            if isinstance(pL[0], Symbol):
                M[pL[0]] = True
            else:
                M[pL[0]] = False
            print(f"Propogated for lit {pL[0]} and SL =", SL)
            
        print(f"SL is ", SL)
        if(len(SL) == 0):
            return ('SAT', M)
        if(containsEmptyDizLabeled(SL)):
            return ('UNSAT', None, getEmptyDizLabeled(SL)[1])
        
        while(getPureLiteralFromLabeled(SL) != None):
            l = getPureLiteralFromLabeled(SL)
            out = []
            for dizL in SL:
                if(l not in dizL[0].args):
                    out.append(dizL)
            SL = out
            print(f"PURE {l} was eliminated SL is {SL}", SL)
            if isinstance(l, Symbol):
                M[l] = True
            else:
                M[l] = False
        
    if(len(SL) == 0):
        return ('SAT', M)
    lit = ChooseLiteralFromLabeled(SL)
    print(M)
    print(f"lit is {lit}")
    print(f"SL is {SL}")
    if isinstance(lit, Symbol):
        M[lit] = True
    else:
        M[lit] = False
    tmp = false if lit.atoms()[0] in A.atoms() else true
    temp = interpolantdsDPLL(SL + [(lit, tmp)], A, B, M)
    if(temp[0] == 'SAT'):
        return temp
    else:
        if isinstance(lit, Symbol):
            M[lit] = True
        else:
            M[lit] = False
        return interpolantdsDPLL(SL + [(  ~lit, tmp  )], A, B, M)
    
    
def make_labels(A_cnf, B_cnf):
    tmp = A_cnf.args + B_cnf.args
    nSLs = []
    for a in tmp:
        if a in A_cnf.args:
            nSLs.append((a, false))
        else:
            nSLs.append((a, true))
    return nSLs

def interpoland_by_DPLL(SL, A, B, M):
    SL = make_labels(A, B)
    M = {atom: None for atom in (phi.atoms() | xi.atoms())}
    return interpolantdsDPLL(SL, A, B, M)

p,q,r, s = symbols('p q r s')
phi = (p | ~q) & (~p |~r) &q
xi = (~q|r)&(q|s)&~s

SL = make_labels(phi, xi)
M = {atom: None for atom in (phi.atoms() | xi.atoms())}
answer = interpolantdsDPLL(SL, phi, xi, M)

print(answer)

