# -*- coding: utf-8 -*-
"""
Created on Sat Oct 30 16:59:27 2021

@author: chote
"""

"""
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
import copy
#%
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


def atoms_generator(S):
    for i, diz in enumerate(S):
        for lit in diz:
            yield abs(lit)   

def atoms(S):
    return list(set(atoms_generator(S)))
            

def CNF_non_rec(a,b, oldvar, newvar):
    #if()
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
        if(len(C) !=0 ):
            out.append(C)
    return out

def makeCLs(C):
    return list(map(lambda c: {c: [[]]}, C))
def makeDLs(D):
    return list(map(lambda c: {c: [[]]}, D))

def CNF_counts_same_clause(S, diz):
    counter = 0
    for diz_i in S:
        if(diz_i==diz):
            counter+=1
    return counter

def CNF_contains_double_clauses(S):
    for diz in S:
        if(CNF_counts_same_clause(S, diz) >= 2):
            return diz
    return None

def elimSameClauses(S):
    #S = list(map(lambda x: x[0], SL))
    S_copy = copy.deepcopy(S)
    while(CNF_contains_double_clauses(S_copy) != None):
        diz = CNF_contains_double_clauses(S_copy)
        for i in S_copy:
            if(i == diz):
                S_copy.remove(i)
                #print(f"copy removed: {S_copy}")
                if(i not in S_copy):
                    S_copy.append(i)
                    break
                
    return S_copy                
#S = [[3], [2], [2], [3], [2], [3]]
#S = [[2], [2], [2], [3]]
#print(f"ELIM_SAME_CLAUSES: {elimSameClauses(S)}")            
#print(f"CONTAINS_DOUBLE_CLAUSES: {CNF_contains_double_clauses(S)}")  


def contains_contra(S, lit):
    for diz in S:
        if(len(diz) == 1 and diz[0] == -lit):
            return True
    return False

def elim_contras(S, lit):
    while([-lit] in S):
        S.remove([-lit])
    '''
    for diz in S:
        if(len(diz) == 1 and diz[0] == -lit):
            S.remove(diz)
    '''
    return

def elim_All_contras(S):
    should_remove = set()
    S_copy = copy.deepcopy(S)
    contra_Found = False
    for diz in S_copy:
        if(len(diz) == 1 and contains_contra(S_copy, diz[0])):
            contra_Found = True
            elim_contras(S_copy, diz[0])
            should_remove.add(diz[0])
    should_remove = list(map(lambda x: [x], should_remove))
    while(len(should_remove) > 0):
        diz = should_remove.pop()
        while(diz in S_copy):
            S_copy.remove(diz)
    if(contra_Found and [] not in S_copy):
        S_copy.append([])
    return S_copy            


def EliminateLabeledLiteral(SL, atPHI, atXI, lit, inter2):
    out = []
    p = abs(lit)
    nSLs = []
    nCLs = []
    nDLs = []
    print(f"elimination for p and SL = {p} and {SL}")
    if((p in atPHI and (p not in atXI)) or ((p not in atPHI) and p in atXI)):        
        for pair in SL:
            diz, inter = pair
            #if(lit in diz):
            C = [l for l in diz if l != lit]
            I = copy.deepcopy(inter)
            CI = (C, I)
            nSLs.append(CI)
    

    if(p in atPHI and p in atXI):
        for pair in SL:
            diz, inter = pair
            #if(lit in diz):
            C = [l for l in diz if l != lit]
            '''
            if(not isDizIn(diz, CLs)):
                I2 = copy.deepcopy(inter)
                for c in range(I2):
                    I2[c].append(-lit)
                I = [[lit]]+I2
                
            elif(not isDizIn(diz, DLs)):
                I1 = copy.deepcopy(inter)
                for i, c in enumerate(I1):
                    I1[i].append(-lit)
                I = I1
            '''
            print(f"Added clause C = {C}")
            I = copy.deepcopy(inter)
            print(f"inter is {I}")
            for i in range(len(I)):
                I[i].append(lit)
            I2 = copy.deepcopy(inter2)                
            for i in range(len(I2)):
                I2[i].append(-lit)
            CI = (C, elim_All_contras(I+I2))
            nSLs.append(CI)
        
    print(f"nSLs is {nSLs}")
    return nSLs

def UnitPropogate(SL, atPHI, atXI, lit):
    print(f"UnitPropogate for (lit, inter) = ({lit[0][0]}, {lit[1]})\n and SL =", SL)
#    tmp = [c for c in S if lit in c]
#    tmp2 = [c for c in S if c not in tmp]
    s = [c for c in SL if lit[0][0] not in c[0]]
    return EliminateLabeledLiteral(s, atPHI, atXI, -lit[0][0], lit[1])

def clearlyIncludingLabeled(p, SL):
    for i, v in enumerate(SL):
        for j in v[0]:
            if(j == -p):
                return False
    return True

def ChooseLiteralLabeled(SL):
    if(len(SL) == 0):
        return None
    for diz in SL:
        if(len(diz[0]) == 0):
            continue
        lit = diz[0][0]
        return lit
    return None
    
def containsSimpleDizLabeled(SL):
    #print(f"trouble HERE, SL is {SL}")
    for i in SL:
        #print(f"i[0] is {i[0]}")
        if(len(i[0])==1):
            return True
    return False


   
def getSimpleDizLabeled(SL):
    for i in SL:
        if(len(i[0])==1):
            return i
        
def containsEmptyDizLabeled(SL):
    for v in SL:
        if(len(v[0]) == 0):
            return True
    return False

def getEmptyDizLabeled(SL):
    for v in SL:
        if(len(v[0]) == 0):
            return v
        
def getPureLiteralLabeled(SL):
    for diz in SL:
        for lit in diz[0]:
            if(clearlyIncludingLabeled(lit, S)):
                return lit
    return None
    

def isDizInLabeled(diz, SL):
    for d in SL:
        if(d[0] == diz):
            return True
    return False
    
def createLabeledS(S):
    mid = len(S)/2
    atPHI = atoms(S[:mid])
    atXI  = atoms(S[mid:])
    CL = list(map(lambda c: (c, [[]]), S[:mid]))
    DL = list(map(lambda c: (c, []), S[mid:]))
    return CL+DL, atPHI, atXI

def interpolantdsDPLL(SL, atPHI, atXI, M):
    if(len(SL)==0):
        return ('SAT', M)
    for diz in SL:
        if(len(diz[0]) == 0):
            return ('UNSAT', None, diz[1])
        
    while(containsSimpleDizLabeled(SL) or getPureLiteralLabeled(SL) != None):        
        while(containsSimpleDizLabeled(SL)):
            diz = getSimpleDizLabeled(SL)
            
            #if(M[abs(diz[0][0])] == -sign(diz[0][0])):
            #    return ('UNSAT', None, diz[1])
            #print(f"DPLL Simple diz is {diz}")
            SL = UnitPropogate(SL, atPHI, atXI, diz)
            M[abs(diz[0][0])] = sign(diz[0][0])
            print(f"Propogated for lit {diz[0][0]} and SL =", SL)
            
        print(f"SL is ", SL)
        if(len(SL) == 0):
            return ('SAT', M)
        if(containsEmptyDizLabeled(SL)):
            return ('UNSAT', None, getEmptyDizLabeled(SL)[1])
        
        while(getPureLiteralLabeled(SL) != None):
            l = getPureLiteralLabeled(SL)
            out = []
            for v in SL:
                if(l not in v[0]):
                    out.append(v)
            S = out
            print(f"PURE {l} was eliminated SL is ", SL)
            M[abs(l)] = sign(l)
        
    if(len(SL) == 0):
        return ('SAT', M)
    lit = ChooseLiteralLabeled(SL)
    print(M)
    print(f"lit is {lit}")
    print(f"SL is", SL)
    M[abs(lit)] = sign(lit)
    tmp = [[]] if abs(lit) in atPHI else []
    temp = interpolantdsDPLL(SL + [(  [lit], tmp  )], atPHI, atXI, M)
    if(temp[0] == 'SAT'):
        return ('SAT', temp[1])
    else:
        M[abs(lit)] = sign(lit)
        return interpolantdsDPLL(SL + [(  [-lit], tmp  )], atPHI, atXI, M)
    
    
    
    
    
    
    
    

M = [None for _ in range(len(oldvs)+len(newvs) + 1)]


phi = [[1,-2], [-1,-3], [2]]
xi = [[-2, 3], [2, 4], [-4]]
M = [None]*5
S = phi+xi

atPHI = atoms(phi)
atXI  = atoms(xi)
print(f"atPhi is {atPHI}")
print(f"atXI is {atXI}")
CL = list(map(lambda c: (c, [[]]), phi))
DL = list(map(lambda c: (c, []), xi))

answer = interpolantdsDPLL(CL+DL, atPHI, atXI, M)
print(f"\n\nS is {S}")
print(f"\n\nANSWER IS {answer}")



def interpolants_DPLL_start(C, D, M):
    C1 = list(map(lambda c: {c: [[]]}, C))
    D1 = list(map(lambda c: {c: []}, D))
    
    
def interps_DPLL(S, M):
    if(len(S)==0):
        return ('SAT', M)
    for diz in S:
        if(len(diz) == 0):
            return ('UNSAT', None)

