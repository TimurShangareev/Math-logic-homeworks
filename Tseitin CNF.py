# -*- coding: utf-8 -*-
"""
Created on Tue Oct 19 22:49:05 2021

@author: chote
"""
"""
Формулы в содержат только коньюнкции, дизьюнкции и литералы, записываются в 
виде кортежей f = (a,b), где
a - тип связки логической ('var', '|', '!', '&')
b - аргументы формулы. Сам является формулой, либо, если f имеет тип 'var', 
    является одной из переменных. Если тип f - '&' или '|', то 2 аргумента.
Переменные задаются целыми неотрицательными числами
Не поддерживаются константные значения (истина ложь)
"""
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

def CNF(a,b, oldvar, newvar):
    if(a[0] == '!' and a[1][0] == '!'):
        a = (a[1][1][0], a[1][1][1])
        return CNF(a, b, oldvar, newvar)
    if(a[0] == 'var'):
        return [a,b]
    if(a[0] == '!'):
        x,y = CNF(a[1], b, oldvar, newvar)
        return [['!', x], y]
    if(a[0] == '&'):
        l1, d1 = CNF(a[1][0], b, oldvar, newvar)
        l2, d2 = CNF(a[1][1], d1, oldvar, newvar)
        p = search_new_var_name(oldvar, newvar)
        newvar.append(p)
        d = []+d2
        d.append(['|', [
            [l1[0], l1[1]], ['!', ['var', p]]
                    ]])
        d.append(['|', [
            [l2[0], l2[1]], ['!', ['var', p]]
                             ]])
        d.append(['|', [
            ['var', p], ['|', [
                ['!', l2], ['!', l1]
                ]]
            ]])
        return [['var', p], d]
    
    if(a[0] == '|'):
        l1, d1 = CNF(a[1][0], b, oldvar, newvar)
        l2, d2 = CNF(a[1][1], d1, oldvar, newvar)
        p = search_new_var_name(oldvar, newvar)
        newvar.append(p)
        d = []+d2
        d.append(['|', [
            ['!', [l1[0], l1[1]]], ['var', p]
                    ]])
        d.append(['|', [
            ['!', [l2[0], l2[1]]], ['var', p]
                             ]])
        d.append(['|', [
            ['!',['var', p]], [ '|', [
                ['/', [l1, l2]]
                ]]
            ]])
        return [['var', p], d]
    
empt=[]
oldvs = [0, 1, 2]
newvs = []

tmp = ['&', [
    ['var', 0], ['var', 1]
    ]]

phi = ['!', ['|', [
    tmp, ['!', ['var', 2]]
                   ]]]

l, d = CNF(phi, empt, oldvs, newvs)

def DPLL(S, M):
    if(len(S)==0):
        return