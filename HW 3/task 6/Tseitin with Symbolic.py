# -*- coding: utf-8 -*-
"""
Created on Thu Nov  4 10:54:14 2021

@author: chote
"""
def search_new_var_name(oldvar, newvar):
    if(len(newvar) == 0):
        return max(oldvar) + 1
    return max(newvar) + 1
  
    
class Formula:
    def __init__(self, sig = None, params = []):
        self.is_invert = False
        self.is_sym = False
        self.is_conj = False
        self.is_disj = False
        self.is_False = False
        self.is_True = False
        
        
        if(sig == '&'):
            self.is_conj = True
        elif(sig == '|'):
            self.is_disj = True
        elif(sig == '~'):
            self.is_invert = True
        elif(sig == False):
            self.is_False = True
        elif(sig == True):
            self.is_True = True
        elif isinstance(sig, str):
            self.is_sym = True
            
        if isinstance(sig, str):

            self.sym = sig
        
        self.parameters = params
        
    def __eq__(self, other):
        if(self.is_False and other.is_False or self.is_True and other.is_True):
            return True
        if self.sym==other.sym:
            if self.sym in ['&','|']:
                if(self.parameters[0]== other.parameters[0] and self.parameters[1] == other.parameters[1]
                    or self.parameters[1]== other.parameters[0] and self.parameters[0] == other.parameters[1]):
                    return True
                
            if self.sym == '~':
                return self.parameters[0] == other.parameters[0]
            
            if isinstance(self.sym, str):
                return True
            
    def __ne__(self, other):
        return not self.__eq__(other)
    
    def __and__(self, other):

        if other.is_True:
            return self
        if(other.is_False):
            return Formula(sig = False)
        if self.is_True:
            return other
        if(self.is_False):
            return Formula(sig = False)
        
        out = Formula('&', params= [self, other])

        return out
    
    def __or__(self, other):
        if other.is_True:
            return Formula(sig=True)
        if(other.is_False):
            return self
        if self.is_True:
            return Formula(sig = True)
        if(self.is_False):
            return other
        
        out = Formula('|', params= [self, other])
        
        return out
    
    def __invert__(self):
        out = Formula('~', params=[self])
        
        return out
    
    def atoms(self):
        if(self.is_True or self.is_False):
            return []
        if(self.is_sym):
            return self.sym
        out = []
        for p in self.parameters:
            out += p.atoms()
        return list(set(out))
    
    def __str__(self):
        if self.sym in ['&', '|']:
            return " ".join(( self.parameters[0].__str__(), self.sym, self.parameters[1].__str__()))
        if self.sym == '~':
            if self.parameters[0].is_conj or self.parameters[0].is_disj:
                return '~(' + self.parameters[0].__str__() + ')'
            return '~' + self.parameters[0].__str__()
        return self.sym
        
        
        
    
class Symbol(Formula):
    def __init__(self, sym = False):
        Formula.__init__(self)
        if sym == False:
            self.is_False = True
        elif sym == True:
            self.is_True = True
            
        self.sym = str(sym)
            
    def __eq__(self, other):
        if(self.is_False and other.is_False or self.is_True and other.is_True):
            return True
        if self.sym == other.sym:
            return True
        return False
    
    def __ne__(self, other):
        return not self.__eq__(other)
    
    def atoms(self):
        return self.sym
    
    def __and__(self, other):

        if other.is_True:
            return self
        if(other.is_False):
            return Symbol(sym = False)
        if self.is_True:
            return other
        if(self.is_False):
            return Formula(sym = False)
        
        out = Formula('&', params= [self, other])

        return out
    
    def __or__(self, other):
        if other.is_True:
            return Formula(sig=True)
        if(other.is_False):
            return self
        if self.is_True:
            return Formula(sig = True)
        if(self.is_False):
            return other
        
        out = Formula('&', params= [self, other])
        
        return out
    
    
A, B = Formula('A'), Formula('B')

print((A | ~(B & ~B |~A)).atoms())


