#!/usr/bin/env python

"""
Copyright (c) 2009, Daniela Inclezan
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the KRLAB nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY DANIELA INCLEZAN ``AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL DANIELA INCLEZAN BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS   
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
This software follows a model by Gregory Gelfond.
"""


"""
Copyright (c) 2009, Gregory Gelfond
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the KRLAB nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY GREGORY GELFOND ``AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL GREGORY GELFOND BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS   
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"""

import optparse
import sys
import string

from lepl import *

# =====================================
# PREDEFINED STRINGS
# =====================================

NO_INPUT_FILE = 'no input file'


# For the translation to ASP:

GENERAL_AXIOMS = '% General Axioms:\n\n' + \
                 'dom(nodes).\n\n' + \
                 'dom(universe).\n' + \
                 'is_a(universe, nodes).\n\n' + \
                 'dom(actions).\n' + \
                 'is_a(actions, nodes).\n' + \
                 'link(actions, universe).\n\n' + \
                 'dom(booleans).\n' + \
                 'is_a(booleans, nodes).\n' + \
                 'link(booleans, universe).\n\n' + \
                 'instance(X, nodes) :-\n\t' + \
                        'is_a(X, nodes).\n\n' + \
                 'instance(X, Y) :- \n\t' + \
                    'is_a(X, Y), \n\t' + \
                    'dom(X), \n\t' + \
                    'dom(Y), \n\t' + \
                    'is_a(Y, nodes). \n\n' + \
                 'instance(X, Y) :- \n\t' + \
                    'instance(X, Z), \n\t' + \
                    'link(Z, Y), \n\t' + \
                    'dom(X), \n\t' + \
                    'dom(Y), \n\t' + \
                    'dom(Z), \n\t' + \
                    'instance(Y, nodes), \n\t' + \
                    'instance(Z, nodes). \n\n'


# =====================================
# GLOBAL VARS/ STRUCTURES
# =====================================

static = True
basic = True

functions = {}

superclasses = {}

instances = {}

# =====================================
# UTILITY FUNCTIONS
# =====================================

def is_variable(text):
    return text[0].isupper()

def is_constant(text):
    return text[0].islower()


# =====================================================================

class SortDecl(object):
    """
    Objects of type SortDecl correspond to sort declarations of the 
    language of ALM. Sort declarations are statements of the form:
            s1, ..., sk :: c1, ..., cn
    where:
            s1, ..., sk, c1, ..., cn   -- are sort names
            k >= 1 and n >= 1
    """
    
    def __init__(self, new_sorts, supersorts):
        """
        Creates a new object of the type SortDecl given the list of
        sort names and the supersort.
        """
        global crt_sorts
        crt_sorts = new_sorts
        
        super(SortDecl, self).__init__()
        self.new_sorts = new_sorts
        self.supersorts = supersorts

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        global superclasses
        global instances
        
        s = ''
        for x in self.new_sorts:
            s = s + 'dom(' + x + ').\nis_a(' + x + ', nodes).\n'
            sups = []
            for y in self.supersorts:
                s = s + 'link(' + x + ', ' + y + ').\n\n'
                sups.append(y)
                for z in superclasses[y]:
                    sups.append(z)
            superclasses[x] = sups
            instances[x] = set()
        return s

# =====================================================================

class AttrDecl(object):
    """
    Objects of type AttrDecl correspond to attribute declarations of the 
    language of ALM. Attribute declarations are statements of the form:
            f1, ..., fk : s0 * ... * sn -> s
    where:
            f1, ..., fk  -- are attribute names, k >= 1
            s0, ..., sn -- are sort names with n >= 0
            (If n = 0 then the part "s0 *... * sn -> " is ommitted)
            s -- is a sort name
    """

   
    def __init__(self, attr_names, param_sorts, return_sort):
        """
        Creates a new object of the type AttrDecl given:
        - the list of attributes declared in this attribute declaration,
        - the list of sorts of its parameters (excludig the sort of the first
        implicit parameter, which is the sort to which the attribute
        declaration belongs), and
        - the range of the attribute.
        """
        super(AttrDecl, self).__init__()
        global functions
        
        self.attr_names = attr_names
        self.param_sorts = param_sorts

        if len(crt_sorts) > 1:
            print 'Error: Attributes cannot be specified for multiple sorts at a time.'
        else:
            self.param_sorts.insert(0, crt_sorts[0])
            
        self.return_sort = return_sort

        for attr_name in self.attr_names:
            function_info = []
            function_info.append(static)
            function_info.append(self.param_sorts)
            function_info.append(self.return_sort)
            functions[attr_name] = function_info

    def whenStaticAndReturnSortBooleans(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')

        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t') 
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')
        return s
    
    def whenReturnSortNotBooleans(self):
        s = ''
        for attr_name in self.attr_names:
            s = s + "#nherb " + attr_name + "/" +\
                    str(len(self.param_sorts)) + ".\n\n" 
            s = s + '% Definition of dom_' + attr_name + '\n\n'
            s = s + 'dom_' + attr_name + '('
            s = s + concatenateParams(self.param_sorts, ') :-\n\t')  
            s = s + attr_name + '('
            s = s + concatenateParams(self.param_sorts, ') #= X,\n\t') 
            s = s + constructInstance(self.param_sorts, ',\n\tinstance(X, ' + self.return_sort + ').\n\n')
        return s

    def whenReturnSortBooleans(self):
        s = ''
        for attr_name in self.attr_names:
            s = s + '% Definition of dom_' + attr_name + '\n\n'
            s = s + 'dom_' + attr_name + '('
            s = s + concatenateParams(self.param_sorts, ') :-\n\t')
            s = s + attr_name + '('
            s = s + concatenateParams(self.param_sorts, '),\n\t') 
            s = s + constructInstance(self.param_sorts, '.\n\n')

            s = s + 'dom_' + attr_name + '('
            s = s + concatenateParams(self.param_sorts, ') :-\n\t') 
            s = s + '-' + attr_name + '('
            s = s + concatenateParams(self.param_sorts, '),\n\t') 
            s = s + constructInstance(self.param_sorts, '.\n\n')
        return s

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        s = ''

        if self.return_sort == "booleans" :
            s = s + self.whenReturnSortBooleans()
        else :
            s = s + self.whenReturnSortNotBooleans()

        for attr_name in self.attr_names:
            s = s + '% CWA for dom_' + attr_name + '\n\n'
            s = s + '-dom_' + attr_name + '('
            s = s + concatenateParams(self.param_sorts, ') :-\n\t') 
            s = s + 'not dom_' + attr_name + '('
            s = s + concatenateParams(self.param_sorts, '),\n\t') 
            s = s + constructInstance(self.param_sorts, '.\n\n')

        return s

    
# =====================================================================

class FunctionTypeResetter(object):
    def __init__(self, type_str):
        """
        """
        super(FunctionTypeResetter, self).__init__()

        global static
        global basic
        
        if type_str == 'statics':
            static = True
        elif type_str == 'fluents':
            static = False
        elif type_str == 'basic':
            basic = True
        elif type_str == 'defined':
            basic = False
     
    
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        #TODO
        return ''                       
            
        

# =====================================================================
def concatenateParams(params, ending):
    s = ''
    for i in range(0, len(params)):
        s = s + 'X' + str(i + 1)
        if i < len(params) - 1:
            s = s + ', '
    s = s + ending
    return s

def constructInstance(params, ending):
    s = ''
    for i in range(0, len(params)):
        s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + params[i] + ')'
        if i < len(params) - 1:
            s = s + ',\n\t'
    s = s + ending
    return s

class FunctionDecl(object):
    """
    Objects of type FunctionDecl correspond to function declarations of the 
    language of ALM. Function declarations are statements of the form:
            f : s1 * ... * sn -> s
    where:
            s1, ..., sn, s   -- are sort names
            n >= 1
    """
    
    def __init__(self, total, function_name, param_sorts, return_sort):
        """
        Creates a new object of the type FunctionDecl given ...
        """
        super(FunctionDecl, self).__init__()
        global functions
        self.total = total
        self.function_name = function_name
        self.param_sorts = param_sorts
        self.return_sort = return_sort
        self.basic = basic
        self.static = static

        function_info = []
        function_info.append(static)
        function_info.append(param_sorts)
        function_info.append(return_sort)
        functions[function_name] = function_info

    def forAllFunctions(self):
        s = ''
        s = s + '% CWA for dom_' + self.function_name + '\n\n'
        s = s + '-dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')
        s = s + 'not dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t')     
        s = s + constructInstance(self.param_sorts, '.\n\n')
        return s
    def whenReturnSortBooleans(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')
        return s
    def whenReturnSortNotBooleans(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t') 
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') #= X,\n\t') 
        s = s + constructInstance(self.param_sorts, ',\n\tinstance(X, ' + self.return_sort + ').\n\n')
        return s
    def whenStaticAndReturnSortBooleans(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')

        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t') 
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')
        return s
    def whenStaticAndReturnSortNotBooleans(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')  
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') #= X,\n\t') 
        s = s + constructInstance(self.param_sorts, ',\n\tinstance(X, ' + self.return_sort + ').\n\n')
        return s
    def whenBasicNotStaticAndReturnSortBooleans(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I) :-\n\t') 
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t') 
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')

        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I) :-\n\t') 
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t') 
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')
        return s
    def whenBasicNotStaticAndReturnSortNotBooleans(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I) :-\n\t')  
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I) #= X,\n\t') 
        s = s + constructInstance(self.param_sorts, ',\n\tinstance(X, ' + self.return_sort + '),\n\tstep(I).\n\n')
        return s
    def whenNotBasicNotStatic(self):
        s = ''
        s = s + '% Definition of dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')
        s = s + '% CWA for ' + self.function_name + '\n\n'
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I) :-\n\t')            
        s = s + 'not ' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t')
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')
        return s
    def whenBasicStatic(self):
        s = ''
        s = s + '% CWA for dom_' + self.function_name + '\n\n'
        s = s + '-dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t') 
        s = s + 'not dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')
        return s
    def whenNotBasicStatic(self):
        s = ''
        s = s + '% CWA for dom_' + self.function_name + '\n\n'
        s = s + '-dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')
        s = s + 'not dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t') 
        s = s + constructInstance(self.param_sorts, '.\n\n')
        s = s + '% CWA for ' + self.function_name + '\n\n'
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ') :-\n\t')
        s = s + 'not ' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t')        
        s = s + constructInstance(self.param_sorts, '.\n\n')
        return s
    def whenBasicNotStatic(self):
        s = ''
        s = s + '% Inertia Axioms for dom_' + self.function_name + '\n\n'
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1) :-\n\t')          
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t')     
        s = s + 'not -dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1),\n\t') 
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')
        
        s = s + '-dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1) :-\n\t') 
        s = s + '-dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t') 
        s = s + 'not dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1),\n\t')            
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')

        s = s + '% Inertia Axioms for ' + self.function_name + '\n\n'
        return s
    def whenBasicNotStaticAndReturnSortBooleansMore(self):
        s = ''
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1) :-\n\t') 
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1),\n\t')
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t') 
        s = s + 'not -' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1),\n\t')                 
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1) :-\n\t') 
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1),\n\t')
        s = s + '-' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t') 
        s = s + 'not ' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1),\n\t')               
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')
        return s
    def whenBasicNotStaticAndReturnSortNotBooleansMore(self):
        s = ''
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1) #= X :-\n\t')               
        s = s + 'dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1),\n\t') 
        s = s + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I) #= X,\n\t')                 
        s = s + 'not ' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I + 1) #!= X,\n\t') 
        s = s + constructInstance(self.param_sorts, ',\n\tinstance(X, ' + self.return_sort +  '),\n\tstep(I).\n\n')
        return s
    def whenTotalStatic(self):
        s = ''
        s = s + '% ' + self.function_name + ' is a total function\n'
        s = s + ':- -dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, '),\n\t')
        s = s + constructInstance(self.param_sorts, '.\n\n')
        return s
    def whenTotalNotStatic(self):
        s = ''
        s = s + '% ' + self.function_name + ' is a total function\n\n'
        s = s + ':- -dom_' + self.function_name + '('
        s = s + concatenateParams(self.param_sorts, ', I),\n\t')
        s = s + constructInstance(self.param_sorts, ',\n\tstep(I).\n\n')
        return s
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        #TODO
        s = '\n'
        #s = s + self.forAllFunctions()
        #if self.return_sort == "booleans" :
        #    s = s + self.whenReturnSortBooleans()
        #else :
        #    s = s + self.whenReturnSortNotBooleans()

        if self.return_sort != "booleans" :
            if self.static:
                s = s + "#nherb " + self.function_name + "/" +\
                    str(len(self.param_sorts)) + ".\n\n"
            else:
                s = s + "#nherb " + self.function_name + "/" +\
                    str(len(self.param_sorts)+1) + ".\n\n"

        if self.static :
            if self.return_sort == "booleans" :
                s = s + self.whenStaticAndReturnSortBooleans()
            else :
                s = s + self.whenStaticAndReturnSortNotBooleans()
        if self.basic and not self.static :
            if self.return_sort == "booleans" :
                s = s + self.whenBasicNotStaticAndReturnSortBooleans()
            else :
                s = s + self.whenBasicNotStaticAndReturnSortNotBooleans()

        if not self.static and not self.basic :
            s = s + self.whenNotBasicNotStatic()
        if self.basic and self.static :
            s = s + self.whenBasicStatic()
        if not self.basic and self.static :
            s = s + self.whenNotBasicStatic()
        if self.basic and not self.static :
            s = s + self.whenBasicNotStatic()
            if self.return_sort == "booleans" :
                s = s + self.whenBasicNotStaticAndReturnSortBooleansMore()
            else :
                s = s + self.whenBasicNotStaticAndReturnSortNotBooleansMore()

        if not self.static and not self.basic :
            s = s + self.whenNotBasicNotStatic()

        if 'total' in self.total:
            if self.static :
                s = s + self.whenTotalStatic()
            else:
                s = s + self.whenTotalNotStatic()
        return s

# =====================================================================

class ConstantDecl(object):
    """
    Objects of type ConstantDecl correspond to object constant declarations of the 
    language of ALM, which are statements of the form:
            o1, ..., ok : c1, ..., cn
    where:
            o1, ..., ok  -- are constant names
            c1, ..., cn   -- are sort names
            k >= 1 and n >= 1
    """
    
    def __init__(self, constants, sorts):
        """
        Creates a new object of the type ConstantDecl given the list of
        constant names and the sorts.
        """
     
        super(ConstantDecl, self).__init__()
        self.constants = constants
        self.sorts = sorts

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        global instances
        
        s = ''
        for x in self.constants:
            s = s + 'dom(' + x + ').\n'
            for y in self.sorts:
                s = s + 'is_a(' + x + ', ' + y + ').\n\n'
                instances[y].add(x)
                for z in superclasses[y]:
                    instances[y].add(x)
        return s
        
# =====================================================================

class Axioms(object):
    """
    Objects of type Axioms correspond to axioms of system descriptions,
    declared as:
            axioms <list of axioms>
    """
    
    def __init__(self):
        """
        Creates a new object of the type Axioms.       
        """
        super(Axioms, self).__init__()       

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return '% Axioms\n\n'

# =====================================================================

class DynamicCausalLaw(object):
	"""
	Objects of type DynamicCausalLaw correspond to dynamic causal laws of
	the language of ALM. Dynamic causal laws are statements of the form:
		occurs(a) causes l if p
	where:
		a    -- is a variable or a constant
		l    -- is an basic fluent literal
		p    -- is a set of literals
	"""
	
	def __init__(self, occ, head, body):
		"""
		Creates a new object of the type DynamicCausalLaw given: 
		occ - the "occurs" expression represented as a list [occurs, a]
		head - the head literal represented as a list
		body - the body literals represented as a list
		"""
		super(DynamicCausalLaw, self).__init__()
		self.occ = occ
		self.head = head
		self.body = body
		self.variables = get_vars([occ, head, body])


        def determineStepVariable(self):
            if 'I' in self.variables:
                i = 1
                while 'I' + str(i) not in self.variables :
                    i += 1
                return 'I' + str(i)
            else :
                return 'I'
        def assembleHead(self, a_set, step):
            s = ''
            # assemble head
            s = s + self.head[0] + '('
            for i in range(0, len(self.head[1])) :
                s = s + self.head[1][i]
                if i < len(self.head[1]) - 1:
                    s = s + ', '
            s = s + ', ' + step + ' + 1) '
            for i in range(2, len(self.head)) : 
                s = s + self.head[i]
                if i < len(self.head) - 1:
                    s = s + ' '
            s = s + ' :-\n\t'

            functionName = ''
            if self.head[0][0] == '-' :
                functionName = self.head[0][1:]
            else :
                functionName = self.head[0]
            if functionName in functions :
                for i in range(0, len(self.head[1])) :
                    temps = "instance(" + self.head[1][i] + ", " + functions[functionName][1][i] + ")"   
                    a_set.add(temps)

            s = string.replace(s, " = ", " #= ")
            return s
        def assembleOCC(self, a_set, step):
            temps = ''
            temps = temps + self.occ[0] + '('
            for i in range(1, len(self.occ)) :
                temps = temps + self.occ[i]
                if i < len(self.occ) - 1:
                    temps = temps + ', '
            temps = temps + ', ' + step + ')'
            a_set.add(temps)
            for i in range(1, len(self.occ)) :
                a_set.add('instance(' + self.occ[i] + ', actions)') 
        def dealWithArithmeticExpression(self, a_set, j):
            temps = ''
            for i in range(0, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            a_set.add(temps)
        def dealWithStaticExpression(self, a_set, j):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ') '
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            temps = string.replace(temps, " != ", " #!= ")
            temps = string.replace(temps, " = ", " #= ")
            a_set.add(temps)
        def dealWithFluentExpression(self, a_set, j, step):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ', ' + step + ') '
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            temps = string.replace(temps, " != ", " #!= ")
            temps = string.replace(temps, " = ", " #= ")                   
            a_set.add(temps)
        def dealWithOtherExpression(self, a_set, j):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ')'
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            a_set.add(temps)
        def assembleAllExpression(self, a_set):
            s = ''
            i = 0
            for item in a_set:
                s = s + item
                if i < len(a_set) - 1:
                    s = s + ',\n\t'
                i = i + 1
            s = s + '.\n\n'
            return s
        def assembleBody(self, a_set, step):
            s = ''
            for j in range(0, len(self.body)):
                # literal is an arithmetic expression
                if isinstance(self.body[j][1], str):
                    self.dealWithArithmeticExpression(a_set, j)
                else:
                    if self.body[j][0][0] == '-' :
                        functionName = self.body[j][0][1:]
                    else :
                        functionName = self.body[j][0]
                    if functionName in functions:
                        for i in range(0, len(self.body[j][1])):
                            temps = "instance(" + self.body[j][1][i] + ", " + functions[functionName][1][i] + ")"   
                            a_set.add(temps)
                        if len(self.body[j]) > 3:
                            temps = "instance(" + self.body[j][3] + ", " + functions[functionName][2] + ")"   
                            a_set.add(temps)
                        # static
                        if functions[functionName][0]:  
                            self.dealWithStaticExpression(a_set, j)
                        else :
                            # fluent
                            self.dealWithFluentExpression(a_set, j, step)
                    else:
                        self.dealWithOtherExpression(a_set, j)
            s = s + self.assembleAllExpression(a_set)      
            return s

        def logic_program_form(self):
            """
            Returns the translation into ASP
            """
            #TODO
            # determine step variable
            a_set = set()
            step = self.determineStepVariable()
            s = ''
            # assemble head
            s = s + self.assembleHead(a_set, step)
            # occ
            self.assembleOCC(a_set, step)
            # body
            s = s + self.assembleBody(a_set, step)
            return s

# =====================================================================

class ExecutabilityCondition(object):
	"""
	Objects of type ExecutabilityCondition correspond to executability
	conditions the language of ALM. These are statements of the form:
		impossible occurs(a) if p
	where:
		a    -- is a variable or a constant
		p    -- is a set of literals or expressions [-]occurs(a)
	"""
	
	# TODO: handle occurs expressions in the body!!!
	
	def __init__(self, occ, body):
		"""
		Creates a new object of the type ExecutabilityCondition given: 
		occ - the "occurs" expression represented as a list [occurs, a]
		body - the body literals represented as a list
		"""
		super(ExecutabilityCondition, self).__init__()
		self.occ = occ
		self.body = body
		self.variables = get_vars([occ, body])


        def determineStepVariable(self):
            if 'I' in self.variables:
                i = 1
                while 'I' + str(i) not in self.variables :
                    i += 1
                return 'I' + str(i)
            else :
                return 'I'

        def assembleOCC(self, a_set, step):
            s = '-'
            s = s + self.occ[0] + '('
            for i in range(1, len(self.occ)) :
                s = s + self.occ[i]
                if i < len(self.occ) - 1:
                    s = s + ', '
            s = s + ', ' + step + ') :-\n\t'

            a_set.add('step(' + step + ')')
            for i in range(1, len(self.occ)) :
                a_set.add('instance(' + self.occ[i] + ', actions)')
            return s
            
        def dealWithArithmeticExpression(self, a_set, j):
            temps = ''
            for i in range(0, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            a_set.add(temps)
        def dealWithStaticExpression(self, a_set, j):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ') '
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            temps = string.replace(temps, " != ", " #!= ")
            temps = string.replace(temps, " = ", " #= ")
            a_set.add(temps)
        def dealWithFluentExpression(self, a_set, j, step):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ', ' + step + ') '
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            temps = string.replace(temps, " != ", " #!= ")
            temps = string.replace(temps, " = ", " #= ")                    
            a_set.add(temps)
        def dealWithOtherExpression(self, a_set, j):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ')'
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            a_set.add(temps)
        def assembleAllExpression(self, a_set):
            s = ''
            i = 0
            for item in a_set:
                s = s + item
                if i < len(a_set) - 1:
                    s = s + ',\n\t'
                i = i + 1
            s = s + '.\n\n'
            return s
        def assembleBody(self, a_set, step):
            s = ''
            for j in range(0, len(self.body)):
                # literal is an arithmetic expression
                if isinstance(self.body[j][1], str):
                    self.dealWithArithmeticExpression(a_set, j)
                else:
                    if self.body[j][0][0] == '-' :
                        functionName = self.body[j][0][1:]
                    else :
                        functionName = self.body[j][0]
                    if functionName in functions:
                        for i in range(0, len(self.body[j][1])):
                            temps = "instance(" + self.body[j][1][i] + ", " + functions[functionName][1][i] + ")"   
                            a_set.add(temps)
                        if len(self.body[j]) > 3:
                            temps = "instance(" + self.body[j][3] + ", " + functions[functionName][2] + ")"   
                            a_set.add(temps)
                        # static
                        if functions[functionName][0]:  
                            self.dealWithStaticExpression(a_set, j)
                        else :
                            # fluent
                            self.dealWithFluentExpression(a_set, j, step)
                    else:
                        self.dealWithOtherExpression(a_set, j)
            s = s + self.assembleAllExpression(a_set)      
            return s

        def logic_program_form(self):
            """
            Returns the translation into ASP
            """
            #TODO
            # determine step variable
            a_set = set()
            step = self.determineStepVariable()
            # occ
            s = self.assembleOCC(a_set, step)
            # body
            s = s + self.assembleBody(a_set, step)
            return s

# =====================================================================

class StateConstraint(object):
	"""
	Objects of type StateConstraint correspond to state constraints of
	the language of ALM. State Constraints are statements of the form:
		l if p
	where:
		l    -- is a literal
		p    -- is a set of literals
	"""
	
	def __init__(self, head, body):
		"""
		Creates a new object of the type StateConstraint given: 
		head - the head literal represented as a list
		body - the body literals represented as a list
		"""
		super(StateConstraint, self).__init__()
		self.head = head
		self.body = body
		self.variables = get_vars([head, body])


        def determineStepVariable(self):
            if 'I' in self.variables:
                i = 1
                while 'I' + str(i) not in self.variables :
                    i += 1
                return 'I' + str(i)
            else :
                return 'I'
        def assembleHead(self, a_set, step):
            global static
            
            s = ''
            # assemble head
            if self.head[0] == 'false':
                s = s + ':-  '
            else:
                functionName = ''
                if self.head[0][0] == '-' :
                    functionName = self.head[0][1:]
                else :
                    functionName = self.head[0]
                    
                s = s + self.head[0] + '('
                for i in range(0, len(self.head[1])) :
                    s = s + self.head[1][i]
                    if i < len(self.head[1]) - 1:
                        s = s + ', '
                if not functions[functionName][0]:               
                    s = s + ', ' + step
                    a_set.add('step(' + step + ')')
                s = s + ') '
                for i in range(2, len(self.head)) : 
                    s = s + self.head[i]
                    if i < len(self.head) - 1:
                        s = s + ' '
                s = s + ' :-\n\t'

                if functionName in functions :
                    for i in range(0, len(self.head[1])) :
                        temps = "instance(" + self.head[1][i] + ", " + \
                                functions[functionName][1][i] + ")"   
                        a_set.add(temps)

                s = string.replace(s, " = ", " #= ")
            return s
        def dealWithArithmeticExpression(self, a_set, j):
            temps = ''
            for i in range(0, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            a_set.add(temps)
        def dealWithStaticExpression(self, a_set, j):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ') '
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            temps = string.replace(temps, " != ", " #!= ")
            temps = string.replace(temps, " = ", " #= ")
            a_set.add(temps)
        def dealWithFluentExpression(self, a_set, j, step):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ', ' + step + ') '
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            temps = string.replace(temps, " != ", " #!= ")
            temps = string.replace(temps, " = ", " #= ")                   
            a_set.add(temps)
        def dealWithOtherExpression(self, a_set, j):
            temps = ''
            temps = temps + self.body[j][0] + '('
            for i in range(0, len(self.body[j][1])):
                temps = temps + self.body[j][1][i]
                if i < len(self.body[j][1]) - 1:
                    temps = temps + ', '
            temps = temps + ')'
            for i in range(2, len(self.body[j])):
                temps = temps + self.body[j][i]
                if i < len(self.body[j]) - 1:
                    temps = temps + ' '
            a_set.add(temps)
        def assembleAllExpression(self, a_set):
            s = ''
            i = 0
            for item in a_set:
                s = s + item
                if i < len(a_set) - 1:
                    s = s + ',\n\t'
                i = i + 1
            s = s + '.\n\n'
            return s
        def assembleBody(self, a_set, step):
            s = ''
            for j in range(0, len(self.body)):
                # literal is an arithmetic expression
                if isinstance(self.body[j][1], str):
                    self.dealWithArithmeticExpression(a_set, j)
                else:
                    # if the first character of the literal is '-'
                    if self.body[j][0][0] == '-' :
                        functionName = self.body[j][0][1:]
                    else :
                        functionName = self.body[j][0]
                    if functionName in functions:
                        for i in range(0, len(self.body[j][1])):
                            temps = "instance(" + self.body[j][1][i] + ", " +\
                                    functions[functionName][1][i] + ")"   
                            a_set.add(temps)
                        
                        if len(self.body[j]) > 3:
                            temps = "instance(" + self.body[j][3] + ", " +\
                                    functions[functionName][2] + ")"   
                            a_set.add(temps)
                        # static
                        if functions[functionName][0]:  
                            self.dealWithStaticExpression(a_set, j)
                        else :
                            # fluent
                            self.dealWithFluentExpression(a_set, j, step)
                    else:
                        self.dealWithOtherExpression(a_set, j)
            s = s + self.assembleAllExpression(a_set)      
            return s

        def logic_program_form(self):
            """
            Returns the translation into ASP
            """
            #TODO
            # determine step variable
            a_set = set()
            step = self.determineStepVariable()
            s = ''
            # assemble head
            s = s + self.assembleHead(a_set, step)
            # body
            s = s + self.assembleBody(a_set, step)
            return s

	    
# =====================================================================

class SystemDescription(object):
    """
    Objects of type SystemDescription correspond to system descriptions 
    of the language of ALM. System descriptions are statements of the 
    form:
            system description <name>
                theory <name1>
                    [module]+
                structure <name2>
                     <structure description>
    where:
            <name>, <name1>, <name2>   -- are constants
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type SystemDescription given the        
        system description name.
        """
        super(SystemDescription, self).__init__()
        self.name = name

        global superclasses
        superclasses['universe'] = []
        superclasses['actions'] = ['universe']
        superclasses['booleans'] = ['universe']

        global instances
        instances['universe'] = set()
        instances['actions'] = set()
        instances['booleans'] = set()
        
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return '% ASP{f} Translation of System Description ' + self.name + '\n\n'   

# =====================================================================

class Theory(object):
    """
    Objects of type Theory correspond to theories of system descriptions
    of the language of ALM. Theories are statements of the form:
            theory <name>
                [module]+
    where:
            <name>   -- is a constant
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type Theory given the        
        theory name.
        """
        super(Theory, self).__init__()
        self.name = name

    def logic_program_form(self):
        """
        Returns the translation into ASP{f}
        """
        return '% -------------------------------------\n' +\
               '% Theory ' + self.name + '\n' +\
               '% -------------------------------------\n\n' +\
               GENERAL_AXIOMS

# =====================================================================

class Structure(object):
    """
    Objects of type Structure correspond to structures of the 
    language of ALM. The structure is a statement of the form:
            structure <name>
                <structure description>
    where:
            <name>    -- is a constant
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type Structure given the        
        structure name.
        """
        super(Structure, self).__init__()
        self.name = name

        
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return '% -------------------------------------\n' +\
               '% Structure ' + self.name + '\n' +\
               '% -------------------------------------\n\n'

# =====================================================================

class Module(object):
    """
    Objects of type Module correspond to system descriptions of the 
    language of ALM. Modules are declared as:
            module <name>
    where:
            <name>    -- is a constant
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type Module given the module name.       
        """
        super(Module, self).__init__()
        self.name = name
        

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return '% -------------------------------------\n' +\
               '% Module ' + self.name + '\n\n'
    
# =====================================================================

class SortDeclarations(object):
    """
    Objects of type SortDeclarations correspond to statements of the form:
            sort declarations
    """
    
    def __init__(self, something):
        """
        """    
        super(SortDeclarations, self).__init__()


    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return "\n% Sort Declarations\n\n"
		
# =====================================================================

class Instance(object):
    """
    Objects of type Instance correspond to instance definitions of the 
    language of ALM. Instance defintions are statements of the form:
            i1, ..., ik in c1, ..., cn
    where:
            i1, ..., ik   -- are instances
			c1, ..., cn   -- are sort names
            k >= 1 and n >= 1
    """
    
    def __init__(self, instances, sorts, attr_vals):
        """
        Creates a new object of the type Insatnce given the list of
        instance names and their sorts.
        """
        global crt_instances
        crt_instances = instances
        
        super(Instance, self).__init__()
        self.instances = instances
        self.sorts = sorts
	self.attr_vals = attr_vals

    def inst_name(self, inst):
        sx = inst[0]
        if len(inst[1]) > 0:
            sx = "".join([sx, "(", ", ".join(inst[1]), ")"])
        return sx

    def inst_with_no_vars(self, inst):
        s = ''
        sx = self.inst_name(inst)
           
        s = s + 'dom(' + sx + ').\n'

        global instances
        for y in self.sorts:
            s = s + 'is_a(' + sx + ', ' + y + ').\n\n'
                
            instances[y] = instances[y] | set([sx])
            for z in superclasses[y]:
                instances[z] = instances[z] | set([sx])

        return s


    def params_contain_var(self, inst):
        for x in inst[1]:
            if is_variable(x):
                return True
        return False

    def logic_program_attribute_vals(self, inst):
        s = ''
        str_inst = self.inst_name(inst)
        for attr_def in self.attr_vals:
            attr_name = attr_def[0]
            attr_params = list(attr_def[1])
            attr_params.insert(0, str_inst)

            attr_val = attr_def[2]
            s_aux = "".join([attr_name, "(", ", ".join(attr_params), ")"])
            
            dom = ''
            if self.params_contain_var(inst):
                dom = ' :- dom(' + attr_params[0] + ')'
                for i in range (1, len(attr_params)):
                    dom = dom + ', ' + "dom(" + attr_params(i) + ")"

            if attr_val == "true" :
                s = s + s_aux + dom + '.\n'
            elif attr_val == "false" :
                s = s + '-' + s_aux + dom + '.\n'
            else:
                s = s + s_aux + " #= " + attr_val + dom + '.\n'
        return s

    def subs_for_var(self, var):
        substitutions_for_var = set()
        str_inst = self.inst_name(self.instances[0])

        for attr_def in self.attr_vals:
            attr_name = attr_def[0]
            attr_params = list(attr_def[1])
            attr_params.insert(0, str_inst)
            attr_val = attr_def[2]
                    
            global functions
            attr_param_sorts = functions[attr_name][1]
            attr_return_sort = functions[attr_name][2]
                   
            for i in range(0, len(attr_params)):
                if attr_params[i] == var:
                    subx = substitutions_for_var | instances[attr_param_sorts[i]]

            if attr_val == var:
                substitutions_for_var = substitutions_for_var | instances[attr_return_sort]

        return substitutions_for_var 
        
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        s = ''
        if len(self.instances) > 1:
            for x in self.instances:
                s = s + self.inst_with_no_vars(x)
            if len(self.attr_vals) > 1:
                print 'Error: Attribute values cannot be specified for ' +\
			'multiple instances at a time.'
            return s

        inst = self.instances[0]
        str_inst = self.inst_name(inst)

        if not self.params_contain_var(inst):
            s = s + self.inst_with_no_vars(inst)
        else:
            vars = set()
            grounded_params = [inst[1]]
            for x in inst[1]:
                if is_variable(x):
                    vars = vars | set([x])

            for var in vars:
                substitutions_for_var = self.subs_for_var(var)              

                aux = []
                for g in grounded_params:                   
                    if var in g:
                        for val in substitutions_for_var:
                            gr = list(g);
                            for i in range(0, len(gr)):
                                if gr[i] == var:
                                    gr[i] = val
                            aux.append(gr)
                    else:
                        aux.append(g)
						
                grounded_params = list(aux)
				
            for g in grounded_params:
                crt_inst = [inst[0]]
                crt_inst.append(g)
                s = s + self.inst_with_no_vars(crt_inst)			
                              
        return s + self.logic_program_attribute_vals(inst)




# =====================================================================
# ALM LANGUAGE GRAMMAR
# =====================================================================

# =====================================
# BASIC TOKEN TYPES
# =====================================
 
CONSTANT  = Token('[a-z][_a-zA-Z0-9]*')
VARIABLE  = Token('[A-Z][_a-zA-Z0-9]*')

NUMBER    = Token(Integer())

COMMA     = Token(',') 
SUBSORT   = Token('::')
COLON     = Token(':')
TIMES     = Token('\*')
RARROW    = Token('\->')

LPAREN    = Token('\(')
RPAREN    = Token('\)')
EQ        = Token('=')
NEQ       = Token('!=')

ARITH_OP  = Or(
              Token('\+'),
              Token('\-'),
              Token('\*'),
              Token('/')
            )

COMP_OP   = Or(
              Token('>='),
              Token('<='),
              Token('>'),
              Token('<')
            )
            
# =====================================
# SORT DECLARATIONS
# =====================================

CT_LIST = CONSTANT & ZeroOrMore(~COMMA & CONSTANT) > list

ATTR_DOMAIN = Optional(CONSTANT & ZeroOrMore(~TIMES & CONSTANT) & ~RARROW) > list

ATTR_DECL = CT_LIST & ~COLON & ATTR_DOMAIN & CONSTANT > args(AttrDecl)

SORT_ATTRS = ~Token('attributes') & OneOrMore(ATTR_DECL)

SORT_DECL_HEAD = CT_LIST & ~SUBSORT & CT_LIST > args(SortDecl)

SORT_DECL = SORT_DECL_HEAD & Optional(SORT_ATTRS)

SORT_DECLARATIONS_HEADER = ~Token('sort declarations')

SORT_DECLARATIONS = SORT_DECLARATIONS_HEADER & OneOrMore(SORT_DECL)

# =====================================
# FUNCTION DECLARATIONS
# =====================================

TOTAL_PARTIAL = Optional(Token('total')) > set

FUNC_DOMAIN = CONSTANT & ZeroOrMore(~TIMES & CONSTANT) & ~RARROW > list

FUNC_DECL = TOTAL_PARTIAL & CONSTANT & ~COLON & FUNC_DOMAIN & CONSTANT > args(FunctionDecl)

FUNC_SECTION = OneOrMore(FUNC_DECL)

FUNC_SECTION_HEADER = Or(
        Token('basic'),
        Token('defined')
    ) > args(FunctionTypeResetter)

FUNC_BODY = OneOrMore(FUNC_SECTION_HEADER & FUNC_SECTION)

FUNC_HEADER = Or(
        Token('statics'),
        Token('fluents')
    ) > args(FunctionTypeResetter)
    
FUNCTION_DECLARATIONS_BODY = OneOrMore(FUNC_HEADER & FUNC_BODY)

FUNCTION_DECLARATIONS_HEADER = ~Token('function declarations')

FUNCTION_DECLARATIONS = FUNCTION_DECLARATIONS_HEADER & FUNCTION_DECLARATIONS_BODY

# =====================================
# CONSTANT DECLARATIONS
# =====================================

CONSTANT_DECL = CT_LIST & ~COLON & CT_LIST > args(ConstantDecl)
  
CONSTANT_BODY = OneOrMore(CONSTANT_DECL)

CONSTANTS_HEADER = ~Token('object constants')

CONSTANT_DECLARATIONS = CONSTANTS_HEADER & CONSTANT_BODY

# =====================================
# DYNAMIC_CAUSAL_LAW
# =====================================

CV = Or(CONSTANT, VARIABLE)

CVN = Or(CV, NUMBER)

EQ_NEQ_LIT = CVN & Or(EQ, NEQ, COMP_OP) & CVN > list


DCL_OCC = Token('occurs') & ~LPAREN & CV & ~RPAREN > list


LIT_NAME = Optional(Token('\-')) & CONSTANT > ''.join

PARAMS = Optional(~LPAREN & CVN & ZeroOrMore(~COMMA & CVN) & ~RPAREN) > list

BOOL_BASIC_LIT = LIT_NAME & PARAMS > list


NON_BOOL_BASIC_LIT = CONSTANT & PARAMS & Or(EQ, NEQ) & CVN > list

BASIC_LIT = Or(BOOL_BASIC_LIT, NON_BOOL_BASIC_LIT, EQ_NEQ_LIT)


ARITH_LIT = CVN & ARITH_OP & CVN & Or(EQ, NEQ) & CVN > list


DCL_LIT = Or(BASIC_LIT, ARITH_LIT)

DCL_BODY = Optional(~Token('if') & DCL_LIT & ZeroOrMore(~COMMA & DCL_LIT)) > list

DYNAMIC_CAUSAL_LAW = DCL_OCC & ~Token('causes') & BASIC_LIT & DCL_BODY &\
                     ~Token('\.') > args(DynamicCausalLaw)

# =====================================
# EXECUTABILITY_CONDITION
# =====================================

EC_OCC = Token('occurs') & ~LPAREN & CV & ~RPAREN > list

OCC_LIT = Or(Token('occurs'), Token('\-occurs')) & ~LPAREN & CV & ~RPAREN > list


EC_LIT = Or(BASIC_LIT, ARITH_LIT, OCC_LIT, EQ_NEQ_LIT)

EC_BODY = Optional(~Token('if') & EC_LIT & ZeroOrMore(~COMMA & EC_LIT)) > list

EXECUTABILITY_CONDITION = ~Token('impossible') & EC_OCC & EC_BODY & \
                          ~Token('\.')  > args(ExecutabilityCondition)

# =====================================
# STATE_CONSTRAINT
# =====================================

SC_LIT = Or(BASIC_LIT, ARITH_LIT, EQ_NEQ_LIT)

SC_BODY = Optional(~Token('if') & SC_LIT & ZeroOrMore(~COMMA & SC_LIT)) > list

STATE_CONSTRAINT = Or(BASIC_LIT, Token('false')) & SC_BODY & ~Token('\.') \
                   > args(StateConstraint)

# =====================================
# MODULE
# =====================================
	
AXIOM = Or(
			DYNAMIC_CAUSAL_LAW,
			STATE_CONSTRAINT,
			EXECUTABILITY_CONDITION
			)		

AXIOMS = ~Token('axioms') > args(Axioms)

MODULE_BODY = Optional(SORT_DECLARATIONS) & \
              Optional(FUNCTION_DECLARATIONS) & \
              Optional(CONSTANT_DECLARATIONS) & \
              Optional(AXIOMS & OneOrMore(AXIOM))

MODULE_HEADER = ~Token('module') & CONSTANT & \
                ~Optional(Token('depends on') & CT_LIST) > args(Module)

MODULE_SECTION = MODULE_HEADER & MODULE_BODY

# =====================================
# STRUCTURE
# =====================================

STRUCTURE_HEADER = ~Token('structure') & CONSTANT > args(Structure)

STATIC_VALS = ~Token('values of statics') & OneOrMore(STATE_CONSTRAINT)

ATTR_VALS = CONSTANT & PARAMS & ~Token('=') & CVN > list

#INST = CONSTANT & Optional(LPAREN & INST1 & \
#                           ZeroOrMore(COMMA & INST)) > ''.join

#INST1 = Or(VARIABLE, NUMBER, INST)

INSTANCE_TRAIL = Optional(~LPAREN & CVN & \
                               ZeroOrMore(~COMMA & CVN) & ~RPAREN) > list

INSTANCE = CONSTANT & INSTANCE_TRAIL > list

INSTANCE_LIST = INSTANCE & ZeroOrMore(~COMMA & INSTANCE) > list

INSTANCE_DEF_TRAIL = ZeroOrMore(ATTR_VALS) > list

INSTANCE_DEF = INSTANCE_LIST & ~Token('in') & CT_LIST & INSTANCE_DEF_TRAIL > args(Instance)

STRUCTURE_SECTION = STRUCTURE_HEADER & ~Token('instances') & \
                    OneOrMore(INSTANCE_DEF) & Optional(STATIC_VALS)


# =====================================
# SYSTEM DESCRIPTION
# =====================================

THEORY_HEADER = ~Token('theory') & CONSTANT > args(Theory)

THEORY_SECTION = THEORY_HEADER & OneOrMore(MODULE_SECTION)

SYSTEM_DESCRIPTION_HEADER = ~Token('system description') & CONSTANT \
                            > args(SystemDescription)

EOF = ~Eof()

SYSTEM_DESCRIPTION = SYSTEM_DESCRIPTION_HEADER & THEORY_SECTION & STRUCTURE_SECTION \
                     & ~EOF


# =====================================================================
# DRIVER AND UTILITY FUNCTIONS
# =====================================================================

# =====================================
# UTILITY FUNCTIONS
# =====================================

def rewrite_lp(f_lp, statement):
    """
    Given an object representation a statement of the language ALM,
    prints the logic program form of the statement to file f_lp
    """
    f_lp.write(statement.logic_program_form())

def flatten_list(l):
	result = []
	for x in l:
		if hasattr(x, '__iter__'):
			aux = flatten_list(x)
			result.extend(aux)
		else:
			result.append(x)
	return result
	
def is_variable(text):
    return text[0].isupper()

def is_constant(text):
    return text[0].islower()
	
def get_vars(l):
	result = []
	for x in flatten_list(l):
		if is_variable(x) :
			result.append(x)
	return list(set(result))

# =====================================
# PROGRAM DRIVER
# =====================================


def main():
    if len(sys.argv) != 2:
        print 'You need to write "ALMtoASP.py" and the name of the \
               input file'
    else:
        try:
            source = open(sys.argv[1], 'r')
  
            representation = SYSTEM_DESCRIPTION.parse_file(source)
            if representation != None:
                print 'The syntax analysis of the input file "' + \
                       sys.argv[1] + '" was successful'

                lp_output_file = sys.argv[1].rpartition('.')[0] + '.lp'
                f_lp = open(lp_output_file, 'w')
                list_lp = []

                for i in range (0,len(representation)):
                    list_lp.append(f_lp)
                map(rewrite_lp, list_lp, representation)
                f_lp.close()

            else:
                print 'The input file "' + sys.argv[1] + \
                          '" contains syntax errors!!!'

            print "\n",    
            source.close()
        except IOError:
            print "Unable to open the file: " + options.filename
   
if __name__ == "__main__":
    main()






