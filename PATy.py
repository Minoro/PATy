#-*- coding:utf-8 -*-
from copy import copy

# clausulas =['A or B', '~A or C', '~B or C']
clausulas =['~A(x) or B(x,y)', '~B(x,y) or C(x)', '~C(x) or D(x,y)', '~D(x,y) or E(x) or F(x,y)']

operadores = ['or', 'and']

def to_cnf(clausulas):
    '''
    :param clausulas: 'Lista com as clausuas'
    :return: 'Faz a separação na operação AND'
    '''
    cnf = []
    temp = []
    for clausula in clausulas:
        conjunto = clausula.split('and')
        for c in conjunto:
            temp.append(c.strip()) #adiciona clausula sem espaço no começo ou fim

    for clausula in temp:
        conjunto = clausula.split('or')
        conj_or = []
        for c in conjunto:
            conj_or.append(c.strip()) #adiciona clausula sem espaço no começo ou fim
        cnf.append(conj_or)

    return cnf

def nega(clausula):

    if clausula.startswith('~'):
        c = clausula[clausula.rfind('~')+1:]
    else:
        c = '~'+clausula

    return c

def resolucao(cls):
    clausulas = copy(cls)
    max = len(clausulas)

    current = copy(clausulas[0])
    for i in range(1, max):
        clausula = copy(clausulas[i])

        for i, c in enumerate(current):
            #trata negação dupla
            while c.startswith('~~'):
                c = c[2:]
            current[i] = c

            find = nega(c)
            if find in clausula:
                current.remove(c)
                clausula.remove(find)

        current += clausula
        current = list(set(current))

    return current

def refutacao(clausulas, conclusao):
    p = copy(clausulas)
    for c in conclusao:
        p.append([nega(c)])

    print 'Provar = ', p
    res = resolucao(p)
    print res
    if len(res) == 0:
        return True
    return False

print clausulas
clausulas = to_cnf(clausulas)
print  clausulas
c = ['~A(x)', 'F(x,y)']
print refutacao(clausulas, c)