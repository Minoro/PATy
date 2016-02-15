#-*- coding:utf-8 -*-
from copy import copy

# clausulas =['P(f(a),x,y,z) or P(x,y,z,w)']
clausulas =['C(a)',
            '~F(y) or L(a,y)',
            '~C(x) or ~F(y) or ~G(y) or ~L(x,y)',
            '~F(x) or ~M(c,x) or ~C(y) or L(y,x)',
            'F(b)',
            'M(c,b)',
            'G(b)']


constantes = ['a', 'b', 'c', 'd', 'e', 'f', 'g']
variaveis = ['w','x', 'y', 'z']


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

def aglutinar(clausulas):
    fila = []
    for clasula in clausulas:
        for c in clasula:
            fila.append(c)
    return fila

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

def refutacao(cls):

    premissas = copy(cls)
    for premissa in cls:
        find = nega(premissa)
        if(find in premissas):
            premissas.remove(premissa)
            premissas.remove(find)

    print premissas
    if len(premissas) == 0:
        return True
    return False

def unificacao(clausulas):

    fila = copy(clausulas)
    for i,c in enumerate(fila):
        if c.startswith('~'):
            func = c[1]
        else:
            func = c[0]

        args = c[c.find(func)+2:c.rfind(')')]

        j = i+1
        while j < len(fila):
            if(func in fila[j]):
                args_func = fila[j][fila[j].find(func)+2:fila[j].rfind(')')]

                args.split(',')
                args_func.split(',')

                for x, y in zip(args, args_func):
                    if x == y:
                        continue

                    if x in constantes:
                        key = x
                        fetch = y
                    else:
                        key = y
                        fetch = x

                    for it, clasula in enumerate(fila):
                        fila[it] = fila[it].replace(key, fetch)

            j += 1

    return list(set(fila))





# c = ['~A(a)', 'F(x,y)']
# print refutacao(clausulas, c)

