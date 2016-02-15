#-*- coding:utf-8 -*-
from copy import copy

# clausulas =['P(f(a),x,y,z) or P(x,y,z,w)']
# expressao =['C(a)',
#             '~F(y) or L(a,y)',
#             '~C(x) or ~F(y) or ~G(y) or ~L(x,y)',
#             '~F(x) or ~M(c,x) or ~C(y) or L(y,x)',
#             'F(b)',
#             'M(c,b)',
#             'G(b)']

# expressao = ['~P(x) or Q(x,b)', 'P(a) or Q(a,b)']

# expressao = '(exists(u) forall(w) forall(x) exists(y) forall(z))(P(x) or Q(w,y,z) or R(u))'
# expressao = '(forall(x) forall(y) exists(u) forall(z) exists(w))(P(u,x) and P(z,y) and R(w))'

#Do Coppin
expressao = ['(exists(x) forall(y))(C(x) and ~F(y) or L(x,y))',
                '(forall(x) forall(y))(~C(x) or ~F(y) or ~G(y) or ~L(x,y))',
                '(forall(x) forall(y))(~F(x) or ~M(c,x) or ~C(y) or ~L(y,x))',
                '(exists(x))(F(x) and M(c,x) and G(x))']

#EXERCICIO DO SLIDE
# expressao = ['(forall(x))(~C(x) or W(x) and ~C(x) or R(x))',
#                 '(forall(x))(C(x) and ~W(x))',
#                 '(exists(x))(C(x) and O(x))',
#                 '(forall(x))(~O(x) or ~R(x))']

# CORES DO GRAFO
# expressao = ['()(A(x) or B(x))',
#              '()(C(x) or D(x))',
#              '()(~A(x) or ~B(x))',
#              '()(~C(x) or ~D(x))',
#              '()(~A(x) or ~C(x))',
#              '()(B(x) and D(x))']

constantes = ['a', 'b', 'c', 'd', 'e']
funcoes = ['f', 'g', 'h', 'i']
variaveis = ['u','w','x', 'y', 'z']


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

        j = i+1
        while j < len(fila):
            if(func in fila[j]):
                args = c[c.find(func)+2:c.rfind(')')]
                args_func = fila[j][fila[j].find(func)+2:fila[j].rfind(')')]

                args_f = args.split(',')
                args_func = args_func.split(',')

                for x, y in zip(args_f, args_func):
                    if x == y:
                        continue

                    replace_const = False
                    for const in constantes:
                        if const in x:
                            replace_const = True
                            break
                    if replace_const:
                        fetch = x
                        key = y
                    else:
                        fetch = y
                        key = x

                    for it, clasula in enumerate(fila):
                        fila[it] = fila[it].replace(key, fetch)

                    c = c.replace(key, fetch)
                    j = i
                    break

            j += 1

    return list(set(fila))

def skolemizacao(expressao):
    index = split_quantificadores(expressao)
    quantificadores = expressao[:index]
    premissa = expressao[index:]

    if quantificadores.startswith('('):
        quantificadores = quantificadores[1:-1]

    quantificadores = quantificadores.split(' ')

    fila_forall = []
    fila = {}
    for q in quantificadores:
        var = q[q.find('(')+1 : q.find(')')]

        if 'forall' in q:
            fila_forall.append(var)
        elif 'exists' in q:
            fila[var] = copy(fila_forall)

    i = 0 #indice para funções
    j = 0 #indice para constantes
    for key in fila:
        qnt = fila[key]
        if(len(qnt) > 0):
            func = funcoes[i]+'('
            for f in qnt:
                func += f
                if(f != qnt[-1]):
                    func += ','
            func += ')'
            i += 1
        else:
            while(constantes[j] in premissa): j +=1
            func = constantes[j]

            j += 1
        premissa = premissa.replace(key, func)
    return [premissa[1:-1]]



def split_quantificadores(expressao):
    count = 0
    index = 0
    for letra in expressao:
        if letra == '(':
            count += 1
        elif letra == ')':
            count -= 1
        index += 1
        if count == 0:
            return index
    return -1

# print clausulas
# clausulas = to_cnf(clausulas)
# print clausulas
# clausulas = aglutinar(clausulas)
# print clausulas
#
# print unificacao(clausulas)


print expressao
exp = []
for e in expressao:
    exp += skolemizacao(e)

print exp
exp = to_cnf(exp)

print 'Cláusulas: '
for e in exp:
    print e
print '-'*80
exp = unificacao(aglutinar(exp))
print exp

# print exp
print refutacao(exp)

