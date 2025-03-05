
MAX_CONSTANTS = 10

# Parse a formula, consult parseOutputs for return values.
# 1. an atom
# 2. a negation of a first order logic formula
# 3. a universally quantified formula
# 4. an existentially quantified formula
# 5. a binary connective first order formula
# 6. a proposition
# 7. a negation of a propositional formula
# 8. a binary connective propositional formula
def parse(fmla):
    length = len(fmla)
    if length == 1:
        if checkProp(fmla):
            return 6 # a proposition
    if length == 6:
        if checkPred(fmla):
            return 1 # an atom
    if fmla[0] == '~' and length > 1:
        if parse(fmla[1:length]) in range(1,6):
            return 2 # a negation of a first order logic formula
        elif parse(fmla[1:length]) in range(6,9):
            return 7 # a negation of a propositional formula
    if fmla[0] == 'A' and checkVar(fmla[1]):
        if parse(fmla[2:length])!=0:
            return 3 # a universally quantified formula
    if fmla[0] == 'E' and checkVar(fmla[1]):
        if parse(fmla[2:length])!= 0:
            return 4 # an existentially quantified formula
    if fmla[0] == '(' and fmla[length-1] == ')' and length >= 6:
        return checkBin(fmla)   
    return 0 # not a formula

def checkBin(fmla):
    connective = con(fmla)
    if connective == 0:
        return False
    left = lhs(fmla)
    right = rhs(fmla)
    if parse(left) in range(1,6) and parse(right) != 0:
        return 5 # a binary connective first order formula
    elif parse(left) != 0 and parse(right) in range(1,6):
        return 5 # a binary connective first order formula
    elif parse(left) in range(6,9) and parse(right) in range(6,9):
        return 8 # a binary connective propositional formula
    else:
        return 0

def checkVar(char):
    return char in 'xyzw' or char in 'abcdefghij'

def checkPred(fmla):
    if fmla[0] in 'PQRS':
        if fmla[3] == ',' and fmla[1] == '(' and fmla[5] == ')':
            if (checkVar(fmla[2]) and checkVar(fmla[4])):
                return True
    return False


def checkProp(fmla):
    return fmla in 'pqrs'

# Return the LHS of a binary connective formula
def lhs(fmla):
    connective = con(fmla)
    loc = locConn(fmla,connective)
    return fmla[1:loc]

def locConn(fmla,connective):
    count = 1
    bracCount = 0
    connective = connective[0]
    for c in fmla[1:len(fmla)-1]:
        if c == '(':
            bracCount = bracCount + 1
        if c == ')':
            bracCount = bracCount - 1
        if c == connective and bracCount == 0:
            return count
        count = count + 1
    

# Return the connective symbol of a binary connective formula
def con(fmla):
    connective = ''
    bracCount = 0
    fst = False
    for c in fmla[1:]:
        if c == '(':
            bracCount = bracCount + 1
        if c == ')':
            bracCount = bracCount - 1
        if fst:
            if (c in '/\\>') and bracCount == 0:
                connective += c
                if connective == '=>' or connective == '/\\' or connective == '\\/':
                    return connective
            else:
                return 0 
        if (c in '/\\=') and bracCount == 0:
            connective = c
            fst = True
                      
    return 0

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    connective = con(fmla)
    loc = locConn(fmla,connective)
    return fmla[loc+2:len(fmla)-1]


# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    return [fmla]

#check for satisfiability
# 0 : not satisfiable
# 1 : satisfiable
# 2 : number of constants exceeds MAX_CONSTANTS(10)
def sat(tableau):
    new_consts = 0
    gam_dict = {}
    while tableau:
        th = tableau.pop(0)
        if copl(th) and not closed(th):
            return 1
        fmla = None
        for f in th:
            if not literal(f):
                fmla = f
                break

        if isAlpha(fmla):
            th.remove(fmla)
            th.extend(applyAlpha(fmla))
            if not closed(th) and th not in tableau:
                tableau.append(th)

        if isBeta(fmla):
            th1 = th.copy()
            th2 = th.copy()
            th1.remove(fmla)
            th2.remove(fmla)
            toAdd = applyBeta(fmla)
            th1.append(toAdd[0])
            th2.append(toAdd[1])
            if not closed(th1) and th1 not in tableau:
                tableau.append(th1)
            if not closed(th2) and th2 not in tableau:
                tableau.append(th2)
                
        if isGamma(fmla):
            if leaveGa(th, fmla):
                th.remove(fmla)
                th.append(fmla)
            else:
                if fmla not in gam_dict:
                    gam_dict[fmla] = 0
                if gam_dict[fmla] == new_consts:
                    th.remove(fmla)
                else:
                    th.append(applyGamma(fmla, gam_dict[fmla]))
                    gam_dict[fmla] += 1
            if not closed(th) and th not in tableau:
                tableau.append(th)

        if isDelta(fmla):
            if new_consts == MAX_CONSTANTS:
                return 2
            else:
                th.remove(fmla)
                th.append(applyDelta(fmla, new_consts))
                if not closed(th) and th not in tableau:
                    tableau.append(th)
                new_consts += 1
                
    return 0


def copl(th):
    canexpt = {3, 4, 5, 8}
    for f in th:
        ft = parse(f)
        if (ft == 2 and len(f) != 7) or (ft == 7 and len(f) != 2) or ft in canexpt:
            return False
    return True

def leaveGa(th,fmla):
    th0 = th.copy()
    th0.remove(fmla)
    for f in th0:
        if parse(f) == 2 and parse(f[1:len(f)]) == 3:
            return True
        elif parse(f) == 7 and not(len(f)==2):
            return True
        elif parse(f) == 4 or parse(f) == 5 or parse(f) == 8:
            return True
    return False

def isAlpha(fmla):
    if fmla[0] == '~' and fmla[1] == '~':
        return 1
    elif fmla[0] == '~' and (parse(fmla[1:len(fmla)])== 5 or parse(fmla[1:len(fmla)])== 8):
        if con(fmla[1:len(fmla)]) == '\\/':
            return 2
        if con(fmla[1:len(fmla)]) == '=>':
            return 4
    elif (parse(fmla) == 5 or parse(fmla) == 8) and con(fmla) == '/\\':
        return 3
    else:
        return 0

def applyAlpha(fmla):
    if isAlpha(fmla) == 1:
        return [fmla[2:len(fmla)]]
    elif isAlpha(fmla) == 2:
        return ["~" + lhs(fmla[1:len(fmla)]), "~" + rhs(fmla[1:len(fmla)])]
    elif isAlpha(fmla) == 4:
        return[lhs(fmla[1:len(fmla)]),"~" + rhs(fmla[1:len(fmla)]) ]
    else:
        return [lhs(fmla),rhs(fmla)]
    
def isBeta(fmla):
    if fmla[0] == '~' and (parse(fmla[1:len(fmla)])== 5 or parse(fmla[1:len(fmla)])== 8):
        if con(fmla[1:len(fmla)]) == '/\\':
            return 1 
    elif parse(fmla)== 5 or parse(fmla)== 8:
        if con(fmla) == '=>':
            return 2
        if con(fmla) == '\\/':
            return 3
    else:
        return 0

def applyBeta(fmla):
    if isBeta(fmla) == 1:
        return["~" + lhs(fmla[1:len(fmla)]), "~" + rhs(fmla[1:len(fmla)])]
    elif isBeta(fmla) == 2:
        return["~" + lhs(fmla), rhs(fmla)]
    else:
        return[lhs(fmla), rhs(fmla)]
    
def isGamma(fmla):
    if parse(fmla) == 3:
        return 1
    elif parse(fmla) == 2 and parse(fmla[1:len(fmla)]) == 4:
        return 2
    else:
        return 0

def applyGamma(fmla,cnn):
    constants = ['a','b','c','d','e','f','g','h','i','j']
    const = constants[cnn]
    if parse(fmla) == 3:
        var = fmla[1]
        return fmla[2:len(fmla)].replace(var,const)
    else: # ~Ex
        var = fmla[2]
        return ("~" + fmla[3:len(fmla)].replace(var,const))

def isDelta(fmla):
    if parse(fmla) == 4:
        return 1
    elif parse(fmla) == 2 and parse(fmla[1:len(fmla)]) == 3:
        return 2
    else:
        return 0

def applyDelta(fmla,cnn):
    constants = ['a','b','c','d','e','f','g','h','i','j']
    const = constants[cnn]
    if parse(fmla) == 4:
        var = fmla[1]
        return (fmla[2:len(fmla)].replace(var,const))
    else: # ~Ax
        var = fmla[2]
        return ("~" + fmla[3:len(fmla)].replace(var,const))

def closed(th):
    for i in th:
        for j in th:
            if i == "~" + j:
                return True
    return False

def literal(fmla):
    if parse(fmla) == 1 or parse(fmla) == 6:
        return True
    elif fmla[0] == '~':
        return parse(fmla[1:]) == 1 or parse(fmla[1:]) == 6
    return False

#------------------------------------------------------------------------------------------------------------------------------:
#                   DO NOT MODIFY THE CODE BELOW. MODIFICATION OF THE CODE BELOW WILL RESULT IN A MARK OF 0!                   :
#------------------------------------------------------------------------------------------------------------------------------:

f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
