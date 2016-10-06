import sys
import copy

factsdict={}
rulesdict={}
infintyCheckList=[]
class Facts:

    def __init__(self):
        self.cliteral=''
        self.cvalue=''
        self.cconstants=''
    def setLiteral(self, literalp):
        self.cliteral = literalp
    def setValue(self, valuep):
        self.cvalue = valuep
    def setConstants(self, constantsp):
        self.cconstants = constantsp
    def getLiteral(self):
        return self.cliteral
    def getValue(self):
        return self.cvalue
    def getConstants(self):
        return self.cconstants

class Predicate:

    def __init__(self):
        self.pliteral=''
        self.pvalue=''
        self.parguments=''
    def setPliteral(self, literalp):
        self.pliteral = literalp
    def setPvalue(self, valuep):
        self.pvalue = valuep
    def setParguments(self, constantsp):
        self.parguments = constantsp
    def getPliteral(self):
        return self.pliteral
    def getPvalue(self):
        return self.pvalue
    def getParguments(self):
        return self.parguments

class Rules:
    def __init__(self):
        self.id =''
        self.rhs = []
        self.lhs = []
    def setLhs(self, lhsp):
        self.lhs.append(lhsp)
    def getLhs(self):
        return self.lhs
    def setRhs(self, rhsp):
        self.rhs.append(rhsp)
    def getRhs(self):
        return self.rhs
    def setId(self, idp):
        self.id = idp
    def getId(self):
        return self.id


#----------------------------------------------------------------------------------------------------------------
def  storeIndividualFacts(clausep):

        literal = ''
        #value = 'false'
        f1 = Facts()
        iol = clausep.index('(')
        literal = clausep[0:iol]
        #value = 'true'
        argument=[]
        startIndex =clausep.index('(')+1
        endIndex = clausep.index(')')
        argument=clausep[startIndex:endIndex].split(', ')
        i=0
        constantsv=[]
        while (i < len(argument)):
            constantsv.append(argument[i].strip())
            i=i+1

        f1.setLiteral(literal)
        f1.setConstants(constantsv)
        #f1.setValue(value)
        if(factsdict.has_key(literal)):
            storefact=factsdict.get(literal)
            #print storefact[0].getConstants()
            storefact.append(f1)
            factsdict[literal]=storefact
        else:
            storefact=[]
            storefact.append(f1)
            factsdict[literal]=storefact


#----------------------------------------------------------------------------------------------------------------

def numberOfQueries(queryp):
    fquery = queryp.split(' && ')
    return fquery
#----------------------------------------------------------------------------------------------------------------

def isContainMoreThanOneFacts(clausep):
    ffacts=[]
    factsdict=[]
    if(' && ' in clausep):
        ffacts = clausep.split(' && ')
        sof = len(ffacts)
        i=0
        while(i < sof):
            f = ffacts[i].strip()
            factsdict = storeIndividualFacts(f)
            i=i+1
    else:
        storeIndividualFacts(clausep)

#----------------------------------------------------------------------------------------------------------------

def  storepredicate(clausep):
    r1 = Rules()
    lop = clausep.split(' => ')
    lhspredicate = lop[0].strip()
    rhspredicate = lop[1].strip()
    iol = rhspredicate.index('(')
    literal = rhspredicate[0:iol]
    #value = 'true'
    argument=[]
    startIndex =rhspredicate.index('(')+1
    endIndex = rhspredicate.index(')')
    argument=rhspredicate[startIndex:endIndex].split(', ')
    i=0
    constantsv=[]
    while (i < len(argument)):
        constantsv.append(argument[i].strip())
        i=i+1
    p1 = Predicate()
    p1.setPliteral(literal)
    p1.setParguments(constantsv)
    r1.setRhs(p1)
    r1.setId(idreps)
    nolhs = lhspredicate.split(' && ')
    i=0
    while(i < len(nolhs)):
        currentp = nolhs[i]
        iol = currentp.index('(')
        literal = currentp[0:iol]
        argument=[]
        startIndex =currentp.index('(')+1
        endIndex = currentp.index(')')
        argument=currentp[startIndex:endIndex].split(', ')
        j=0
        constantsv=[]
        while (j < len(argument)):
            constantsv.append(argument[j].strip())
            j=j+1
        p1 = Predicate()
        p1.setPliteral(literal)
        p1.setParguments(constantsv)
        r1.setLhs(p1)
        i = i+1
    keyofrulesdict = r1.getRhs()[0].getPliteral()
    #rulesdict
    if(rulesdict.has_key(keyofrulesdict)):
        storerules=rulesdict.get(keyofrulesdict)
        #print storefact[0].getConstants()
        storerules.append(r1)
        rulesdict[keyofrulesdict]=storerules
    else:
        storerules=[]
        storerules.append(r1)
        rulesdict[keyofrulesdict]=storerules

#----------------------------------------------------------------------------------------------------------------

def makeKB(clausep):
    #Storing Fact First
    if(' => ' in clausep ):
        storepredicate(clausep)
        return
    else:
        isContainMoreThanOneFacts(clausep)

#----------------------------------------------------------------------------------------------------------------
def getListOfArgument(query):
    startIndex =query.index('(')+1
    endIndex = query.index(')')
    argument=query[startIndex:endIndex].split(', ')
    return argument

#----------------------------------------------------------------------------------------------------------------
def convertToPredicate(currentquery):
    p1 = Predicate()
    iol = currentquery.index('(')
    literal = currentquery[0:iol]
    argument=[]
    startIndex =currentquery.index('(')+1
    endIndex = currentquery.index(')')
    argument=currentquery[startIndex:endIndex].split(', ')
    i=0
    constantsv=[]
    while (i < len(argument)):
        constantsv.append(argument[i].strip())
        i=i+1

    p1.setPliteral(literal)
    p1.setParguments(constantsv)
    return p1
#----------------------------------------------------------------------------------------------------------------

def getNameOfLiteral(query):
    iol = query.index('(')
    literal = query[0:iol]
    return literal
#----------------------------------------------------------------------------------------------------------------
# Return 1 if its varibale; return 0 if its constant
def checkVariableFromString(arguments):
    if(len(arguments) == 1 and arguments.islower()):
        return 1
    else:
        return 0

#----------------------------------------------------------------------------------------------------------------

def unificationWithRule(queryArguments, rightArguments,dictlocal,dictreturn):
    i=0
    if(len(queryArguments) == len(rightArguments)):
        while (i < len(queryArguments)):
            if(checkVariableFromString(queryArguments[i]) or checkVariableFromString(rightArguments[i])):
                if( checkVariableFromString(queryArguments[i]) == 1 and  checkVariableFromString(rightArguments[i]) == 0 ):
                     if(queryArguments[i] in dictreturn ):
                         if(dictreturn.get(queryArguments[i]) != rightArguments[i]):
                             return 0
                     else:
                        dictreturn[queryArguments[i]] = rightArguments[i]
                elif(checkVariableFromString(queryArguments[i]) == 0 and  checkVariableFromString(rightArguments[i]) == 1 ):
                     if(rightArguments[i] in dictlocal):
                         if(dictlocal.get(rightArguments[i]) != queryArguments[i]):
                             return 0
                     else:
                        dictlocal[rightArguments[i]] = queryArguments[i]
                elif(checkVariableFromString(queryArguments[i]) == 1 and  checkVariableFromString(rightArguments[i]) == 1):
                    if( queryArguments[i] in dictreturn and rightArguments[i] not in dictreturn ):
                        dictreturn[rightArguments[i]] = dictreturn.get(queryArguments[i])
                    elif(queryArguments[i] in dictreturn and rightArguments[i]  in dictreturn ):
                        if(dictreturn.get(queryArguments[i]) != dictreturn.get((rightArguments[i])) ):
                            return 0
                    elif(queryArguments[i] not in dictreturn and rightArguments[i] in dictreturn):
                        dictreturn[queryArguments[i]] = dictreturn.get(rightArguments[i])
                    else:
                        dictreturn[queryArguments[i]] = rightArguments[i]
            elif(queryArguments[i] != rightArguments[i]):
                return 0


            i=i+1



#----------------------------------------------------------------------------------------------------------------
def predicateClone(predicate):

    clonePredicate = Predicate()
    clonePredicate.setPliteral(predicate.getPliteral())
    clonePredicate.setPvalue(predicate.getPvalue())
    clonePredicate.setParguments(list(predicate.getParguments()))
    return (clonePredicate)
#----------------------------------------------------------------------------------------------------------------

def doUnificationWithleft(currentLeftPredicate, constantsToVerify):

    leftPredicate = predicateClone(currentLeftPredicate)

    argumentList = leftPredicate.getParguments()
    i=0
    while (i < len(argumentList)):
        if(argumentList[i] in constantsToVerify):
            argumentList[i] = constantsToVerify.get( argumentList[i] )
        i=i+1

    return leftPredicate

def unificationWithMap(queryArgument, factArgument, dictreturn):
    if(len(queryArgument) == len(factArgument)):
        i=0
        while( i < len(queryArgument) ):
            if(checkVariableFromString(queryArgument[i]) == 0 and  checkVariableFromString(factArgument[i]) == 0 ):
                if(queryArgument[i] != factArgument[i]):
                    return 0 #Both the arguments are constant and are different

            elif(checkVariableFromString(queryArgument[i]) == 1 and  checkVariableFromString(factArgument[i]) == 0):
                 dictreturn[queryArgument[i]] = factArgument[i]

            i=i+1
        return 1

def updateValueOfLists(dict,dictlocal,dictreturn):
        temp ={}
        for i in dictreturn:
            for j in dictlocal:
                if(dictreturn[i] == j):
                    temp[i] = dictlocal[j]
                    dict.update(temp)
                elif(i not in dict):
                    temp[i] = dictreturn[i]
                    dict.update(temp)



#----------------------------------------------------------------------------------------------------------------
def printFunction(action,predicate):

    literal = predicate.getPliteral()
    arguments=list(predicate.getParguments())

    i=0
    while (i < len(arguments)):

        if(checkVariableFromString(arguments[i])):
            arguments[i]= "_"
        i=i+1
    args=  ', '.join(arguments)
    content = action + ": " + literal + "(" + args + ")" +"\n"
    outputfile.write(content)


#----------------------------------------------------------------------------------------------------------------
def printLastStatus(status):
    outputfile.write(status)

#----------------------------------------------------------------------------------------------------------------
def unifyForPrint(p1, dict):


    args = p1.getParguments()
    i=0
    while (i< len(args)):
            if(args[i] in dict):
                args[i] = dict.get(args[i])
            i=i+1

    return p1

#----------------------------------------------------------------------------------------------------------------
def checkClause(p1,dict,infinityLoop):

    dictlocal={}
    dictreturn={}
    constantsToVerify ={}
    if(p1.getPliteral() in factsdict):
        getListOfFacts = factsdict.get(p1.getPliteral())
        t=0
        while (t < len(getListOfFacts)):
            currentFact = getListOfFacts[t]
            queryArgument = p1.getParguments()
            factArgument = currentFact.getConstants()
            factCheckedStatus = unificationWithMap(queryArgument, factArgument, dictreturn)
            if(factCheckedStatus == 0):
                if(t == (len(getListOfFacts)-1)):
                    printFunction("False", p1)
                    return 0
            else:
                dict.update(dictreturn)
                printPredicate=unifyForPrint(p1,dict)
                printFunction("True", printPredicate)

                return 1
            # Got Fact Checking Status
            t=t+1

    if(p1.getPliteral() in rulesdict):
        getAllMatchingRules = rulesdict.get(p1.getPliteral())
        t=0;
        while (t< len(getAllMatchingRules)):
                currentRule = getAllMatchingRules[t] # Individual Rule from the List
                if(currentRule.getId() in infinityLoop):
                    return False
                tempInfinityLoop = {}
                tempInfinityLoop[currentRule.getId()] = currentRule
                currentRhs= currentRule.getRhs() #Individual rhs from the current rule
                #rightPredicate = currentRhs[0].getPliteral()
                rightArgumentList = currentRhs[0].getParguments()
                unificationWithRule(p1.getParguments(), rightArgumentList,dictlocal,dictreturn)
                leftPredicatelist = currentRule.getLhs()

                i=0
                flag=True
                while(i< len(leftPredicatelist)):
                    currentLeftPredicate = leftPredicatelist[i]

                    p2=doUnificationWithleft(currentLeftPredicate, dictlocal)
                    printFunction("Ask", p2)
                    flag=flag and checkClause(p2,dictlocal,tempInfinityLoop)
                    if(not flag):
                        break
                    i=i+1
                if(flag):
                    updateValueOfLists(dict,dictlocal,dictreturn)
                    printPredicate = unifyForPrint(p1,dict)
                    printFunction("True", printPredicate)

                    return True

                else:
                    printFunction("Ask",p1)
                    dictlocal.clear()




                t=t+1

#Execution of The main Program
file =open("input.txt","r")
query = file.readline().strip()
#rquery stores total number of query that is passed from the programm
rquery = numberOfQueries(query)
nos = int(file.readline())
outputfile = open("output.txt", 'w')
sentence=[]
idreps=0
while(idreps<nos):
    clauses=file.readline().strip()
    makeKB(clauses)
    idreps = idreps +1

k=0
while (k<len(rquery)):
    localDict={}
    currentquery = rquery[k].strip()
    p1=convertToPredicate(currentquery)
    printFunction("Ask", p1)
    finalstatus = checkClause(p1,localDict,{})
    k=k+1


if(finalstatus == 1):
    printLastStatus("True")
else:
    printLastStatus("False")

