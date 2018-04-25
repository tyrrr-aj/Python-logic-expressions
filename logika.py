import string

def Quine_McCluskey(expression): # shortens the expression using the Quine - McCluskey's algorithm
    def vars(expression): # produces list of variables used in expression
        variables = set()
        result = set()
        for e in expression:
            variables = variables.union(e)
        while variables:
            e = variables.pop()
            if e[0] == '~':
                result.add(e[1:])
            else:
                result.add(e)
        return list(result)
    def find_good_assignments(expression, variables):
        def binary_representation(number, length): # returns binary representation of a number with zeros added at begnning to get proper length
            binary_repr = ''
            for i in range(length):
                binary_repr = str(number % 2) + binary_repr
                number = number >> 1
            return binary_repr
        def ones(num): # returns number of ones in num's binary representation
            ones_count = 0
            while num:
                ones_count += num%2
                num = num >> 1
            return ones_count
        def evaluate(conjunction, assignments): # evaluates single conjunction for values from assignments
            for e in conjunction:
                try:
                    if not assignments[e]: # variable is false (hence whole conjunction is false)
                        return False
                except: # KeyError - it's negation of variable
                    if assignments[e[1:]]: # negation of variable is true (hence whole conjucntion is false)
                        return False
            return True # there are only trues in conjunction
    
        assignments = {} # dict with variables and assigned values
        good_assignments = [] # list of lists of assignments for which expression returns True (it's number and binary representation), indexed by number of ones
        for i in range(len(variables) + 1):
            good_assignments.append([])
        for i in range(2**len(variables)): # iteration through all possible assignments of variables and 0/1 values (there are 2**(number of variables) possibilities)
            for pos, e in enumerate(variables): # updates values in assignments, creating next assignment
                assignments[e] = 2**pos & i != 0 # value of pos-th bit in i
            for e in expression:
                if evaluate(e, assignments):
                    good_assignments[ones(i)].append([{i}, binary_representation(i, len(variables)), False]) # [numbers of representations, representation, was used?]
                    break
        return good_assignments
    def join_assignments(good_assignments):
        from copy import deepcopy
        def ones_bin(representation): # returns number of one in given representation
            ones_count = 0
            for e in representation:
                if e == '1':
                    ones_count += 1
            return ones_count
        def joinable(rep1, rep2): # two lists are joinable if they differ only on one position
            first_diff = True
            for i in range(len(rep1)):
                if rep1[i] != rep2[i]:
                    if first_diff:
                        first_diff = False
                    else:
                        return False
            else:
                return True
        def join(rep1, rep2): # joins two joinable representations, replacing diffrent bit by '-'
            for i in range(len(rep1)):
                if rep1[i] != rep2[i]:
                    return rep1[:i] + '-' + rep1[i+1:]
        
        store = [] # representations that won't be joined furthermore
        reps = set() # numbers that are represented
        while (good_assignments):
            better_assignments = [] # newly joined representations
            for i in range(len(good_assignments) - 1): # one position is lost in each iteration, so possible number of ones in representation lowers
                better_assignments.append([])
            for i in range(len(good_assignments) - 1): # for each group of representations (except for the last one, since it has no following group)
                for k in good_assignments[i]: # for each representation of that group
                    for m in good_assignments[i + 1]: # we compare it with each representation in the next group
                        if joinable(k[1], m[1]): # representations can be joined into one better representation
                            joined_repr = join(k[1], m[1])
                            better_assignments[ones_bin(joined_repr)].append([k[0] | m[0], joined_repr, False]) # we store them temporarly in another list
                            k[2] = True # it was used, meaning it won't be rewritten to rest list
                            m[2] = True # it was used too
                    if not k[2] and k[:2] not in store: # 'used' boolean
                        store.append(k[:2])
                        reps = reps | k[0]
            else: # last group hasn't been checked for used/unused representations
                for k in good_assignments[len(good_assignments) - 1]:
                    if not k[2] and k[:2] not in store: # representation wasn't used
                        store.append(k[:2]) # it is stored as final form, the used boolean is no longer necessary so we get rid of it
                        reps = reps | k[0]
            good_assignments = deepcopy(better_assignments) # we abandon already processed representations and move on to joining more complex ones
        return (reps, store)
    def choose_conjunctions(reps, store):
        result = []
        mod_size = 1 # number of unused elements of reps that must be connected to representation to add it to result (all with one must be included, if there are no - we try with two etc.)
        while reps: # while not all representations were included
            for e in reps: # we iterate through reps
                appearings = 0
                for i, k in enumerate(store):
                    if e in k[0]: # seeking representations that must be included (connected to minimal number of numbers)
                        appearings += 1 # we count appearances
                        chosen_appearance = i # we need to store any appearance with number e so that we may later find the one with most connections
                if appearings == mod_size: # if their number was minimal so far, thath's the number we are looking for
                    for i, k in enumerate(store): # we must find representation connected to our variable with most other connections
                        if e in k[0] and len(k[0]) > len(store[chosen_appearance][0]):
                            chosen_appearance = i
                    result.append(store[chosen_appearance][1])
                    to_remove = store[chosen_appearance][0] # all numbers connected with this representation are included, so we may delete them from remaining representations
                    for k in store:
                        k[0] = k[0].difference(to_remove) # we remove all aperances of numbers we have already included in result
                    reps = reps.difference(to_remove) # those numbers have already been included in result
                    break
            else:
                mod_size += 1 # all numbers have more than mod_size appearances
        return result 
    def output_format(expression, variables): # turns result list into nice string
        def con_to_string(con, variables): # returns given conjunction as string with variables' names
            result = ''
            for i in range(len(con)):
                if con[i] == '1':
                    result += variables[i] + ' & '
                elif con[i] == '0':
                    result += '~' + variables[i] + ' & '
            return result[:len(result) - 3]
        
        variables.reverse()
        if len(expression) == 1: # there's only one conjunction, no brackets needed
            return con_to_string(expression[0], variables)
        else:
            final_form = ''
            for e in expression:
                final_form += '(' + con_to_string(e, variables) + ') | '
            return final_form[:len(final_form) - 3]
    
    variables = vars(expression)
    good_assignments = find_good_assignments(expression, variables)
    reps, store = join_assignments(good_assignments)
    result = choose_conjunctions(reps, store)
    return output_format(result, variables)
    
def tautologies(expression): # removes conjunctions that can already be evaluated, returns boolean result if evaluated everything
    contain_trues = False # flag used to state whether empty expression (such that contained only constants or tautologies) was true or false
    for i, e in enumerate(expression): # we go through all the conjunctions
        vars = set(e) # eliminates repeated variables
        if '0' in vars or '~1' in vars: # conjunction is then false
            expression[i] = 0
        else:
            if '1' in vars: # doesen't matter in conjunction
                vars.remove('1')
            if '~0' in vars: # doesen't matter in conjunction
                vars.remove('~0')
            if not vars: # set is empty, so it contained only constant trues
                return 1
            else:
                for el in vars: # now we check for alfa and ~alfa pairs
                    if el[0] == '~' and el[1:] in vars:
                        expression[i] = 0
                        break;
                else:
                    expression[i] = vars # we were modifying vars, not expression, so we have to assign it now
    result = []
    for e in expression: # we rewrite expression, removing all 0s (that stand for already evaluated expressions)
        if e != 0:
            result.append(e)
    if not result: # if result is empty, expression can already be evaluated - its equal to single logic constant 0 or 1
        return 0
    return result

def normal_form(expression): # turns expresion into list of conjuctions (normal alternative form)
    from itertools import product
    if type(expression) == list and len(expression) == 2: # to be done better somewhere else!!! (used only for initial expressions of one negated variable
        return [[expression[0] + expression[1]]]
    
    if type(expression) == list and len(expression) == 3: # hence it's conjuction or alternative
        operation = expression.pop(1) # we take the operator away from the expression, simultanously checking whether we're dealing with alternative or conjunction
        result = []
        for i, e in enumerate(expression): # first we process every subexpression and prepare variables by enclosing each of them in double list (e.g. 'a' -> [['a']])
            if type(e) == list:
                if len(e) == 3: # e is expression we have to process
                    result.append(normal_form(e))
                else: # e is negation of a variable, we connect ~ and variable in single string and wrap as normal variable (e.g. ['~', 'a'] -> [['~a']])
                    result.append([[e[0] + e[1]]])
            else: # e is variable, we wrap it with double list
                result.append([[e]])
        if operation == '|': # we simply have to add elements form lists of arguments, e.g. [[['a']], [[b]]] -> [['a'], ['b]]
            result = [e for f in result for e in f]
        else: # operation is &, we have to take the cartesian product of elements of both argument lists
            result = [e + f for e, f in product(result[0], result[1])]
        return result
    return expression

def deMorgan(expression): # eliminates negations of expressions (allowes only negations of single variables)
    def dbn(expression): # checks and (if neccesary) eliminates double negation from expression (does not process subexpressions)
        if type(expression) == list and len(expression) == 2 and type(expression[1]) == list and len(expression[1]) == 2:
            return expression[1][1]
        else:
            return expression
    
    if type(expression) == str: # if given expression consists of one string only, there's nothing to process, so we return it
            return expression
    if len(expression) == 2 and type(expression[1]) == list: # de Morgan is neccesary
        if expression[1][1] == '&': # we use de Morgan's law to change ~(p&q) into (~p)|(~q)
            result = [deMorgan(dbn(['~', expression[1][0]])), '|', deMorgan(dbn(['~', expression[1][2]]))] # also checks whether subexpressions don't need to be processed
        else: # expression[1][1] == '|', we use de Morgan's law to change ~(p|q) into (~p)&(~q)
            result = [deMorgan(dbn(['~', expression[1][0]])), '&', deMorgan(dbn(['~', expression[1][2]]))]
    else: # de Morgan is not neccesary
        result = []
        for e in expression:
            result.append(deMorgan(e)) # we still have to check whether subexpressions don't need to be processed either
    return result

def double_negations(expression): # eliminates all double negations from expression and it's subexpressions
    if type(expression) == str:
        return expression
    if len(expression) == 2 and len(expression[1]) == 2: # double negation (current and next level)
        return double_negations(expression[1][1])
    else:
        result = []
        for e in expression:
            if type(e) == list:
                result.append(double_negations(e))
            else:
                result.append(e)
        return result

def change_operators(expression): # turns all other operators into alternatives, conjunctions and negations
    if len(expression) < 2: # simple given examples, won't be called recursively
        return expression
     # on second position there's either operatator or var (in case of a negation bracket)
    if expression[1] == '=': # equalities
        expression = [[expression[0], '>', expression[2]], '&', [expression[2], '>', expression[0]]]
    elif expression[1] == '>': # implications
        expression = [['~', expression[0]], '|', expression[2]]
    elif expression[1] == '^': # xors
        expression = [[expression[0], '|', expression[2]], '&', ['~', [expression[0], '&', expression[2]]]]
    result = []
    for e in expression:
        if type(e) == list:
            result.append(change_operators(e))
        else:
            result.append(e)
    return result
    
def split_expression(expression): # splits expression into nested lists of operator and it's arguments
    def final_split(expression): # recursive part - solving brackets, then operators
        operands = ['&|', '^', '>=']
        bracket = []

        while len(expression): # brackets
            e = expression.pop(0)
            if e == '(':
                bracket.append(final_split(expression))
            elif e == ')':
                break
            else:
                bracket.append(e)

        i = 0 # negations
        while i < len(bracket):
            if bracket[i] == '~':
                bracket[i] = [bracket[i], bracket.pop(i + 1)]
            i += 1

        for ops in operands: # rest of operators, by priority
            i = 0
            while i < len(bracket):
                if len(bracket) != 3 and type(bracket[i]) == str and bracket[i] in ops:
                    bracket[i - 1] = [bracket[i - 1], bracket.pop(i), bracket.pop(i)] # previous var, operator, next var
                else:
                    i += 1
        
        if len(bracket) == 1:
            bracket = [e for e in bracket[0]]
        
        return bracket
    
    operands = ['(', ')', '~', '&', '|', '>', '=', '^'] # initial split, from string to list of variables and operators
    splitted = []
    last_operand_position = -1
    for i, e in enumerate(expression):
        if e in operands:
            if last_operand_position != i - 1:
                splitted.append(expression[last_operand_position + 1 : i])
            last_operand_position = i
            splitted.append(expression[i : i + 1])
    if last_operand_position != len(expression) - 1:
        splitted.append(expression[last_operand_position + 1 : len(expression)])
    
    splitted = final_split(splitted)
    
    return splitted

def remove_spaces(expression):
    return expression.replace(' ', '')

def check(expression): # checks if given expression is correct
    operands = ['&', '|', '>', '=', '^']
    chars = string.ascii_letters + '_'
    digits = string.digits
    constants = ['0', '1']
    prefix_operands = ['~']
    state = 1 # 0 - ostatnio znak w nazwie zmiennej, oczekiwany dowolny znak (ciag dalszy nazwy zmiennej),
              #     spacja (koniec nazwy zmiennej), operator, nawias zamykajacy
              # 1 - ostatnio operator, nawias otwierajacy, spacja (ze stanu 1), poczatek wyrazenia,
              #     oczekiwany znak (poczatek nazwy zmiennej - nie cyfra), spacja, nawias otwierajacy, stala, operator jednoargumentowy
              # 2 - ostatnio spacja (ze stanu 0 lub 2), nawias zamykajacy,
              #     oczekiwany operator, spacja, nawias zamykajacy
    brackets = 0
    for e in expression:
        if state == 0:
            if (e in chars) | (e in digits):
                state = 0
            elif e == ' ':
                state = 2
            elif e in operands:
                state = 1
            elif e == ')':
                brackets -= 1
                if brackets < 0:
                    return False
            else:
                return False
        elif state == 1:
            if e in constants:
                state = 2
            elif (e == ' ') | (e in prefix_operands):
                pass # state = 1
            elif e == '(':
                brackets += 1 # state = 1
            elif e in chars:
                state = 0
            else:
                return False
        else: # state == 2
            if e in operands:
                state = 1
            elif e == ')':
                brackets -= 1
                if brackets < 0:
                    return False
            elif e == ' ':
                pass # state = 2
            else:
                return False
    if (brackets == 0) & (state != 1):
        return True
    return False
    
def main():
    # expression - string, expr - list
    expression = input()
    if check(expression): # expresion is correct, so we process it linearly:
        expression = remove_spaces(expression)
        expression = split_expression(expression)
        expression = change_operators(expression)
        expression = double_negations(expression)
        expression = deMorgan(expression)
        expression = normal_form(expression)
        expression = tautologies(expression)
        if type(expression) == list: # expression may have been already evaluated after tautologies step, therefore we would not need to process it further
            expression = Quine_McCluskey(expression)
            if not expression: # Quine - McCluskey algorithm has evaporated all conjuntions, hence the expression is constantly true (if it was false, it would have been recognized earlier)
                print(1)
            else:
                print(expression)
        else:
            print(expression)
    else:
        print('Wrong expression')
    
if __name__ == '__main__':
    main()