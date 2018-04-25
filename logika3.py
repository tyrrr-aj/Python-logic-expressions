# aim of the program is to convert given logic expression to the simplest possible form
    # program accepts:
    # - logical variables (with names of letters and numbers, starting with a letter)
    # - operators: 
    #   - ~ negation
    #   - & conjunction
    #   - | alternation
    #   - > implication
    #   - = equivalance
    #   - ^ exclusive disjunction
    # - logical constants 0 and 1
    # - spaces

def Quine_McCluskey(expression): # shortens the expression using the Quine - McCluskey's algorithm
    def vars(expression): # produces list of variables used in expression
        variables = set()
        result = set()
        for e in expression: # first we gather all symbols from expression (without repetitions)
            variables = variables.union(e)
        while variables: # and then we process all negated variables
            e = variables.pop()
            if e[0] == '~':
                result.add(e[1:])
            else:
                result.add(e)
        return list(result)
    
    def find_good_assignments(expression, variables): # finds assignments of values to variables for which whole expression returns true
        def binary_representation(number, length): # returns binary representation of a number with zeros added at begnning to get proper length (scheme for assignment)
            binary_repr = ''
            for i in range(length):
                binary_repr = str(number % 2) + binary_repr # adds next bit of number at the beginning of result
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
        for i in range(len(variables) + 1): # there can be from 0 to len(variables) ones in representation
            good_assignments.append([]) # we prepare empty lists for them
        for i in range(2**len(variables)): # iteration through all possible assignments of variables and 0/1 values (there are 2**(number of variables) possibilities)
            for pos, e in enumerate(variables): # updates values in assignments, creating next assignment
                assignments[e] = 2**pos & i != 0 # value of pos-th bit in i
            for e in expression:
                if evaluate(e, assignments): # for this assignment expression returns true
                    good_assignments[ones(i)].append([{i}, binary_representation(i, len(variables)), False]) # [numbers of representations, representation, was used?]
                    break
        return good_assignments
    
    def join_assignments(good_assignments): # joins all possible assignments
        from copy import deepcopy
        
        def ones_bin(representation): # returns number of one in given representation
            ones_count = 0
            for e in representation:
                if e == '1':
                    ones_count += 1
            return ones_count
        
        def joinable(rep1, rep2): # two lists are joinable if they differ only on one position
            first_diff = True # true if there were no differences so far
            for i in range(len(rep1)):
                if rep1[i] != rep2[i]:
                    if first_diff:
                        first_diff = False
                    else: # second difference was found
                        return False
            else: # no or one difference has been found
                return True
            
        def join(rep1, rep2): # joins two joinable representations, replacing diffrent bit by '-'
            for i in range(len(rep1)):
                if rep1[i] != rep2[i]:
                    return rep1[:i] + '-' + rep1[i+1:]
        
        store = [] # representations that won't be joined furthermore
        reps = set() # numbers that are represented by representations in store
        while (good_assignments): # while there are still any potentially joinable representatios
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
                    if not k[2] and k[:2] not in store: # 'used' boolean if false, and representation is not already in store
                        store.append(k[:2]) # it is stored as final form, the used boolean is no longer necessary so we get rid of it
                        reps = reps | k[0] # numbers included in representation k are thus included in store
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
    
def tautologies(expression): # removes conjunctions that can already be evaluated, returns 0 or 1 if evaluated everything
    for i, e in enumerate(expression): # we go through all the conjunctions
        vars = set(e) # and start with eliminating repeated variables
        if '0' in vars or '~1' in vars: # whole conjunction is then false
            expression[i] = 0 # so we replace it with 0
        else:
            if '1' in vars: # doesen't matter in conjunction
                vars.remove('1')
            if '~0' in vars: # doesen't matter in conjunction
                vars.remove('~0')
            if not vars: # set is empty, so it contained only constant trues
                return 1
            else:
                for el in vars: # now we check for alfa and ~alfa pairs (variable and it's negation, making conjunction always false)
                    if el[0] == '~' and el[1:] in vars: # negeted variable starts with '~', so el[1:] is actual name of the variable
                        expression[i] = 0
                        break;
                else:
                    expression[i] = vars # we were modifying vars, not element of expression, so we have to assign it now
    result = []
    for e in expression: # we rewrite expression, removing all 0s (that stand for already evaluated expressions)
        if e != 0:
            result.append(e)
    if not result: # if result is empty, expression must have consisted of false conjunctions only, so it is equivalent to 0
        return 0
    return result

def normal_form(expression): # turns expression into list of conjuctions (normal disjunctive form)
    from itertools import product
    
    if type(expression) == list and len(expression) == 2: # it's a single negated variable, so we can return it now - there's nothing to process
        return [[expression[0] + expression[1]]]
    
    if type(expression) == list and len(expression) == 3: # hence it's expression - conjuction or alternative
        operation = expression.pop(1) # we take the operator away from the expression, remembering it to know whether we're dealing with alternative or conjunction
        result = []
        for i, e in enumerate(expression): # first we process every subexpression and prepare variables by enclosing each of them in double list (e.g. 'a' -> [['a']])
            if type(e) == list:
                if len(e) == 3: # e is expression we have to process
                    result.append(normal_form(e))
                else: # e is negation of a variable, we connect ~ and variable in single string and wrap as normal variable (e.g. ['~', 'a'] -> [['~a']])
                    result.append([[e[0] + e[1]]])
            else: # e is variable, we wrap it with double list
                result.append([[e]])
        if operation == '|': # we simply have to add elements form lists of arguments, e.g. [ [['a'], ['b']], [['c']] ] -> [ ['a'], ['b'], ['c'] ]
            result = [e for f in result for e in f]
        else: # operation is &, we have to take the cartesian product of elements of both argument lists
            result = [e + f for e, f in product(result[0], result[1])]
        return result
    return expression

def deMorgan(expression): # eliminates negations of expressions (allowes only negations of single variables)
    def dbn(expression): # checks and (if neccesary) eliminates double negation from single expression (does not process subexpressions)
        if type(expression) == list and len(expression) == 2 and type(expression[1]) == list and len(expression[1]) == 2:
            return expression[1][1] # skip two levels with negations
        else:
            return expression
    
    if type(expression) == str: # if given expression consists of one string only, there's nothing to process, so we return it
            return expression
    if len(expression) == 2 and type(expression[1]) == list: # it's negation of an expression, so de Morgan is neccesary
        if expression[1][1] == '&': # we use de Morgan's law to change ~(p&q) into (~p)|(~q)
            result = [deMorgan(dbn(['~', expression[1][0]])), '|', deMorgan(dbn(['~', expression[1][2]]))] # also checks whether subexpressions don't need to be processed
        else: # expression[1][1] == '|', we use de Morgan's law to change ~(p|q) into (~p)&(~q)
            result = [deMorgan(dbn(['~', expression[1][0]])), '&', deMorgan(dbn(['~', expression[1][2]]))] # same here
    else: # de Morgan is not neccesary
        result = []
        for e in expression:
            result.append(deMorgan(e)) # we still have to check whether subexpressions don't need to be processed either
    return result

def double_negations(expression): # eliminates all double negations from expression and it's subexpressions
    if type(expression) == str: # it's single variable, there's no need to process it
        return expression
    if len(expression) == 2 and len(expression[1]) == 2: # double negation (current and next level), only brackets with negations have length of 2 (expressions have 3)
        return double_negations(expression[1][1]) # double-negated subexpression needs to be recursively checked too
    else:
        result = [] # expression will be rewritten here
        for e in expression: # if expression is not double negation, it may still contain subexpressions, which have to be checked recursively
            if type(e) == list:
                result.append(double_negations(e))
            else:
                result.append(e)
        return result

def change_operators(expression): # turns all other operators into alternatives, conjunctions and negations
    if len(expression) < 2: # if expression is single variable, it cannot be processed normally
        return expression
    
    # on second position of expression there's either operatator or subexpression / variable (in case of a negation bracket)
    if expression[1] == '=': # equivalances
        expression = [[expression[0], '>', expression[2]], '&', [expression[2], '>', expression[0]]]
    elif expression[1] == '>': # implications
        expression = [['~', expression[0]], '|', expression[2]]
    elif expression[1] == '^': # exclusive dijunctions
        expression = [[expression[0], '|', expression[2]], '&', ['~', [expression[0], '&', expression[2]]]]
    result = []
    for e in expression: # after changing operators on current level, we recursively go to subexpressions
        if type(e) == list: # e is subexpression
            result.append(change_operators(e))
        else:
            result.append(e) # e is just an operator / variable
    return result
    
def split_expression(expression):
    # splits expression into nested lists of operator and it's arguments
    # process is done in two steps - first string is turned into list of variables and operators
    # then it is turned into final nested lists form
    
    def final_split(expression): # recursive part - solving brackets, then operators
        operators = ['&|', '^', '>='] # operators are sorted by priority, with brackets and negation treated separatly
        bracket = []

        while len(expression): # first we recursively process brackets, rewriting expression to new list named bracket
            e = expression.pop(0) # each element of expression should only be processed by one instance of function, so we pop them from expression
            if e == '(': # brackets aren't added to new bracket string, so they disappear after that step
                bracket.append(final_split(expression)) # recursive call to process bracket that has just been opened, 
            elif e == ')':
                break # it's time to process just rewritten bracket, rest of the expression will be processed by lower instances
            else:
                bracket.append(e) # if element wasn't bracket, it's simply rewritten to be processed later on

        # now we deal with negations
        i = 0
        while i < len(bracket):
            if bracket[i] == '~':
                bracket[i] = [bracket[i], bracket.pop(i + 1)] # if negation was found, it's replaced by list of negation and the following element (one it applies to)
            i += 1

        for ops in operators: # rest of operators are processed by priority (and for equal priority it's left to right)
            i = 0
            while i < len(bracket):
                if len(bracket) != 3 and type(bracket[i]) == str and bracket[i] in ops: # if len of bracket drops down to 3, it is in desired form - 
                    # [subexpression, operator, subexpression]. Until this, for every operator of currently processed pair (from operators list)
                    # we take what stands before it (this part was already procesed, so it's single list with subexpression), operator and next element of bracket
                    # and make a new subexpression from them
                    bracket[i - 1] = [bracket[i - 1], bracket.pop(i), bracket.pop(i)]
                else:
                    i += 1 # if checked element wasn't operator, we simply go on
        
        if len(bracket) == 1: # while processing list may go nested unnecessarly (contain only another list with actual expression), with which we deal now
            bracket = [e for e in bracket[0]]
        
        return bracket # bracket is returned, and lower instance may add it to it's bracket list before going on
    
    # initial split, from string to list of variables and operators
    operators = ['(', ')', '~', '&', '|', '>', '=', '^']
    splitted = []
    last_operand_position = -1 # position of last char that doesn't belong to variable name, so if first variable starts at 0 it should initially be -1
    for i, e in enumerate(expression):
        if e in operators:
            if last_operand_position != i - 1: # if previous char was not another operator
                splitted.append(expression[last_operand_position + 1 : i]) # chars from last_operand_position + 1 to i make variable name (or constant 0 or 1)
            last_operand_position = i # we have found operator, so an update is needed
            splitted.append(expression[i : i + 1]) # operator has to be added to result expression too
    if last_operand_position != len(expression) - 1: # if expression ends with a variable, there was no operator after it triggering append, so we do it manually here
        splitted.append(expression[last_operand_position + 1 : len(expression)])
    
    splitted = final_split(splitted)
    
    return splitted

def remove_spaces(expression):
    return expression.replace(' ', '')

def check(expression): # checks if given expression is correct
    import string
    
    operators = ['&', '|', '>', '=', '^']
    chars = string.ascii_letters + '_'
    digits = string.digits
    constants = ['0', '1']
    prefix_operators = ['~']
    state = 1 # we will use simple final state machine with possible states:
    # 0 - expected are:
    #       char or digit (from a variable name, not starting it - digit is allowed), leading to state 0
    #       whitespace (after a variable name), leading to state 2
    #       operator, leading to state 1
    #       closing bracket, leading to state 2
    # 1 - initial one, also one that expression should end in; expected are:
    #       char (not digit - it's the beginning of variable name), leading to state 0
    #       logical constant (0 or 1), leading to state 2
    #       whitespace, leading to state 1
    #       prefix operator, leading to state 1
    #       opening bracket, leading to state 1
    # 2 - expected are:
    #       operator, leading to state 1
    #       whitespace, leading to state 2
    #       closing bracket, leading to state 2
    brackets = 0 # increased with every found opening bracket, decreased for every closing one
    for e in expression: # we iterate through every char of expression:
        if state == 0:
            if (e in chars) | (e in digits):
                state = 0
            elif e == ' ':
                state = 2
            elif e in operators:
                state = 1
            elif e == ')':
                brackets -= 1
                state = 2
                if brackets < 0: # at any time, there can't be more closing than opening brackets
                    return False
            else:
                return False # if char was none of the above, it shouldn't be there
        elif state == 1:
            if e in constants:
                state = 2
            elif (e == ' ') | (e in prefix_operators):
                pass # state = 1
            elif e == '(':
                brackets += 1 # state = 1
            elif e in chars:
                state = 0
            else:
                return False
        else: # state == 2
            if e in operators:
                state = 1
            elif e == ')':
                brackets -= 1
                if brackets < 0:
                    return False
            elif e == ' ':
                pass # state = 2
            else:
                return False
    if brackets == 0 and state != 1: # number of opening and closing brackets must be equal, and processing should stop at state 1
        return True
    return False
    
def main():
    expression = input()
    if check(expression): # first we check whether given expresion is correct, if so we process it linearly:
        expression = remove_spaces(expression)
        expression = split_expression(expression) # expression is converted to form of nested lists - on each level a list contains list with subexpression,
                                                  # operator and another list with subexpression, (or - for negation - only an operator and list with subexpression),
                                                  # up to a level when subexpression would be a single variable (or constant)
                                                  # e.g. p&~(q|r) is represented as ['p', '&', ['~', ['q', '|', 'r'] ] ]
        
        expression = change_operators(expression) # on this step equivalances, implications and exclusive dijunctions are replaced with equivalent expressions
                                                  # consisting only of conjuntions, alternations and negations (thus the whole expression consists only of them now)
        
        expression = double_negations(expression) # double negations are excluded from expression
        
        expression = deMorgan(expression) # negations of implications and alternations are removed using de Morgan's laws
                                          # after that negations may apply ony to single variables (or constants)

        expression = normal_form(expression) # turns the expression to disjunctive normal norm, using distibutive properties of conjuntion and alternative
                                             # after that step, expression is represented as a list of lists, each of them representing one conjuntion
                                             # e.g. '(p&q) | p | (q&~r)' would be [ ['p', 'q'], ['p'], ['q', '~r'] ]
                
        expression = tautologies(expression) # conjuntions that are always true or always false are removed from expression
                                             # if no conjuntions are left, epression is already evaluated, so it's valued 0 or 1 (for false or true respectively)
            
        if type(expression) == list: # if expression was evaluated by tautologies function, it only has to be printed
            expression = Quine_McCluskey(expression) # now expression is shortened using the Quine - McCluskey's algorithm
            if not expression: # if Quine - McCluskey algorithm has removed all conjuntions, expression is constantly true
                print(1)       # (if it was false, it would have been recognized earlier by tautologies function)
            else:
                print(expression)
        else:
            print(expression)
    else:
        print('Wrong expression')
    
if __name__ == '__main__':
    main()