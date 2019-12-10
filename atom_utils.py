import copy
import re

### Reprezentare - construcție
FACT = "FACT"
RULE = "RULE"
INTEROGATION = "?"
CONST = "CONST"
VAR = "VAR"
ATOM = "ATOM"
FUNC = "FUNC"
NEG = "~"
AND = "A"
OR = "V"

FACTS = "facts"
RULES = "rules"
INTERROGATIONS = "ints"

# construction functions
def make_const(value):
    return (CONST, value)

def make_var(name):
    return (VAR, name)

def make_atom(predicate, *args):
    return (ATOM, predicate, list(args))

def make_function_call(function, *args):
    return (FUNC, function, list(args))

def make_interogation(atom):
    return (INTEROGATION, atom)

def make_neg(sentence):
    return (NEG, NEG, [sentence])

def make_and(sentence1, sentence2, *others):
    return (AND, AND, [sentence1, sentence2] + list(others))

def make_or(sentence1, sentence2, *others):
    return (OR, OR, [sentence1, sentence2] + list(others))

def is_term(f):
    return is_constant(f) or is_variable(f) or is_function_call(f)

def is_constant(f):
    return f[0] == CONST

def is_variable(f):
    return f[0] == VAR

def is_function_call(f):
    return f[0] == FUNC

def is_atom(f):
    return f[0] == ATOM

def is_sentence(f):
    return is_atom(f) or f[0] == AND or f[0] == OR or f[0] == NEG

def has_args(f):
    return is_function_call(f) or is_sentence(f)

def is_fact(formula):
    if is_atom(formula):
        return True
    return False

def is_positive_literal(L):
    return is_atom(L)

def is_negative_literal(L):
    return get_head(L) == NEG and is_positive_literal(get_args(L)[0])

def is_literal(L):
    return is_positive_literal(L) or is_negative_literal(L)

def is_rule(formula):
    return not is_fact(formula)

# get functions
def get_value(f):
    return f[1] if is_constant(f) else None

def get_name(f):
    return f[1] if is_variable(f) else None

def get_args(f):
    return f[2] if has_args(f) else None

def get_head(f):
    if is_atom(f) or is_function_call(f) or is_sentence(f):
        return f[1]
    return None

def get_premises(formula):
    args = get_args(formula)
    premises = []
    for arg in args:
        if is_negative_literal(arg):
            premises.append(arg)
    return premises

def get_coef(sentence):
    return sentence[len(sentence) - 1]

def get_index(sentence):
    return sentence[len(sentence) - 2]

def get_conclusion(formula):
    args = get_args(formula)
    for arg in args:
        if is_positive_literal(arg):
            return arg
    return None

# modify functions
def replace_args(formula, new_args):
    return (formula[0], formula[1], list(new_args))

def equal_terms(t1, t2):
    if is_constant(t1) and is_constant(t2):
        return get_value(t1) == get_value(t2)
    if is_variable(t1) and is_variable(t2):
            return get_name(t1) == get_name(t2)
    if is_function_call(t1) and is_function_call(t2):
        if get_head(t1) != get_head(t2):
            return all([equal_terms(get_args(t1)[i], get_args(t2)[i]) for i in range(len(get_args(t1)))])
    return False

def is_equal_to(a1, a2):
    if not (is_atom(a1) and is_atom(a2) and get_head(a1) == get_head(a2) and len(get_args(a1)) == len(get_args(a2))):
        return False
    return all([equal_terms(get_args(a1)[i], get_args(a2)[i]) for i in range(len(get_args(a1)))])


def print_formula(f, return_result = False):
    ret = ""
    if is_term(f):
        if is_constant(f):
            ret += str(get_value(f))
        elif is_variable(f):
            ret += "?" + get_name(f)
        elif is_function_call(f):
            ret += str(get_head(f)) + "[" + "".join([print_formula(arg, True) + "," for arg in get_args(f)])[:-1] + "]"
        else:
            ret += "???"
    elif is_atom(f):
        ret += str(get_head(f)) + "(" + "".join([print_formula(arg, True) + ", " for arg in get_args(f)])[:-2] + ")"
    elif is_sentence(f):
        # negation, conjunction or disjunction
        args = get_args(f)
        if len(args) == 1:
            ret += str(get_head(f)) + print_formula(args[0], True)
        else:
            ret += "(" + str(get_head(f)) + "".join([" " + print_formula(arg, True) for arg in get_args(f)]) + ")"
    else:
        ret += "???"
    if return_result:
        return ret
    print(ret)
    return

def print_rule(rule, tabs):
    ret = "[ "
    premises = [get_args(x)[0] for x in get_premises(rule)]
    conclusion = get_conclusion(rule)
    ret += print_formula(conclusion, return_result=True) + " : "
    str_premise = ""
    for premise in premises:
        str_premise += print_formula(premise, return_result=True) + ", "
    str_premise = str_premise[:-2]

    return "Incercam " + ret + str_premise + " ]\n" + "  " * (tabs) + "Scopuri de demonstrat: " + str_premise

def substitute(f, substitution):
    if substitution is None:
        return None
    if is_variable(f) and (get_name(f) in substitution):
        return substitute(substitution[get_name(f)], substitution)
    if has_args(f):
        return replace_args(f, [substitute(arg, substitution) for arg in get_args(f)])
    return f

def occur_check(v, t, subst):
    if v == t:
        return True
    if is_variable(t) and (get_name(t) in subst):
        return occur_check(v, substitute(t,subst), subst)
    if is_function_call(t):
        for arg in get_args(t):
            if occur_check(v, arg, subst):
                return True
    return False

def unify(f1, f2, subst = None):

    if subst is None:
        subst = {}

    S = []
    S.append((f1, f2))

    while len(S) > 0:
        (s, t) = S.pop()

        while is_variable(s) and (get_name(s) in subst):
            s = substitute(s, subst)

        while is_variable(t) and (get_name(t) in subst):
            t = substitute(t, subst)

        if (s != t):
            if is_variable(s):
                if occur_check(s, t, subst):
                    return False
                else:
                    subst[get_name(s)] = t
            elif is_variable(t):
                if occur_check(t, s, subst):
                    return False
                else:
                    subst[get_name(t)] = s
            elif has_args(s) and has_args(t):
                if get_head(s) == get_head(t):
                    args_s = get_args(s)
                    args_t = get_args(t)
                    if len(args_s) == len(args_t):
                        for i in range(len(args_s)):
                            S.append((args_s[i], args_t[i]))
                    else:
                        return False
                else:
                    return False
            else:
                return False

    return subst

def apply_rule(rule, facts):
    premises = get_premises(rule)
    conclusion = get_conclusion(rule)

    substitutions = [{}]

    for premise in premises:
        new_substs = []
        for subst in substitutions:
            for fact in facts:
                new_fact = make_neg(fact)
                new_subst = unify(new_fact, premise, copy.deepcopy(subst))
                if new_subst != False:
                    new_substs.append(new_subst)
        substitutions = new_substs

    concls = []

    for subst in substitutions:
        concls.append(substitute(conclusion, subst))

    return concls

def add_statement(kb, conclusion, *hypotheses):
    s = conclusion if not hypotheses else make_or(*([make_neg(s) for s in hypotheses] + [conclusion]))
    kb.append(s)

def convert_to_tuple(x):
    final_list = []
    for y in x:
        if type(y) == list:
            final_list.append(convert_to_tuple(y))
        elif type(y) == tuple:
            final_list.append(convert_to_tuple(y))
        else:
            final_list.append(y)
    return tuple(final_list)

def merge(dict1, dict2):
    keys1 = dict1.keys()
    keys2 = dict2.keys()
    intersection = keys1 & keys2

    for key in intersection:
        if dict1[key] != dict2[key]:
            return -1

    return {**dict1, **dict2}

def print_solution(solution, tabs):
    ret = "  " * (tabs + 1) + "***************\n" + "  " * (tabs + 1) + "Solution: \n"
    keys = list(solution.keys())
    keys = reversed(keys)

    for k in keys:
        ret += "  " * (tabs + 2) + k + " : " + solution[k][1] + "\n"

    return ret[:-1]

def has_same_var_names(conclusion, theorem):
    if has_args(conclusion) and has_args(theorem):
        c_args = get_args(conclusion)
        t_args = get_args(theorem)
        subst = {}
        for arg in t_args:
            for c_arg in c_args:
                if is_variable(arg) and is_variable(c_arg):
                    if arg == c_arg:
                        subst[get_name(c_arg)] = make_var(get_name(c_arg) + "_c")
    return subst

has_vars = False
initial_theorem = None
was_proved = False
all_solutions = []
var_sol_list = []
visited =[]
has_coeficients = False
coeficients = {}
coeficients_sol_list = []
longest_formula = ""

def check_if_sol_exists(current_sol):

    if current_sol == {}:
        return False

    for sol in all_solutions:
        exists = True
        for var in var_sol_list:
            if sol[var] != current_sol[var]:
                exists = False
                break
        if exists:
            return True

    return False

def evaluate_formula(formula):
    ints = re.findall(r"\d+", formula)
    ints = sorted(ints, reverse=True)
    new_formula = ""

    idx = 0
    while idx < len(formula):
        found = False
        for i in ints:
            if formula.startswith(i, idx):
                if int(i) == 10:
                    new_formula += "10"
                else:
                    new_formula += str(coeficients[list(coeficients.keys())[int(i)]])
                found = True
                if len(i) >= 2:
                    idx += len(i) - 1
                break
        if not found:
            new_formula += formula[idx]
        idx += 1

    return eval(new_formula)

def calculate_formula_for_rule(rule, initial_rule):
    premises = [get_args(x)[0] for x in get_premises(rule)]
    idx_to_replace = str(list(coeficients.keys()).index(convert_to_tuple(initial_rule)))
    cur_rule_formula = idx_to_replace + "*min("
    for premise in premises:
        if convert_to_tuple(premise) in coeficients:
            cur_rule_formula += str(list(coeficients.keys()).index(convert_to_tuple(premise))) + ","
        else:
            cur_rule_formula += str(premise) + ","
    cur_rule_formula += "10)"
    return cur_rule_formula

def backward_chaining(kb, theorem, rest_of_theorems, current_sol, tabs, current_formula = "", verbose = True):
    global has_vars
    global was_proved
    global has_coeficients
    global longest_formula

    mc = []

    if (theorem, current_sol) in visited:
        return
    else:
        visited.append((theorem, current_sol))

    # if we already have this solution don't go more in depth
    if check_if_sol_exists(current_sol):
        return

    theorem = substitute(theorem, current_sol)
    print("  " * tabs + "Scop curent " + print_formula(theorem, True))

    # Verificăm dacă teorema este deja demonstrată
    for fact in filter(is_fact, kb):

        if not has_vars and was_proved and not has_coeficients:
            break

        k = unify(fact, theorem)

        if k or k == {}:

            if verbose:
                print("  " * (tabs + 1) + print_formula(fact, True) + " este un fapt")

            if rest_of_theorems == []:

                final_sol = merge(k, current_sol)

                # Daca avem o solutie valida
                if final_sol and final_sol != -1:

                    if check_if_sol_exists(final_sol):
                        return

                    was_proved = True

                    if has_vars:
                        print(print_solution(final_sol, tabs))
                        all_solutions.append(final_sol)
                        if has_coeficients:
                            if len(current_formula) > len(longest_formula):
                                longest_formula = current_formula
                    else:
                        print("  " * (tabs + 1) + "***************")
                        print("  " * (tabs + 2) + print_formula(initial_theorem, True) + " is true")
                        if has_coeficients:
                            if len(current_formula) > len(longest_formula):
                                longest_formula = current_formula
                        all_solutions.append("True")

                elif final_sol == {}:

                        was_proved = True
                        print("  " * (tabs + 1) + "***************")
                        print("  " * (tabs + 2) + print_formula(initial_theorem, True) + " is true")
                        if has_coeficients:
                            if len(current_formula) > len(longest_formula):
                                longest_formula = current_formula
                        all_solutions.append("True")

                elif final_sol == -1:
                    print("  " * (tabs + 1) + " Solutie invalida")

            else:
                # daca mai avem fapte de demonstrat

                next_sol = merge(k, current_sol)
                if next_sol == -1:
                    print("  " * (tabs + 1) + " Solutie invalida")
                    continue
                next_theorem = rest_of_theorems[0]
                next_rest_theorems = rest_of_theorems[1:]
                if next_sol != -1:
                    if has_coeficients:
                        backward_chaining(kb, next_theorem, next_rest_theorems, next_sol, tabs + 2, current_formula=current_formula)
                    else:
                        backward_chaining(kb, next_theorem, next_rest_theorems, next_sol, tabs + 2)

    # Cautam o regula care sa aiba drept concluzie teorema noastra
    for rule in filter(is_rule, kb):

        # daca teorema deja a fost demonstrata si nu trebuie sa gasim toate solutiile ne oprim
        if not has_vars and was_proved and not has_coeficients:
            break

        # rezolvam conflictele de nume
        substitution = has_same_var_names(get_conclusion(rule), theorem)
        rule_2 = substitute(rule, substitution)

        k = unify(get_conclusion(rule_2), theorem)
        if k or k == {}:
            mc.append((substitute(rule_2,k), rule))

    # Trecem prin fiecare regula
    while True:

        if mc == []:
            break

        current_rule, initial_rule = mc.pop()
        premises = [get_args(x)[0] for x in get_premises(current_rule)]
        premises.extend(rest_of_theorems)

        if verbose:
            print("  " * tabs + print_rule(current_rule, tabs))

        if not has_vars and was_proved and not has_coeficients:
            break

        next_formula = ""
        if has_coeficients:
            cur_rule_formula = calculate_formula_for_rule(current_rule, initial_rule)

            if len(mc) == 1:
                next_current_rule, next_initial_rule = mc[0]
                cur_rule_formula2 = calculate_formula_for_rule(next_current_rule, next_initial_rule)
                cur_rule_formula = "(" + cur_rule_formula + "+" + cur_rule_formula2 + "-" + cur_rule_formula \
                            + "*" + cur_rule_formula2 + ")"

            if current_formula == "":
                next_formula = cur_rule_formula
            else:
                next_formula = current_formula.replace(str(theorem), cur_rule_formula)

        backward_chaining(kb, premises[0], premises[1:], current_sol, tabs + 1, current_formula = next_formula)

    if not was_proved and rest_of_theorems == [] and tabs == 1:
       print("  " * tabs + print_formula(initial_theorem, True) + " is false")
    elif was_proved and rest_of_theorems == [] and has_coeficients and tabs == 1:
        coeficients_sol_list.append(evaluate_formula(longest_formula))

    return
