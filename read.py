import re
import atom_utils

FACTS = "facts"
RULES = "rules"
INTERROGATIONS = "ints"

def compose_function(function_string):
    function_string = function_string.replace(" ", "")
    function_name = function_string.split("(")[0]
    function_string = function_string[:-1][len(function_name) + 1:]
    terms = re.split(r",(?![^(]*\))", function_string)
    made_terms = []
    for t in terms:
        if t == "":
            continue
        if "?" in t:
            new_var = atom_utils.make_var(t[1:])
            made_terms.append(new_var)
        else:
            new_ct = atom_utils.make_const(t)
            made_terms.append(new_ct)

    return atom_utils.make_function_call(function_name, *made_terms)

def compose_atom(atom_string):
    atom_string = atom_string.replace(" ", "")
    predicate_name = atom_string.split("(")[0]
    atom_string = atom_string[:-1][len(predicate_name) + 1:]
    terms = re.split(r",(?![^(]*\))", atom_string)
    made_terms = []
    for t in terms:
        if t == "":
            continue

        if "(" in t:
            new_func = compose_function(t)
            made_terms.append(new_func)
        elif "?" in t:
            new_var = atom_utils.make_var(t[1:])
            made_terms.append(new_var)
        else:
            new_ct = atom_utils.make_const(t)
            made_terms.append(new_ct)
    return atom_utils.make_atom(predicate_name, *made_terms)

def parse_affirmation(line):
    # for coeficient
    if "%" not in line:
        coeficient = 1.0
    else:
        coeficient = float(line.split("%")[1].strip())
        line = line.split("%")[0].strip()

    if ":" not in line:
        return compose_atom(line), coeficient
    else:
        atom, conditions = line.split(":")[0].strip(),line.split(":")[1].replace(" ","")
        # split by commas not inside parens
        conditions_atom_list = re.split(r",(?![^(]*\))", conditions)
        real_atom = compose_atom(atom)
        conditions_list = []
        for cond in conditions_atom_list:
            conditions_list.append(compose_atom(cond))
        neg_conditions_list = [atom_utils.make_neg(x) for x in conditions_list]

        return atom_utils.make_or(real_atom, *neg_conditions_list), coeficient

def parse_interogation(line):
    atom = compose_atom(line[2:])
    return atom_utils.make_interogation(atom)

def read_file(file):
    f = open(file, "r")
    statements = []
    interogations = []
    coeficients = {}

    for line in f:
        line = line.strip()
        if not line:
            continue

        if line[0] == "#" or line[0] == "%" or line[0] == ":":
            continue

        if line[0] == "?":
            interogations.append(parse_interogation(line))
        else:
            x, coef = parse_affirmation(line)
            statements.append(x)
            coeficients[atom_utils.convert_to_tuple(x)] = coef

    f.close()

    return (statements, interogations, coeficients)