import re
import atom_utils

FACTS = "facts"
RULES = "rules"
INTERROGATIONS = "ints"

def compose_atom(atom_string):
    atom_string = atom_string.replace(" ", "")
    predicate_name = atom_string.split("(")[0]
    terms = re.split("[(,)]", atom_string)[:-1][1:]
    made_terms = []
    for t in terms:
        if t == "":
            continue
        if "?" in t:
            new_var = atom_utils.make_var(t[1:])
            made_terms.append(new_var)
        elif "(" in t:
            continue
        else:
            new_ct = atom_utils.make_const(t)
            made_terms.append(new_ct)
    return atom_utils.make_atom(predicate_name, *made_terms)

def parse_affirmation(line):
    if ":" not in line:
        return compose_atom(line)
    else:
        atom, conditions = line.split(":")[0].strip(),line.split(":")[1].replace(" ","")
        # split by commas not inside parens
        conditions_atom_list = re.split(r",(?![^(]*\))", conditions)
        real_atom = compose_atom(atom)
        conditions_list = []
        for cond in conditions_atom_list:
            conditions_list.append(compose_atom(cond))
        neg_conditions_list = [atom_utils.make_neg(x) for x in conditions_list]

        return atom_utils.make_or(real_atom, *neg_conditions_list)

def parse_interogation(line):
    atom = compose_atom(line[2:])
    return atom_utils.make_interogation(atom)

def read_file(file):
    f = open(file, "r")
    statements = []
    interogations = []

    for line in f:
        line = line.strip()
        if not line:
            continue

        if line[0] == "#" or line[0] == "%" or line[0] == ":":
            continue

        if line[0] == "?":
            interogations.append(parse_interogation(line))
        else:
            x = parse_affirmation(line)
            statements.append(x)

    f.close()

    return (statements, interogations)