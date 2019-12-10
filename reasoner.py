import sys
import read
import copy
import atom_utils

FACTS = "facts"
RULES = "rules"
INTERROGATIONS = "ints"

def check_for_vars(atom):
    var_list = []
    if atom_utils.has_args(atom):
        args = atom_utils.get_args(atom)
        for arg in args:
            if atom_utils.is_variable(arg):
                var_list.append(atom_utils.get_name(arg))
    return var_list

def print_all_solutions(solutions, var_list):
    final_string = ""
    for idx, solution in enumerate(solutions):
        string = "Solution " + str(idx) + " = "
        for var in var_list:
            string += str(var) + " : " + str(solution[var]) + ", "
        final_string += string[:-2] + "\n"

    return final_string

def main():
    statements, interogations, coeficients = read.read_file(sys.argv[1])

    for st in statements:
        print(st, coeficients[atom_utils.convert_to_tuple(st)])
        if coeficients[atom_utils.convert_to_tuple(st)] != 1:
            atom_utils.has_coeficients = True
    print()

    for intr in interogations:
        print("Scopul de demonstrat " + atom_utils.print_formula(intr[1], return_result=True))
        statements_aux = copy.deepcopy(statements)
        atom_utils.var_sol_list = check_for_vars(intr[1])
        atom_utils.has_vars = True if atom_utils.var_sol_list != [] else False
        atom_utils.was_proved = False
        atom_utils.all_solutions = []
        atom_utils.visited = []
        atom_utils.initial_theorem = intr[1]
        atom_utils.coeficients = coeficients
        atom_utils.coeficients_sol_list = []
        atom_utils.longest_formula = ""
        atom_utils.backward_chaining(statements_aux, intr[1], [], {}, 1)
        print("Gata")
        if atom_utils.has_vars:
            print(print_all_solutions(atom_utils.all_solutions, atom_utils.var_sol_list))
        else:
            if atom_utils.all_solutions == []:
                print(atom_utils.print_formula(intr[1], return_result= True) + " is false\n")
            else:
                print(atom_utils.print_formula(intr[1], return_result= True) + " is True")
                if atom_utils.has_coeficients:
                    print("Coeficient: " + "%.3f" % atom_utils.coeficients_sol_list[0])
                print()

if __name__ == "__main__":
    # this is done for larger tests(testl4)
    sys.setrecursionlimit(22000)
    main()
