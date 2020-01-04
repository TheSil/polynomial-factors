import argparse
from copy import deepcopy
from expressions import Variable, ASSUMED_1, ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1, \
    ASSUMED_0_OR_1, assumed_type_str
from rules import basic_rules, check_remaining_coeffs, check_01_coeffs, check_terms, check_inequalities
from contradiction import Contradiction
from proof import Proof
import proof


class PolynomialProductAssumptions:

    def __init__(self, deg_p, deg_q):
        self.deg_p = deg_p
        self.deg_q = deg_q
        self.deg_r = deg_p + deg_q
        self.assumed_a = []
        self.assumed_b = []
        for i in range(self.deg_p + 1 + 1):
            self.assumed_a.append(Variable(ASSUMED_CLOSED_INTERVAL_0_TO_1, f"a_{i}"))
        for i in range(self.deg_q + 1 + 1):
            self.assumed_b.append(Variable(ASSUMED_CLOSED_INTERVAL_0_TO_1, f"b_{i}"))
        init_proof = Proof()
        # monic polynomials
        self.assumed_a[self.deg_p].adjust(ASSUMED_1, 2, init_proof)
        self.assumed_b[self.deg_q].adjust(ASSUMED_1, 2, init_proof)
        # we can safely assume that constant coefficients are 1
        self.assumed_a[0].adjust(ASSUMED_1, 2, init_proof)
        self.assumed_b[0].adjust(ASSUMED_1, 2, init_proof)
        init_proof.print()
        self.additional_assumptions = []

    def __str__(self):
        # print all the non-trivial assumptions
        res = ""
        for i in range(1, self.deg_p):
            if self.assumed_a[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"{self.assumed_a[i]}, "
        for i in range(1, self.deg_q):
            if self.assumed_b[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"{self.assumed_b[i]}, "
        return res


# class CoeffCondition:
#     coeff_a = 0
#     coeff_b = 1
#
#     def __init__(self, coeff_type, coeff_index):
#         self.coeff_type = coeff_type
#         self.coeff_index = coeff_index

def apply_all_rules_nonrecursive(assumptions, proof, level):
    return apply_all_rules(assumptions, proof, level, recursive=False)


def apply_all_rules(assumptions, proof, level, recursive=True):

    changed = True
    while changed:
        changed = False

        assumptions.additional_assumptions = []

        while basic_rules(assumptions, level=level, proof=proof):
            pass

        # Failed to find contradiction, try separate (0,1) vs {0,1} cases for the other coefficients
        if not changed:
            if check_remaining_coeffs(assumptions, 1, proof=proof):
                changed = True

        # still no contradiction... iterate over a_i/b_i which must be in {0,1} and
        # check where the both possibilities lead to
        if not changed:
            if check_01_coeffs(assumptions, proof=proof):
                changed = True

        if not changed:
            if check_terms(assumptions, proof=proof):
                changed = True

        if not changed:
            # We still have not found a contradiction, try to find one of a from
            # 1 = [x^k]R(x) = a*b + c*d < a+b+.... = [x^l]R(x) = 1
            # with a,b,c,d in (0,1)
            if check_inequalities(assumptions, proof):
                changed = True

        if not changed and recursive:
            for condition_check in assumptions.additional_assumptions:
                condition_check.check(assumptions, proof=proof, level=level+1, rules_checker=apply_all_rules_nonrecursive)



def check_factorization(a, b):
    proof = Proof()
    proof.report(1, f"Assuming R(x)=P(x)Q(x) with deg P={a}, deg Q={b}")
    poly_str = ""
    for i in range(a + 1):
        poly_str += f"a_{i}"
        if i != 0:
            poly_str += f"*x^{i}"
        if i != a:
            poly_str += "+"
    proof.report(1, f"P(x)={poly_str}")
    poly_str = ""
    for i in range(b + 1):
        poly_str += f"b_{i}"
        if i != 0:
            poly_str += f"*x^{i}"
        if i != b:
            poly_str += "+"
    proof.report(1, f"Q(x)={poly_str}")
    proof.print()
    assumptions = PolynomialProductAssumptions(a, b)

    contradiction_proof = Proof()
    try:
        apply_all_rules(assumptions, contradiction_proof, 3)
    except Contradiction:
        contradiction_proof.print()
        return True

    contradiction_proof.print()

    for i in range(1, a // 2 + 1):
        # assume a_i in (0,1) for each i is the smallest with this property (hence smaller coefficients in {0,1}
        # and try to reach contradiction for EACH ONE
        tmp_proof = Proof()
        try:
            tmp_assumptions = deepcopy(assumptions)
            tmp_proof.report(2, f"Assuming {i} is the smallest with a_{i} in (0,1)")
            tmp_assumptions.assumed_a[i].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, 3, tmp_proof)

            apply_all_rules(tmp_assumptions, tmp_proof, 3)

            print(f" Failed to find contradiction for n={n},a={a},b={b} when assuming"
                  f" a_{i} in (0,1) is smallest with this property")
            print("", tmp_assumptions)
            # return False  # comment this to see all fails for given degree
        except Contradiction:
            pass

        if i != a // 2:
            try:
                assumptions.assumed_a[i].adjust(ASSUMED_0_OR_1, 2, tmp_proof)
                assumptions.assumed_b[i].adjust(ASSUMED_0_OR_1, 2, tmp_proof)
            except Contradiction:
                # probably b_i cannot be 0 or 1, which means we can end it here
                # all higher a_i's will cause the same contradiction
                return True

        tmp_proof.print()

    return True


def check_degree(deg_r):
    result = True
    # degree of any counterexample >= 6 by paper/pencil proof
    for deg_a in range(6, deg_r // 2 + 1):
        deg_b = deg_r - deg_a
        if not check_factorization(deg_a, deg_b):
            result = False
            # break  # comment this to see all fails for given degree
    return result


if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='Find polynomials 0,1 factors contradiction.')
    parser.add_argument('--min', type=int, help='minimal degree of R(x)')
    parser.add_argument('--max', type=int, help='maximal degree of R(x)')
    parser.add_argument('-v', '--verbose', action='store_true', default=False, help='detailed report')
    args = parser.parse_args()

    min_n = args.min
    max_n = args.max
    proof.report_enabled = args.verbose

    for n in range(min_n, max_n + 1):
        print(f"Checking deg R={n}")
        if not check_degree(n):
            print("Counterexample not ruled out for n =", n)
        # print()
        # report(0, "")
