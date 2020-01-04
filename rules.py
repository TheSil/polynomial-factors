from copy import deepcopy
from itertools import chain
from expressions import Multiplication, assumed_type_str
from expressions import ASSUMED_0, ASSUMED_1, ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1, \
    ASSUMED_0_OR_1
from contradiction import Contradiction
from proof import Proof

class ConditionChecker:
    pass

class CoeffConditionChecker(ConditionChecker):

    coeff_a = 0
    coeff_b = 1

    def __init__(self, coeff_type, coeff_index, check_type):
        self.coeff_type = coeff_type
        self.coeff_index = coeff_index
        self.check_type = check_type

    def check(self, assumptions, proof, level, rules_checker):
        if self.coeff_type == self.coeff_a:
            proof.report(level, f"Assuming a_{self.coeff_index} {assumed_type_str(self.check_type)}")
            assumptions.assumed_a[self.coeff_index].adjust(self.check_type, level + 1, proof)
        else:
            proof.report(level, f"Assuming b_{self.coeff_index} {assumed_type_str(self.check_type)}")
            assumptions.assumed_b[self.coeff_index].adjust(self.check_type, level + 1, proof)

class ProductConditionChecker(ConditionChecker):

    def __init__(self, coeff_a_index, coeff_b_index, check_type):
        self.coeff_a_index = coeff_a_index
        self.coeff_b_index = coeff_b_index
        self.check_type = check_type

    def check(self, assumptions, proof, level, rules_checker):
        multi = Multiplication(assumptions.assumed_a[self.coeff_a_index], assumptions.assumed_b[self.coeff_b_index])
        multi.adjust(self.check_type, level + 1, proof)

        if rules_checker:
            rules_checker(assumptions, level=level + 1, proof=proof)


class OrConditionChecker(ConditionChecker):

    def __init__(self):
        self.conditions = []

    def add(self, condition):
        self.conditions.append(condition)

    def check(self, assumptions, proof, level, rules_checker):
        viable = []
        msg = ""
        # for idx, assumption in enumerate(assumed_list):
        #     msg += assumption.name + " "
        #     msg += assumed_type_str(assumed)
        #     if idx != len(assumed_list) - 1:
        #         msg += " or "
        assumption_proof = Proof()
        assumption_proof.report(level, msg)
        for idx, condition in enumerate(self.conditions):
            tmp_assumptions = deepcopy(assumptions)
            tmp_proof = Proof()
            try:
                # since this is a copy, we need to link to its objects!
                #tmp_proof.report(level, f"Assuming {assumption_copy.name} {assumed_type_str(assumed)}")
                condition.check(tmp_assumptions, tmp_proof, level+1, None)
                rules_checker(tmp_assumptions, level=level + 1, proof=tmp_proof)
                # proof += report(level + 1, f"No contradiction")
                viable.append(idx)
            except Contradiction:
                assumption_proof.append(tmp_proof)
                pass
        if len(viable) == 0:
            # not possible
            assumption_proof.report(level, "All possibilities lead to contradiction => contradiction")
            proof.append(assumption_proof)
            raise Contradiction()

        if len(viable) == 1:
            # that one must satisfy the assumption
            assumption_proof.report(level, f"Exactly one possibility yields no contradiction => ")
            #f"{assumed_list[viable[0]].name} {assumed_type_str(assumed)}")
            self.conditions[viable[0]].check(assumptions, assumption_proof, level + 1, None)
            rules_checker(assumptions, level=level + 1, proof=assumption_proof)
            proof.append(assumption_proof)


class AndConditionChecker(ConditionChecker):
    pass



# following are rules that adjust the assumptions (and eventually should reach contradiction)
# - each rule should create assumptions copy as necessary, and should eventually output additional possible assumptions
# - rules should not ideally recursively call any of the other rules, instead they should put their potential assumptions out
#   and let the outer engine try to find the contradictions

def basic_rules(assumptions, level, proof):
    changed = False
    # additional assumptions need to be kept in side assumptions, so that deepcopy will correctly
    # link all references in temporary instances
    for k in range(assumptions.deg_r + 1):
        open_idxs = []
        closed_idxs = []
        ones_idxs = []
        zeroes_idxs = []
        zero_or_one_idxs = []
        for i in range(max(0, k - assumptions.deg_q), min(assumptions.deg_p, k) + 1):
            # a_i * b_j
            j = k - i
            ab_assumption = Multiplication(assumptions.assumed_a[i], assumptions.assumed_b[j])
            if ab_assumption.assumed_type == ASSUMED_0:
                zeroes_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_1:
                ones_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                open_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
                closed_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_0_OR_1:
                zero_or_one_idxs.append(i)
            else:
                raise Exception("Unknown assumed type")

        if len(closed_idxs) == 1 and len(open_idxs) == 0 and len(ones_idxs) == 0 and len(zero_or_one_idxs) == 0:
            # exactly one term, it must be in {0,1}
            i = closed_idxs[0]
            j = k - i
            proof.report(level,
                         f"At coeff [x^{k}](R(x)), term a_{i}*b_{j} in [0,1] is the only non-zero term "
                         f"=> a_{i}*b_{j} in {{0,1}}")
            product = Multiplication(assumptions.assumed_a[i], assumptions.assumed_b[j])
            if product.adjust(ASSUMED_0_OR_1, level + 1, proof):
                changed = True

        if len(open_idxs) == 1:
            if len(zero_or_one_idxs) > 0:
                # all of these muse be zero
                for i in zero_or_one_idxs:
                    j = k - i
                    product = Multiplication(assumptions.assumed_a[i], assumptions.assumed_b[j])
                    if product.adjust(ASSUMED_0, level + 1, proof):
                        changed = True

            if len(closed_idxs) == 0:
                # exactly one of summands is in (0,1) and rest gives an integer together
                i = open_idxs[0]
                j = k - i
                proof.report(level,
                             f"Term a_{i}*b_{j} is the only non-integer term at coeff [x^{k}](R(x)) => contradiction")
                raise Contradiction()
            elif len(closed_idxs) == 1:
                # exactly one of summands is in (0,1),  rest gives an integer together EXCEPT for one coefficient
                # then that coefficients must be in (0,1) too, which means both a_i and b_j in it must be (0,1) or 1
                i = closed_idxs[0]
                j = k - i
                i_open = open_idxs[0]
                j_open = k - i_open
                proof.report(level,
                             f"At coeff [x^{k}](R(x)), term a_{i_open}*b_{j_open} in (0,1) and a_{i}*b_{j} in [0,1] is the "
                             f"only possible non-integer term  => a_{i}*b_{j} in (0,1)")
                product = Multiplication(assumptions.assumed_a[i], assumptions.assumed_b[j])
                if product.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1, proof):
                    changed = True
            else:
                # one of other summands must be in (0,1)
                condition = OrConditionChecker()
                for i in closed_idxs:
                    j = k - i
                    condition.add(ProductConditionChecker(i,j, ASSUMED_OPEN_INTERVAL_0_TO_1 ))
                assumptions.additional_assumptions.append(condition)

        if len(ones_idxs) > 1:
            i1 = ones_idxs[0]
            j1 = k - i1
            i2 = ones_idxs[1]
            j2 = k - i2
            proof.report(level, f"Coeff [x^{k}](R(x)) >= a_{i1}*b_{j1} + a_{i2}*b_{j2} >= 1 + 1 => contradiction")
            raise Contradiction()

        if len(ones_idxs) == 1:
            # there is 1 in summands, all other terms must be 0
            min_i = max(0, k - assumptions.deg_q)
            max_i = min(assumptions.deg_p, k)
            if max_i - min_i > 0:
                tmp_proof = Proof()
                tmp_proof.report(level, f"Coeff [x^{k}](R(x)) = 1 + ... => all other terms must equal 0")
                tmp_changed = False
                try:
                    for i in range(min_i, max_i + 1):
                        if i != ones_idxs[0]:
                            # a_i * b_j
                            j = k - i
                            product = Multiplication(assumptions.assumed_a[i], assumptions.assumed_b[j])
                            if product.adjust(ASSUMED_0, level + 1, proof=tmp_proof):
                                tmp_changed = True
                            else:
                                if assumptions.assumed_a[i].assumed_type != ASSUMED_0 \
                                        and assumptions.assumed_b[j].assumed_type != ASSUMED_0:
                                    assumptions.additional_assumptions.append(
                                        ProductConditionChecker(i, j, ASSUMED_0))
                except Contradiction:
                    proof.append(tmp_proof)
                    raise

                if tmp_changed:
                    proof.append(tmp_proof)
                    changed = True

    return changed

def check_terms(assumptions, proof):
    changed = False
    # additional assumptions need to be kept in side assumptions, so that deepcopy will correctly
    # link all references in temporary instances
    for k in range(assumptions.deg_r + 1):
        open_idxs = []
        closed_idxs = []
        ones_idxs = []
        zeroes_idxs = []
        zero_or_one_idxs = []
        for i in range(max(0, k - assumptions.deg_q), min(assumptions.deg_p, k) + 1):
            # a_i * b_j
            j = k - i
            ab_assumption = Multiplication(assumptions.assumed_a[i], assumptions.assumed_b[j])
            if ab_assumption.assumed_type == ASSUMED_0:
                zeroes_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_1:
                ones_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                open_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
                closed_idxs.append(i)
            elif ab_assumption.assumed_type == ASSUMED_0_OR_1:
                zero_or_one_idxs.append(i)
            else:
                raise Exception("Unknown assumed type")

        for i in chain(closed_idxs, zero_or_one_idxs):
            j = k - i

            # TODO: could be exclusive OR, how would that differ?
            condition = OrConditionChecker()
            condition.add(ProductConditionChecker(i, j, ASSUMED_OPEN_INTERVAL_0_TO_1))
            condition.add(ProductConditionChecker(i, j, ASSUMED_0))
            condition.add(ProductConditionChecker(i, j, ASSUMED_1))
            assumptions.additional_assumptions.append(condition)

    return changed

def check_remaining_coeffs(assumptions, i, proof):
    changed = False
    for j in range(i + 1, assumptions.deg_p):
        # TODO: could be exclusive OR, how would that differ?
        condition = OrConditionChecker()
        condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_a, j, ASSUMED_OPEN_INTERVAL_0_TO_1))
        condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_a, j, ASSUMED_0))
        condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_a, j, ASSUMED_1))
        assumptions.additional_assumptions.append(condition)

    for j in range(i + 1, assumptions.deg_q):
        # TODO: could be exclusive OR, how would that differ?
        condition = OrConditionChecker()
        condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_b, j, ASSUMED_OPEN_INTERVAL_0_TO_1))
        condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_b, j, ASSUMED_0))
        condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_b, j, ASSUMED_1))
        assumptions.additional_assumptions.append(condition)

    return changed

def check_01_coeffs(assumptions, proof):
    changed = False
    for j in range(1, assumptions.deg_p):
        if assumptions.assumed_a[j].assumed_type == ASSUMED_0_OR_1:
            condition = OrConditionChecker()
            condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_a, j, ASSUMED_0))
            condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_a, j, ASSUMED_1))
            assumptions.additional_assumptions.append(condition)

    for j in range(1, assumptions.deg_q):
        if assumptions.assumed_b[j].assumed_type == ASSUMED_0_OR_1:
            condition = OrConditionChecker()
            condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_b, j, ASSUMED_0))
            condition.add(CoeffConditionChecker(CoeffConditionChecker.coeff_b, j, ASSUMED_1))
            assumptions.additional_assumptions.append(condition)

    return changed


def check_inequalities(assumptions, proof):
    lone_idxs = {}  # list of R(x) coeffs' lone terms, such as a_1+b_3
    two_pairs_idxs = {}  # list of R(x) coeffs that have exactly two terms in form a*b+c*d all from (0,1)
    for k in range(assumptions.deg_r + 1):
        lone_idxs[k] = []
        pairs = []
        non_zero = 0
        for i in range(max(0, k - assumptions.deg_q), min(assumptions.deg_p, k) + 1):
            # a_i * b_j
            j = k - i
            if assumptions.assumed_a[i].assumed_type == ASSUMED_1 and \
                    assumptions.assumed_b[j].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                lone_idxs[k].append(('b', j))
            elif assumptions.assumed_a[i].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and \
                    assumptions.assumed_b[j].assumed_type == ASSUMED_1:
                lone_idxs[k].append(('a', i))
            elif assumptions.assumed_a[i].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and \
                    assumptions.assumed_b[j].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                pairs.append((i, j))

            if assumptions.assumed_a[i].assumed_type != ASSUMED_0 and \
                    assumptions.assumed_b[j].assumed_type != ASSUMED_0:
                non_zero += 1

        if non_zero == len(pairs) and len(pairs) == 2:
            # this coefficient is exactly of form a*b+c*d
            two_pairs_idxs[k] = pairs

    # try to find the inequality now
    for k in two_pairs_idxs:
        pairs = two_pairs_idxs[k]
        a = pairs[0][0]
        b = pairs[0][1]
        c = pairs[1][0]
        d = pairs[1][1]

        for k2 in lone_idxs:
            idxs = lone_idxs[k2]
            if ('a', a) in idxs and ('a', c) in idxs:
                proof.report(3,
                             f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < a_{a}+a_{c} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()
            elif ('a', a) in idxs and ('b', d) in idxs:
                proof.report(3,
                             f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < a_{a}+b_{d} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()
            elif ('b', b) in idxs and ('a', c) in idxs:
                proof.report(3,
                             f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < b_{b}+a_{c} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()
            elif ('b', b) in idxs and ('b', d) in idxs:
                proof.report(3,
                             f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < b_{b}+b_{d} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()

    # leads only to contradictions, no change
    return False
