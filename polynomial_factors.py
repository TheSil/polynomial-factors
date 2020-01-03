import argparse
from copy import deepcopy


class Contradiction(Exception):
    def __init__(self):
        pass


ASSUMED_CLOSED_INTERVAL_0_TO_1 = 1
ASSUMED_OPEN_INTERVAL_0_TO_1 = 2
ASSUMED_0 = 3
ASSUMED_1 = 4
ASSUMED_0_OR_1 = 5


def assumed_type_str(assumed_type):
    if assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
        return "in (0,1)"
    elif assumed_type == ASSUMED_0:
        return "= 0"
    elif assumed_type == ASSUMED_1:
        return "= 1"
    elif assumed_type == ASSUMED_0_OR_1:
        return "in {0,1}"
    elif assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
        return "in [0,1]"


report_enabled = True

class Proof:
    def __init__(self):
        self.msg = ""

    def report(self, level, msg):
        self.msg += level * " " + msg + "\n"

    def append(self, proof):
        self.msg += proof.msg

    def append_str(self, str):
        self.msg += str

    def print(self):
        global report_enabled
        if report_enabled:
            print(self.msg.rstrip())


class Assumption:
    pass


class RawAssumption(Assumption):
    def __init__(self, assumed_type, name):
        self.assumed_type = assumed_type
        self.name = name

    def adjust(self, new_assumed_type, level, proof):
        if self.assumed_type == new_assumed_type:
            return False

        if new_assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
            return False

        if new_assumed_type == ASSUMED_0_OR_1:
            if self.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1):
                # already compatible, do nothing
                return False
            if self.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ):
                proof.report(level, f"Since {self} = > contradiction")
                raise Contradiction()
        elif new_assumed_type == ASSUMED_0:
            if self.assumed_type not in (ASSUMED_0, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                proof.report(level, f"Since {self} = > contradiction")
                raise Contradiction()
        elif new_assumed_type == ASSUMED_1:
            if self.assumed_type not in (ASSUMED_1, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                proof.report(level, f"Since {self} = > contradiction")
                raise Contradiction()
        elif new_assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
            if self.assumed_type not in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                proof.report(level, f"Since {self} = > contradiction")
                raise Contradiction()
        else:
            raise Exception("Unknown new assumption type")

        self.assumed_type = new_assumed_type
        proof.report(level, f"Then {self.name} {assumed_type_str(new_assumed_type)}")
        return True

    def __str__(self):
        return self.name + " " + assumed_type_str(self.assumed_type)


class MultipliedAssumptions2(Assumption):

    def __init__(self, a, b):
        self.a = a
        self.b = b
        self.name = f"{a.name}*{b.name}"

    def adjust(self, product, level, proof):
        # this function propagates product assumption into multiplicands if possible
        # e.g. 1*a in (0,1) implies that a in (0,1)
        if product == ASSUMED_OPEN_INTERVAL_0_TO_1:
            if self.a.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1) \
                    and self.b.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1):
                # a in {0,1} * b in {0,1} cannot give c in (0,1)
                proof.report(level, f"{self.name} in (0,1), but {self.a} and {self.b} => contradiction")
                raise Contradiction()

            if ASSUMED_0 in (self.a.assumed_type, self.b.assumed_type):
                proof.report(level, f"{self.name} in (0,1), but {self.a} and {self.b} => contradiction")
                raise Contradiction()

            if self.a.assumed_type == ASSUMED_0_OR_1 and self.b.assumed_type == ASSUMED_0_OR_1:
                proof.report(level, f"{self.name} in (0,1), but {self.a} and {self.b} => contradiction")
                raise Contradiction()

            if self.a.assumed_type not in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1) \
                    or self.b.assumed_type not in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                proof.report(level, f"{self.name} in (0,1), but {self.a} and {self.b} =>")
                if self.a.assumed_type == ASSUMED_1:
                    # 1*b in (0,1) implies that b in (0,1)
                    return self.b.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1, proof)
                elif self.b.assumed_type == ASSUMED_1:
                    # a*1 in (0,1) implies that a in (0,1)
                    return self.a.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1, proof)
                elif self.a.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1) \
                        and self.b.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                    # {0,1} * (0,1) in (0,1) implies first coefficient must be 1
                    return self.a.adjust(ASSUMED_1, level + 1, proof)
                elif self.a.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 \
                        and self.b.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1):
                    # (0,1) * {0,1} in (0,1) implies second coefficient must be 1
                    return self.b.adjust(ASSUMED_1, level + 1, proof)
                elif self.a.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1 \
                        and self.b.assumed_type == ASSUMED_0_OR_1:
                    # [0,1] * {0,1} in (0,1) implies second coefficient must be 1 and first in (0,1)
                    changed_a = self.a.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1, proof)
                    changed_b = self.b.adjust(ASSUMED_1, level + 1, proof)
                    return changed_a or changed_b
                elif self.a.assumed_type == ASSUMED_0_OR_1 \
                        and self.b.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
                    # {0,1} * [0,1] in (0,1) implies first coefficient must be 1 and second in (0,1)
                    changed_a = self.a.adjust(ASSUMED_1, level + 1, proof)
                    changed_b = self.b.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1, proof)
                    return changed_a or changed_b
                else:
                    raise Exception("Unhandled product (0,1) assumption combination")
        elif product == ASSUMED_0:
            # one of multiplicands must be 0, couple contradictions here
            if ASSUMED_0 in (self.a.assumed_type, self.b.assumed_type):
                return False

            if self.a.assumed_type in (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0_OR_1) and \
                self.b.assumed_type in (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0_OR_1):
                return False

            if self.a.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1) \
                    and self.b.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                proof.report(level, f"{self.name} = 0, but {self.a} and {self.b} => contradiction")
                raise Contradiction()

            proof.report(level, f"{self.name} = 0, but {self.a} and {self.b} =>")
            if self.a.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                return self.b.adjust(ASSUMED_0, level + 1, proof)
            elif self.b.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                return self.a.adjust(ASSUMED_0, level + 1, proof)
            else:
                raise Exception("Unhandled product (0) assumption combination")
        elif product == ASSUMED_0_OR_1:
            if self.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1):
                return False

            if self.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1,):
                proof.report(level, f"{self.name} in {{0,1}}, but {self} => contradiction")
                raise Contradiction()

            if self.a.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1 \
                and self.b.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
                return False

            proof.report(level, f"{self.name} in {{0,1}}, but {self.a} and {self.b} =>")
            if self.a.assumed_type == ASSUMED_1 and self.b.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
                return self.b.adjust(ASSUMED_0_OR_1, level + 1, proof)
            elif self.a.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1 and self.b.assumed_type == ASSUMED_1:
                return self.a.adjust(ASSUMED_0_OR_1, level + 1, proof)
            elif self.a.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and self.b.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
                return self.b.adjust(ASSUMED_0, level + 1, proof)
            elif self.a.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1 and self.b.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                return self.a.adjust(ASSUMED_0, level + 1, proof)
            elif self.a.assumed_type == ASSUMED_0_OR_1 and self.b.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                return self.a.adjust(ASSUMED_0, level + 1, proof)
            elif self.a.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and self.b.assumed_type == ASSUMED_0_OR_1:
                return self.b.adjust(ASSUMED_0, level + 1, proof)
            elif self.a.assumed_type == ASSUMED_0_OR_1 and self.b.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
                return False
            elif self.a.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1 and self.b.assumed_type == ASSUMED_0_OR_1:
                return False
            else:
                raise Exception("Unhandled product {0,1} assumption combination")

        elif product == ASSUMED_CLOSED_INTERVAL_0_TO_1:
            # everything is in [0,1]
            return False

        elif product == ASSUMED_1:
            if ASSUMED_OPEN_INTERVAL_0_TO_1 in (self.a.assumed_type, self.b.assumed_type):
                raise Contradiction()
            if ASSUMED_0 in (self.a.assumed_type, self.b.assumed_type):
                raise Contradiction()
            if self.a.assumed_type == ASSUMED_1 and \
                self.b.assumed_type in (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0_OR_1):
                self.b.adjust(ASSUMED_1, level + 1, proof)
                return True
            if self.b.assumed_type == ASSUMED_1 and \
                self.a.assumed_type in (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0_OR_1):
                self.a.adjust(ASSUMED_1, level + 1, proof)
                return True

        else:
            raise Exception("Unsupported multiplication output type")

        return False

    @property
    def assumed_type(self):
        if ASSUMED_0 in (self.a.assumed_type, self.b.assumed_type):
            return ASSUMED_0
        if self.a.assumed_type == ASSUMED_1:
            return self.b.assumed_type
        if self.b.assumed_type == ASSUMED_1:
            return self.a.assumed_type
        if ASSUMED_CLOSED_INTERVAL_0_TO_1 in (self.a.assumed_type, self.b.assumed_type):
            return ASSUMED_CLOSED_INTERVAL_0_TO_1
        if self.a.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and self.b.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
            return ASSUMED_OPEN_INTERVAL_0_TO_1
        if self.a.assumed_type == ASSUMED_0_OR_1 and self.b.assumed_type == ASSUMED_0_OR_1:
            return ASSUMED_0_OR_1
        # only remaining case is {0,1} * (0,1), which can be anything in [0,1), we abuse [0,1] for it
        return ASSUMED_CLOSED_INTERVAL_0_TO_1

    def __str__(self):
        return self.name + " " + assumed_type_str(self.assumed_type)


class PolynomialProductAssumptions:

    def __init__(self, deg_p, deg_q):
        self.deg_A = deg_p
        self.deg_B = deg_q
        self.deg_C = deg_p + deg_q
        self.assumed_a = []
        self.assumed_b = []
        for i in range(self.deg_A + 1 + 1):
            self.assumed_a.append(RawAssumption(ASSUMED_CLOSED_INTERVAL_0_TO_1, f"a_{i}"))
        for i in range(self.deg_B + 1 + 1):
            self.assumed_b.append(RawAssumption(ASSUMED_CLOSED_INTERVAL_0_TO_1, f"b_{i}"))
        init_proof = Proof()
        # monic polynomials
        self.assumed_a[self.deg_A].adjust(ASSUMED_1, 2, init_proof)
        self.assumed_b[self.deg_B].adjust(ASSUMED_1, 2, init_proof)
        # we can safely assume that constant coefficients are 1
        self.assumed_a[0].adjust(ASSUMED_1, 2, init_proof)
        self.assumed_b[0].adjust(ASSUMED_1, 2, init_proof)
        init_proof.print()
        self.additional_assumptions = []

    def __str__(self):
        # print all the non-trivial assumptions
        res = ""
        for i in range(1, self.deg_A):
            if self.assumed_a[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"{self.assumed_a[i]}, "
        for i in range(1, self.deg_B):
            if self.assumed_b[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"{self.assumed_b[i]}, "
        return res


def apply_rules(assumptions, level, proof, recursive=True):
    changed = False
    # additional assumptions need to be kept in side assumptions, so that deepcopy will correctly
    # link all references in temporary instances
    assumptions.additional_assumptions = []
    for k in range(assumptions.deg_C + 1):
        open_idxs = []
        closed_idxs = []
        ones_idxs = []
        zeroes_idxs = []
        zero_or_one_idxs = []
        for i in range(max(0, k - assumptions.deg_B), min(assumptions.deg_A, k) + 1):
            # a_i * b_j
            j = k - i
            ab_assumption = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
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

        if len(closed_idxs) == 1 and len(open_idxs) == 0 and len(ones_idxs) ==0 and len(zero_or_one_idxs)==0:
            # exactly one term, it must be in {0,1}
            i = closed_idxs[0]
            j = k - i
            proof.report(level,
                         f"At coeff [x^{k}](R(x)), term a_{i}*b_{j} in [0,1] is the only non-zero term "
                         f"=> a_{i}*b_{j} in {{0,1}}")
            product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
            if product.adjust(ASSUMED_0_OR_1, level + 1, proof):
                changed = True

        if len(open_idxs) == 1:
            if len(zero_or_one_idxs) > 0:
                # all of these muse be zero
                for i in zero_or_one_idxs:
                    j = k - i
                    product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
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
                product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
                if product.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1, proof):
                    changed = True
            else:
                # one of other summands must be in (0,1)
                summands = []
                for i in closed_idxs:
                    j = k - i
                    summands.append(MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j]))
                assumptions.additional_assumptions.append((summands, ASSUMED_OPEN_INTERVAL_0_TO_1))

        if len(ones_idxs) > 1:
            i1 = ones_idxs[0]
            j1 = k - i1
            i2 = ones_idxs[1]
            j2 = k - i2
            proof.report(level, f"Coeff [x^{k}](R(x)) >= a_{i1}*b_{j1} + a_{i2}*b_{j2} >= 1 + 1 => contradiction")
            raise Contradiction()

        if len(ones_idxs) == 1:
            # there is 1 in summands, all other terms must be 0
            min_i = max(0, k - assumptions.deg_B)
            max_i = min(assumptions.deg_A, k)
            if max_i - min_i > 0:
                tmp_proof = Proof()
                tmp_proof.report(level, f"Coeff [x^{k}](R(x)) = 1 + ... => all other terms must equal 0")
                tmp_changed = False
                try:
                    for i in range(min_i, max_i + 1):
                        if i != ones_idxs[0]:
                            # a_i * b_j
                            j = k - i
                            product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
                            if product.adjust(ASSUMED_0, level + 1, proof=tmp_proof):
                                tmp_changed = True
                            else:
                                if assumptions.assumed_a[i].assumed_type != ASSUMED_0 \
                                        and assumptions.assumed_b[j].assumed_type != ASSUMED_0:
                                    assumptions.additional_assumptions.append(
                                        ((assumptions.assumed_a[i], assumptions.assumed_b[j]), ASSUMED_0))
                except Contradiction:
                    proof.append(tmp_proof)
                    raise

                if tmp_changed:
                    proof.append(tmp_proof)
                    changed = True

    if not changed and recursive:
        # try if additional assumptions fall through
        for idx_assumptions, (assumed_list, assumed) in enumerate(assumptions.additional_assumptions):
            # at least one of the items in assumed list must be as said "assumed", try them one by one
            viable = []
            msg = ""
            for idx, assumption in enumerate(assumed_list):
                msg += assumption.name + " "
                msg += assumed_type_str(assumed)
                if idx != len(assumed_list) - 1:
                    msg += " or "
            assumption_proof = Proof()
            assumption_proof.report(level, msg)
            for idx, assumption in enumerate(assumed_list):
                tmp_assumptions = deepcopy(assumptions)
                tmp_proof = Proof()
                try:
                    # since this is a copy, we need to link to its objects!
                    assumption_copy = tmp_assumptions.additional_assumptions[idx_assumptions][0][idx]
                    tmp_proof.report(level, f"Assuming {assumption_copy.name} {assumed_type_str(assumed)}")
                    assumption_copy.adjust(assumed, level + 1, tmp_proof)
                    while apply_rules(tmp_assumptions, recursive=False, level=level + 1, proof=tmp_proof):
                        pass
                    #proof += report(level + 1, f"No contradiction")
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
                assumption_proof.report(level, f"Exactly one possibility yields no contradiction => "
                              f"{assumed_list[viable[0]].name} {assumed_type_str(assumed)}")
                assumed_list[viable[0]].adjust(assumed, level, assumption_proof)
                proof.append(assumption_proof)

    if not changed:
        # We still have not found a contradiction, try to find one of a from
        # 1 = [x^k]R(x) = a*b + c*d < a+b+.... = [x^l]R(x) = 1
        # with a,b,c,d in (0,1)
        check_inequalities(assumptions, proof)

    return changed

def check_remaining_coeffs(assumptions, i, proof):
    for j in range(i+1, assumptions.deg_A):
        can_be_open = False
        can_be_zero = False
        can_be_one = False

        proof1 = Proof()
        proof2 = Proof()
        try:
            tmp_assumptions2 = deepcopy(assumptions)
            proof1.report(3, f"Assuming a_{j} in (0,1)")
            tmp_assumptions2.assumed_a[j].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, 3, proof1)
            while apply_rules(tmp_assumptions2, level=3, proof=proof1):
                pass
            can_be_open = True
        except Contradiction:
            pass

        try:
            tmp_assumptions2 = deepcopy(assumptions)
            proof2.report(3, f"Assuming a_{j} = 0")
            tmp_assumptions2.assumed_a[j].adjust(ASSUMED_0, 3, proof2)
            while apply_rules(tmp_assumptions2, level=3, proof=proof2):
                pass
            can_be_zero = True
        except Contradiction:
            pass

        try:
            tmp_assumptions2 = deepcopy(assumptions)
            proof2.report(3, f"Assuming a_{j} = 1")
            tmp_assumptions2.assumed_a[j].adjust(ASSUMED_1, 3, proof2)
            while apply_rules(tmp_assumptions2, level=3, proof=proof2):
                pass
            can_be_one = True
        except Contradiction:
            pass

        if not can_be_open and not can_be_zero and not can_be_one:
            proof.append(proof1)
            proof.append(proof2)
            proof.report(3, f"Coefficient a_{j} cannot be in neither (0,1) nor {{0,1}} => contradiction")
            raise Contradiction
        elif can_be_open and not can_be_zero and not can_be_one:
            proof.append(proof2)
            proof.report(3, f"Coefficient a_{j} cannot be in {{0,1}} =>")
            assumptions.assumed_a[j].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, 3, proof)
        elif not can_be_open and can_be_zero and not can_be_one:
            proof.append(proof1)
            proof.report(3, f"Coefficient a_{j} cannot be in (0,1) nor 1 =>")
            assumptions.assumed_a[j].adjust(ASSUMED_0, 3, proof)
        elif not can_be_open and not can_be_zero and can_be_one:
            proof.append(proof1)
            proof.report(3, f"Coefficient a_{j} cannot be in (0,1) nor 0 =>")
            assumptions.assumed_a[j].adjust(ASSUMED_1, 3, proof)
        elif not can_be_open and can_be_zero and can_be_one:
            proof.append(proof1)
            proof.report(3, f"Coefficient a_{j} cannot be in (0,1) =>")
            assumptions.assumed_a[j].adjust(ASSUMED_0_OR_1, 3, proof)
        else:
            pass

    for j in range(i+1, assumptions.deg_B):
        can_be_open = False
        can_be_zero_one = False

        proof1 = Proof()
        proof2 = Proof()
        try:
            tmp_assumptions2 = deepcopy(assumptions)
            proof1.report(3, f"Assuming b_{j} in (0,1)")
            tmp_assumptions2.assumed_b[j].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, 3, proof1)
            while apply_rules(tmp_assumptions2, level=3, proof=proof1):
                pass
            can_be_open = True
        except Contradiction:
            pass

        try:
            tmp_assumptions2 = deepcopy(assumptions)
            proof2.report(3, f"Assuming b_{j} in {{0, 1}}")
            tmp_assumptions2.assumed_b[j].adjust(ASSUMED_0_OR_1, 3, proof2)
            while apply_rules(tmp_assumptions2, level=3, proof=proof2):
                pass
            can_be_zero_one = True
        except Contradiction:
            pass

        if not can_be_open and not can_be_zero_one:
            proof.append(proof1)
            proof.append(proof2)
            proof.report(3, f"Coefficient b_{j} cannot be in neither (0,1) nor {{0,1}} => contradiction")
            raise Contradiction
        elif can_be_open and not can_be_zero_one:
            proof.append(proof2)
            proof.report(3, f"Coefficient b_{j} cannot be in {{0,1}} =>")
            assumptions.assumed_b[j].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, 3, proof)
        elif not can_be_open and can_be_zero_one:
            proof.append(proof1)
            proof.report(3, f"Coefficient b_{j} cannot be in (0,1) =>")
            assumptions.assumed_b[j].adjust(ASSUMED_0_OR_1, 3, proof)
        else:
            pass


def check_01_coeffs(assumptions, proof):
    changed = False
    for j in range(1, assumptions.deg_A):
        if assumptions.assumed_a[j].assumed_type == ASSUMED_0_OR_1:
            can_be_one = False
            can_be_zero = False

            proof1 = Proof()
            proof2 = Proof()
            try:
                tmp_assumptions2 = deepcopy(assumptions)
                proof1.report(3, f"Assuming a_{j} = 0")
                tmp_assumptions2.assumed_a[j].adjust(ASSUMED_0, 3, proof1)
                while apply_rules(tmp_assumptions2, level=3, proof=proof1):
                    pass
                can_be_zero = True
            except Contradiction:
                pass

            try:
                tmp_assumptions2 = deepcopy(assumptions)
                proof2.report(3, f"Assuming_a_{j} = 1")
                tmp_assumptions2.assumed_a[j].adjust(ASSUMED_1, 3, proof2)
                while apply_rules(tmp_assumptions2, level=3, proof=proof2):
                    pass
                can_be_one = True
            except Contradiction:
                pass

            if not can_be_one and not can_be_zero:
                proof.append(proof1)
                proof.append(proof2)
                proof.report(3, f"Coefficient a_{j} in {{0,1}} cannot be in neither 0 nor 1 => contradiction")
                raise Contradiction
            elif can_be_one and not can_be_zero:
                proof.append(proof2)
                proof.report(3, f"oefficient a_{j} in {{0,1}} cannot be 0 =>")
                if assumptions.assumed_a[j].adjust(ASSUMED_1, 3, proof):
                    changed = True
            elif not can_be_one and can_be_zero:
                proof.append(proof1)
                proof.report(3, f"Coefficient a_{j} in {{0,1}} cannot be 1 =>")
                if assumptions.assumed_a[j].adjust(ASSUMED_0, 3, proof):
                    changed = True
            else:
                pass

    for j in range(1, assumptions.deg_B):
        if assumptions.assumed_b[j].assumed_type == ASSUMED_0_OR_1:
            can_be_one = False
            can_be_zero = False

            proof1 = Proof()
            proof2 = Proof()
            try:
                tmp_assumptions2 = deepcopy(assumptions)
                proof1.report(3, f"Assuming b_{j} = 0")
                tmp_assumptions2.assumed_b[j].adjust(ASSUMED_0, 3, proof1)
                while apply_rules(tmp_assumptions2, level=3, proof=proof1):
                    pass
                can_be_zero = True
            except Contradiction:
                pass

            try:
                tmp_assumptions2 = deepcopy(assumptions)
                proof2.report(3, f"Assuming b_{j} = 1")
                tmp_assumptions2.assumed_b[j].adjust(ASSUMED_1, 3, proof2)
                while apply_rules(tmp_assumptions2, level=3, proof=proof2):
                    pass
                can_be_one = True
            except Contradiction:
                pass

            if not can_be_one and not can_be_zero:
                proof.append(proof1)
                proof.append(proof2)
                proof.report(3, f"Coefficient b_{j} in {{0,1}} cannot be in neither 0 nor 1 => contradiction")
                raise Contradiction
            elif can_be_one and not can_be_zero:
                proof.append(proof2)
                proof.report(3, f"Coefficient b_{j} in {{0,1}} cannot be 0 =>")
                if assumptions.assumed_b[j].adjust(ASSUMED_1, 3, proof):
                    changed = True
            elif not can_be_one and can_be_zero:
                proof.append(proof1)
                proof.report(3, f"Coefficient b_{j} in {{0,1}} cannot be 1 =>")
                if assumptions.assumed_b[j].adjust(ASSUMED_0, 3, proof):
                    changed = True
            else:
                pass

    return changed

def check_inequalities(assumptions, proof):
    lone_idxs = {} # list of R(x) coeffs' lone terms, such as a_1+b_3
    two_pairs_idxs = {} # list of R(x) coeffs that have exactly two terms in form a*b+c*d all from (0,1)
    for k in range(assumptions.deg_C + 1):
        lone_idxs[k] = []
        pairs = []
        non_zero = 0
        for i in range(max(0, k - assumptions.deg_B), min(assumptions.deg_A, k) + 1):
            # a_i * b_j
            j = k - i
            if assumptions.assumed_a[i].assumed_type == ASSUMED_1 and \
                    assumptions.assumed_b[j].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                lone_idxs[k].append(('b',j))
            elif assumptions.assumed_a[i].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and \
                    assumptions.assumed_b[j].assumed_type == ASSUMED_1:
                lone_idxs[k].append(('a',i))
            elif assumptions.assumed_a[i].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and \
                    assumptions.assumed_b[j].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                pairs.append((i,j))

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
            if ('a',a) in idxs and ('a',c) in idxs:
                proof.report(3, f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < a_{a}+a_{c} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()
            elif ('a',a) in idxs and ('b',d) in idxs:
                proof.report(3, f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < a_{a}+b_{d} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()
            elif ('b',b) in idxs and ('a',c) in idxs:
                proof.report(3, f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < b_{b}+a_{c} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()
            elif ('b',b) in idxs and ('b',d) in idxs:
                proof.report(3, f"1=[x^{k}]R(x) = a_{a}b_{b}+a_{c}b_{d} < b_{b}+b_{d} + ... = [x^{k2}]R(x) = 1 => contradiction")
                raise Contradiction()


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
        while apply_rules(assumptions, recursive=False, level=2, proof=contradiction_proof):
            pass
    except Contradiction:
        contradiction_proof.print()
        return True

    contradiction_proof.print()

    for i in range(1, a//2 + 1):
        # assume a_i in (0,1) for each i is the smallest with this property (hence smaller coefficients in {0,1}
        # and try to reach contradiction for EACH ONE
        tmp_proof = Proof()
        try:
            tmp_assumptions = deepcopy(assumptions)
            tmp_proof.report(2, f"Assuming {i} is the smallest with a_{i} in (0,1)")
            tmp_assumptions.assumed_a[i].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, 3, tmp_proof)

            changed = True
            while changed:
                changed = False

                while apply_rules(tmp_assumptions, level=3, proof=tmp_proof):
                    pass

                  # Failed to find contradiction, try separate (0,1) vs {0,1} cases for the other coefficients
                check_remaining_coeffs(tmp_assumptions, i, proof=tmp_proof)

                while apply_rules(tmp_assumptions, level=3, proof=tmp_proof):
                    pass

                # still no contradiction... iterate over a_i/b_i which must be in {0,1} and
                # check where the both possibilities lead to
                if check_01_coeffs(tmp_assumptions, proof=tmp_proof):
                   changed = True

            print(f" Failed to find contradiction for n={n},a={a},b={b} when assuming"
                  f" a_{i} in (0,1) is smallest with this property")
            print("", tmp_assumptions)
            return False  # comment this to see all fails for given degree
        except Contradiction:
            pass

        if i != a//2:
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
            break  # comment this to see all fails for given degree
    return result


if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='Find polynomials 0,1 factors contradiction.')
    parser.add_argument('--min', type=int, help='minimal degree of R(x)')
    parser.add_argument('--max', type=int, help='maximal degree of R(x)')
    parser.add_argument('-v', '--verbose', action='store_true', default=False, help='detailed report')
    args = parser.parse_args()

    min_n = args.min
    max_n = args.max
    report_enabled = args.verbose

    for n in range(min_n, max_n + 1):
        print(f"Checking deg R={n}")
        if not check_degree(n):
            print("Counterexample not ruled out for n =", n)
        #print()
        #report(0, "")
