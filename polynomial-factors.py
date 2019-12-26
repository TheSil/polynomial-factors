from copy import copy, deepcopy

class Contradiction(Exception):
    def __init__(self):
        pass

ASSUMED_CLOSED_INTERVAL_0_TO_1 = 1
ASSUMED_OPEN_INTERVAL_0_TO_1 = 2
ASSUMED_0 = 3
ASSUMED_1 = 4
ASSUMED_0_OR_1 = 5

report_enabled = True


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

def assumption_str(assumption):
    return assumption.name + " " + assumed_type_str(assumption.assumed_type)

def report(level, msg):
    global report_enabled
    if report_enabled:
        print(level * " " + msg)

class Assumption:
    pass

class RawAssumption(Assumption):
    def __init__(self, assumed_type, name):
        self.assumed_type = assumed_type
        self.name = name

    def adjust(self, new_assumed_type, level=0):
        if self.assumed_type == new_assumed_type:
            return False

        if self.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
            self.assumed_type = new_assumed_type
            report(level, f"Then {self.name} {assumed_type_str(new_assumed_type)}")
            return True

        if new_assumed_type == ASSUMED_0_OR_1:
            if self.assumed_type in (ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                report(level, f"Then {self.name} {assumed_type_str(new_assumed_type)}")
                return True
            report(level, f"Since {assumption_str(self)} = > contradiction")
            raise Contradiction()

        if new_assumed_type == ASSUMED_0:
            if self.assumed_type in (ASSUMED_0, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                report(level, f"Then {self.name} {assumed_type_str(new_assumed_type)}")
                return True
            report(level, f"Since {assumption_str(self)} = > contradiction")
            raise Contradiction()

        if new_assumed_type == ASSUMED_1:
            if self.assumed_type in (ASSUMED_1, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                report(level, f"Then {self.name} {assumed_type_str(new_assumed_type)}")
                return True
            report(level, f"Since {assumption_str(self)} = > contradiction")
            raise Contradiction()

        if new_assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
            if self.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                report(level, f"Then {self.name} {assumed_type_str(new_assumed_type)}")
                return True
            report(level, f"Since {assumption_str(self)} = > contradiction")
            raise Contradiction()

        raise Exception("Unknown new assumption type")


class MultipliedAssumptions2(Assumption):

    def __init__(self, a, b):
        self.a = a
        self.b = b
        self.name = f"{a.name}*{b.name}"

    def adjust(self, product, level):
        # this function propagates product assumption into multiplicands if possible
        # e.g. 1*a in (0,1) implies that a in (0,1)
        if product == ASSUMED_OPEN_INTERVAL_0_TO_1:
            if (self.a.assumed_type == ASSUMED_1):
                # 1*b in (0,1) implies that b in (0,1)
                report(level, f"{self.name} in (0,1), but {assumption_str(self.a)} and {assumption_str(self.b)} =>")
                return self.b.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1)
            elif (self.b.assumed_type == ASSUMED_1):
                # a*1 in (0,1) implies that a in (0,1)
                report(level, f"{self.name} in (0,1), but {assumption_str(self.a)} and {assumption_str(self.b)} =>")
                return self.a.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1)
            elif self.a.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1) \
                    and self.b.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                # {0,1} * (0,1) in (0,1) implies first coefficient must be 1
                report(level, f"{self.name} in (0,1), but {assumption_str(self.a)} and {assumption_str(self.b)} =>")
                return self.a.adjust(ASSUMED_1, level + 1)
            elif self.a.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 \
                    and self.b.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1):
                # (0,1) * {0,1} in (0,1) implies second coefficient must be 1
                report(level, f"{self.name} in (0,1), but {assumption_str(self.a)} and {assumption_str(self.b)} =>")
                return self.b.adjust(ASSUMED_1, level + 1)
            if self.a.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1) \
                    and self.b.assumed_type == (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1):
                # a in {0,1} * b in {0,1} cannot give c in (0,1)
                report(level, f"{self.name} in (0,1), but {assumption_str(self.a)} and {assumption_str(self.b)} => contradiction")
                raise Contradiction()

        elif product == ASSUMED_0:
            # one of multiplicands must be 0, couple contradictions here
            if self.a.assumed_type == ASSUMED_0 \
                    or self.b.assumed_type == ASSUMED_0:
                return False

            if self.a.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1) \
                    and self.b.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                report(level, f"{self.name} = 0, but {assumption_str(self.a)} and {assumption_str(self.b)} => contradiction")
                raise Contradiction()

            if self.a.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                report(level, f"{self.name} = 0, but {assumption_str(self.a)} and {assumption_str(self.b)} =>")
                self.b.adjust(ASSUMED_0, level + 1)

            if self.b.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                report(level, f"{self.name} = 0, but {assumption_str(self.a)} and {assumption_str(self.b)} =>")
                self.a.adjust(ASSUMED_0, level + 1)

        return False
        # TODO: remaining product types

    @property
    def assumed_type(self):
        if self.a.assumed_type == ASSUMED_0 or self.b.assumed_type == ASSUMED_0:
            return ASSUMED_0
        if self.a.assumed_type == ASSUMED_1: return self.b.assumed_type
        if self.b.assumed_type == ASSUMED_1: return self.a.assumed_type
        if self.a.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1: return self.b.assumed_type
        if self.b.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1: return self.a.assumed_type
        if self.a.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1 and self.b.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
            return ASSUMED_OPEN_INTERVAL_0_TO_1
        if self.a.assumed_type == ASSUMED_0_OR_1 and self.b.assumed_type == ASSUMED_0_OR_1:
            return ASSUMED_0_OR_1
        # only remaining case is {0,1} * (0,1), which can be anything in [0,1), we abuse [0,1] for it
        return ASSUMED_CLOSED_INTERVAL_0_TO_1

class PolynomialProductAssumptions:

    def __init__(self, deg_A, deg_B):
        self.deg_A = deg_A
        self.deg_B = deg_B
        self.deg_C = deg_A+deg_B
        self.assumed_a = []
        self.assumed_b = []
        #self.assumed_c = []
        for i in range(self.deg_A + 1 + 1):
            self.assumed_a.append(RawAssumption(ASSUMED_CLOSED_INTERVAL_0_TO_1, f"a_{i}"))
        for i in range(self.deg_B + 1 + 1):
            self.assumed_b.append(RawAssumption(ASSUMED_CLOSED_INTERVAL_0_TO_1, f"b_{i}"))
        # for i in range(self.deg_C + 1 + 1):
        #     self.assumed_c.append(RawAssumption(ASSUMED_0_OR_1))
        # monic polynomials
        self.assumed_a[self.deg_A].adjust(ASSUMED_1, 2)
        self.assumed_b[self.deg_B].adjust(ASSUMED_1, 2)
        # self.assumed_c[self.deg_C] = RawAssumption(ASSUMED_1)
        # we can safely assume that constant coefficients are 1
        self.assumed_a[0].adjust(ASSUMED_1, 2)
        self.assumed_b[0].adjust(ASSUMED_1, 2)
        # self.assumed_c[0] = RawAssumption(ASSUMED_1)

    def __str__(self):
        # print all the non-trivial assumptions
        res = ""
        for i in range(1, self.deg_A):
            if self.assumed_a[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"a_{i} "
                res += assumed_type_str(self.assumed_a[i].assumed_type)
                res += ", "
        for i in range(1, self.deg_B):
            if self.assumed_b[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"b_{i} "
                res += assumed_type_str(self.assumed_b[i].assumed_type)
                res += ", "
        return res

def apply_rules(assumptions, recursive=True, level=1):
    #print(f"Applying rules to: {assumptions}")
    changed = False
    # additional assumptions need to be kept in side assumptions, so that deepcopy will correctly
    # link all references in temporary instances
    assumptions.additional_assumptions = []
    for k in range(assumptions.deg_C + 1):
        open = []
        closed = []
        ones = []
        zeroes = []
        zero_or_one = []
        for i in range(max(0, k - assumptions.deg_B), min(assumptions.deg_A, k) + 1):
            # a_i * b_j
            j= k-i
            ab_assumption = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
            if (ab_assumption.assumed_type == ASSUMED_0):
                zeroes.append(i)
            elif (ab_assumption.assumed_type == ASSUMED_1):
                ones.append(i)
            elif (ab_assumption.assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1):
                open.append(i)
            elif (ab_assumption.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1):
                closed.append(i)
            elif (ab_assumption.assumed_type == ASSUMED_0_OR_1):
                zero_or_one.append(zero_or_one)
            else:
                raise Exception("Unknown assumed type")

        if len(open) == 1:
            if len(closed) == 0:
                # exactly one of summands is in (0,1) and rest gives an integer together
                i = open[0]
                j = k - i
                report(level, f"Term a_{i}*b_{j} is the only non-integer coefficient at coeff [x^{k}](R(x)) => contradiction")
                raise Contradiction()
            elif len(closed) == 1:
                # exactly one of summands is in (0,1),  rest gives an integer together EXCEPT for one coefficient
                # then that coefficients must be in (0,1) too, which means both a_i and b_j in it must be (0,1) or 1
                i = closed[0]
                j = k - i
                i_open = open[0]
                j_open =  k - i_open
                report(level, f"At coeff [x^{k}](R(x)), term a_{i_open}*b_{j_open} in (0,1) and a_{i}*b_{j} in [0,1] is the only is the only possible non-integer coeff  => a_{i}*b_{j} in (0,1)")
                product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
                if product.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, level + 1):
                    changed = True
            else: # len(closed) > 1
                # one of other summands must be in (0,1)
                summands = []
                for i in closed:
                    j = k - i
                    summands.append(MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j]))
                assumptions.additional_assumptions.append((summands, ASSUMED_OPEN_INTERVAL_0_TO_1))

        if len(ones) > 1:
            i1 = ones[0]
            j1 = k - i1
            i2 = ones[1]
            j2 = k - i2
            report(level, f"Coeff [x^{k}](R(x)) >= a_{i1}*b_{j1} + a_{i2}*b_{j2} >= 1 + 1 => contradiction")
            raise Contradiction()

        if len(ones) == 1:
            # there is 1 in summands, all other terms must be 0
            min_i = max(0, k - assumptions.deg_B )
            max_i =  min(assumptions.deg_A, k)
            if max_i - min_i > 0:
                report(level, f"Coeff [x^{k}](R(x)) = 1 + ... => all other terms must equal 0")
                for i in range(min_i, max_i + 1):
                    if i != ones[0]:
                        # a_i * b_j
                        j = k - i
                        product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
                        if product.adjust(ASSUMED_0, level + 1):
                            changed = True
                        else:
                            if assumptions.assumed_a[i].assumed_type != ASSUMED_0 \
                              and assumptions.assumed_b[j].assumed_type != ASSUMED_0:
                                assumptions.additional_assumptions.append(((assumptions.assumed_a[i],assumptions.assumed_b[j]),ASSUMED_0))

    if not changed and recursive:
        # try if additional assumptions fall through
        for idx_assumptions, (assumed_list, assumed) in enumerate(assumptions.additional_assumptions):
            # at least one of the items in assumed list must be as said "assumed", try them one by one
            viable = []
            msg = ""
            for idx, assumption in enumerate(assumed_list):
                msg += assumption.name + " "
                msg += assumed_type_str(assumed)
                if idx != len(assumed_list) - 1 :
                    msg += " or "
            report(level, msg)
            for idx, assumption in enumerate(assumed_list):
                #if assumption.assumed_type not in (ASSUMED_1, ASSUMED_0):
                tmp_assumptions = deepcopy(assumptions)
                try:
                    # since this is a copy, we need to link to its objects!
                    report(level, f"Assuming {tmp_assumptions.additional_assumptions[idx_assumptions][0][idx].name} {assumed_type_str(assumed)}")
                    tmp_assumptions.additional_assumptions[idx_assumptions][0][idx].adjust(assumed, level+1)
                    while apply_rules(tmp_assumptions, recursive=False, level=level+1):
                        pass
                    report(level+1, f"No contradiction")
                    viable.append(idx)
                except Contradiction as e:
                    pass
            if len(viable) == 0:
                # not possible
                report(level, "All possibilities lead to contradiciton => contradiction")
                raise Contradiction()

            if len(viable) == 1:
                # that one must satisfy the assumption
                report(level, f"Exactly one possibility yields no contradiction => {assumed_list[viable[0]].name} {assumed_type_str(assumed)}")
                assumed_list[viable[0]].adjust(assumed, level)

    return changed


def check2(a, b):
    report(1, f"Assuming R(x)=P(x)Q(x) with deg P={a}, deg Q={b}")
    poly_str = ""
    for i in range(a+1):
        poly_str += f"a_{i}"
        if i != 0:
            poly_str += f"*x^{i}"
        if i != a:
            poly_str += "+"
    report(1, f"P(x)={poly_str}")
    poly_str = ""
    for i in range(b+1):
        poly_str += f"b_{i}"
        if i != 0:
            poly_str += f"*x^{i}"
        if i != b:
            poly_str += "+"
    report(1, f"Q(x)={poly_str}")
    assumptions = PolynomialProductAssumptions(a, b)

    try:
        while apply_rules(assumptions, recursive=False, level=2):
            pass
    except Contradiction as e:
        return True

    for i in range(1, a):
        # assume a_i in (0,1) for each i is the smallest with this property (hence smaller coefficients in {0,1}
        # and try to reach contradiction for EACH ONE
        try:
            tmp_assumptions = deepcopy(assumptions)
            report(2, f"Assuming a_{i} in (0,1)")
            tmp_assumptions.assumed_a[i].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1, 3)
            while apply_rules(tmp_assumptions, level=3):
                pass
            print(f" Failed to find contradiction for n={n},a={a},b={b} when assuming a_{i} in (0,1)")
            print("", tmp_assumptions)
            return False # uncomment this to see all fails for given degree
        except Contradiction as e:
            pass

        if i != a - 1:
            assumptions.assumed_a[i].adjust(ASSUMED_0_OR_1, 2)

    return True

def check(n):
    result = True
    for deg_a in range(2,n//2 + 1):
        deg_b = n - deg_a
        if not check2(deg_a, deg_b):
            result = False
            break # uncomment this to see all fails for given degree
    return result

for n in range(18, 18+1):
    print(f"Checking deg R={n}")
    if not check(n):
        print("Counterexample not ruled out for n =", n)
    report(0,"")








