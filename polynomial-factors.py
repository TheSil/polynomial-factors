from copy import copy, deepcopy

class Contradiction(Exception):
    pass

ASSUMED_CLOSED_INTERVAL_0_TO_1 = 1
ASSUMED_OPEN_INTERVAL_0_TO_1 = 2
ASSUMED_0 = 3
ASSUMED_1 = 4
ASSUMED_0_OR_1 = 5

class Assumption:
    pass

class RawAssumption(Assumption):
    def __init__(self, assumed_type):
        self.assumed_type = assumed_type

    def adjust(self, new_assumed_type):
        if self.assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
            self.assumed_type = new_assumed_type
            return

        if new_assumed_type == ASSUMED_CLOSED_INTERVAL_0_TO_1:
            raise Contradiction()

        if new_assumed_type == ASSUMED_0_OR_1:
            if self.assumed_type in (ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                return
            raise Contradiction()

        if new_assumed_type == ASSUMED_0:
            if self.assumed_type in (ASSUMED_0, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                return
            raise Contradiction()

        if new_assumed_type == ASSUMED_1:
            if self.assumed_type in (ASSUMED_1, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                return
            raise Contradiction()

        if new_assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
            if self.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1):
                self.assumed_type = new_assumed_type
                return
            raise Contradiction()

        raise Exception("Unknown new assumption type")

class MultipliedAssumptions2(Assumption):

    def __init__(self, a, b):
        self.a = a
        self.b = b

    def adjust(self, product):
        # this function propagates product assumption into multiplicands if possible
        # e.g. 1*a in (0,1) implies that a in (0,1)
        if product == ASSUMED_OPEN_INTERVAL_0_TO_1:
            if (self.a.assumed_type == ASSUMED_1):
                # 1*b in (0,1) implies that b in (0,1)
                return self.b.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1)
            elif (self.b.assumed_type == ASSUMED_1):
                # a*1 in (0,1) implies that a in (0,1)
                return self.a.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1)
            if self.a.assumed_type in (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1) \
                    or self.b.assumed_type == (ASSUMED_0, ASSUMED_1, ASSUMED_0_OR_1):
                # a in {0,1} * b in {0,1} cannot give c in (0,1)
                raise Contradiction()

        elif product == ASSUMED_0:
            # one of multiplicands must be 0, couple contradictions here
            if self.a.assumed_type == ASSUMED_0 \
                    or self.b.assumed_type == ASSUMED_0:
                return False

            if self.a.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1) \
                    and self.b.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                raise Contradiction()

            if self.a.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                self.b.adjust(ASSUMED_0)

            if self.b.assumed_type in (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1):
                self.a.adjust(ASSUMED_0)

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

class CoeffAssumptions:

    def __init__(self, deg_A, deg_B):
        self.deg_A = deg_A
        self.deg_B = deg_B
        self.deg_C = deg_A+deg_B
        self.assumed_a = []
        self.assumed_b = []
        #self.assumed_c = []
        for i in range(self.deg_A + 1 + 1):
            self.assumed_a.append(RawAssumption(ASSUMED_CLOSED_INTERVAL_0_TO_1))
        for i in range(self.deg_B + 1 + 1):
            self.assumed_b.append(RawAssumption(ASSUMED_CLOSED_INTERVAL_0_TO_1))
        # for i in range(self.deg_C + 1 + 1):
        #     self.assumed_c.append(RawAssumption(ASSUMED_0_OR_1))
        # monic polynomials
        self.assumed_a[self.deg_A] = RawAssumption(ASSUMED_1)
        self.assumed_b[self.deg_B] = RawAssumption(ASSUMED_1)
        # self.assumed_c[self.deg_C] = RawAssumption(ASSUMED_1)
        # we can safely assume that constant coefficients are 1
        self.assumed_a[0] = RawAssumption(ASSUMED_1)
        self.assumed_b[0] = RawAssumption(ASSUMED_1)
        # self.assumed_c[0] = RawAssumption(ASSUMED_1)

    def __str__(self):
        # print all the non-trivial assumptions
        res = ""
        for i in range(1, self.deg_A):
            if self.assumed_a[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"a_{i} "
                if self.assumed_a[i].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                    res += "in (0,1)"
                elif self.assumed_a[i].assumed_type == ASSUMED_0:
                    res += "= 0"
                elif self.assumed_a[i].assumed_type == ASSUMED_1:
                    res += "= 1"
                elif self.assumed_a[i].assumed_type == ASSUMED_0_OR_1:
                    res += "in {0,1}"
                res += ", "
        for i in range(1, self.deg_B):
            if self.assumed_b[i].assumed_type != ASSUMED_CLOSED_INTERVAL_0_TO_1:
                res += f"b_{i} "
                if self.assumed_b[i].assumed_type == ASSUMED_OPEN_INTERVAL_0_TO_1:
                    res += "in (0,1)"
                elif self.assumed_b[i].assumed_type == ASSUMED_0:
                    res += "= 0"
                elif self.assumed_b[i].assumed_type == ASSUMED_1:
                    res += "= 1"
                elif self.assumed_b[i].assumed_type == ASSUMED_0_OR_1:
                    res += "in {0,1}"
                res += ", "
        return res

def apply_rules(assumptions, recursive=True):
    #print(f"Applying rules to: {assumptions}")
    changed = False
    additional_assumptions = []
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
                raise Contradiction()

            # otherwise at least one of the other coefficients must be in (0,1)
            # TBD

        if len(open) == 1 and len(closed) == 1:
            # exactly one of summands is in (0,1),  rest gives an integer together EXCEPT for one coefficient
            # then that coefficients must be in (0,1) too, which means both a_i and b_j in it must be (0,1) or 1
            i = closed[0]
            j = k - i
            product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
            if product.adjust(ASSUMED_OPEN_INTERVAL_0_TO_1):
                changed = True

        if len(ones) > 1:
            raise Contradiction()

        if len(ones) == 1:
            # there is 1 in summands, all other terms must be 0
            for i in range(max(0, k - assumptions.deg_B ), min(assumptions.deg_A, k) + 1):
                if i != ones[0]:
                    # a_i * b_j
                    j = k - i
                    product = MultipliedAssumptions2(assumptions.assumed_a[i], assumptions.assumed_b[j])
                    if product.adjust(ASSUMED_0):
                        changed = True
                    else:
                        if assumptions.assumed_a[i].assumed_type != ASSUMED_0 \
                          and assumptions.assumed_b[j].assumed_type != ASSUMED_0:
                            additional_assumptions.append((i,j,k,ASSUMED_0))

    if not changed and recursive:
        # try if additional assumptions fall through
        for (i,j,k,assumed) in additional_assumptions:
            if assumed == ASSUMED_0:
                if assumptions.assumed_a[i].assumed_type not in (ASSUMED_1, ASSUMED_0):
                    tmp_assumptions = deepcopy(assumptions)
                    tmp_assumptions.assumed_a[i].adjust(ASSUMED_0)
                    #print(f"assuming a_{i}=0")
                    try:
                        while apply_rules(tmp_assumptions, recursive=False):
                            pass
                    except Contradiction as e:
                        # a_i cannot be 0, so b_j must be
                        assumptions.assumed_b[j].adjust(ASSUMED_0)
                        changed=True
                        break

                if assumptions.assumed_b[j].assumed_type not in (ASSUMED_1, ASSUMED_0):
                    tmp_assumptions = deepcopy(assumptions)
                    tmp_assumptions.assumed_b[j].adjust(ASSUMED_0)
                    #print(f"assuming b_{j}=0")
                    try:
                        while apply_rules(tmp_assumptions, recursive=False):
                            pass
                    except Contradiction as e:
                        # b_j cannot be 0, so a_i must be
                        assumptions.assumed_a[i].adjust(ASSUMED_0)
                        changed=True
                        break

    return changed


def check2(a, b):
    assumptions = CoeffAssumptions(a, b)

    try:
        while apply_rules(assumptions, recursive=False):
            pass
    except Contradiction as e:
        return True

    for i in range(1, a):
        # assume a_i in (0,1) for each i is the smallest with this property (hence smaller coefficients in {0,1}
        # and try to reach contradiction for EACH ONE
        try:
            tmp_assumptions = deepcopy(assumptions)
            tmp_assumptions.assumed_a[i].adjust(ASSUMED_OPEN_INTERVAL_0_TO_1)
            while apply_rules(tmp_assumptions):
                pass
            print(f"Failed to find contradiction for n={n},a={a},b={b} when assuming a_{i} in (0,1)")
            print(tmp_assumptions)
            #return False # uncomment this to see all fails for given degree
        except Contradiction as e:
            pass

        assumptions.assumed_a[i].adjust(ASSUMED_0_OR_1)

    return True

def check(n):
    result = True
    for deg_a in range(2,n//2 + 1):
        deg_b = n - deg_a
        if not check2(deg_a, deg_b):
            print(f"Failed to find contradiction for n={n},a={deg_a},b={deg_b}")
            result = False
            #break # uncomment this to see all fails for given degree
    return result

n = 5#5
while n < 20:
    print("Checking n =",n)
    if not check(n):
        print("Counterexample possible for n =",n)
    n += 1








