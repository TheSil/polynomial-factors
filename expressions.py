from contradiction import Contradiction


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

class AssumedExpression:
    pass

class Variable(AssumedExpression):
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


class Multiplication(AssumedExpression):

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

