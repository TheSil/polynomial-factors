import unittest
from polynomial_factors import *

class DummyProof:
    def __init__(self):
        pass

    def report(self, level, msg):
        pass

class RawAssumptionsTestCase(unittest.TestCase):
    def test_adjust_returns_correct(self):
        proof = DummyProof()

        assumption = RawAssumption(ASSUMED_CLOSED_INTERVAL_0_TO_1, 'test')
        self.assertEqual(False, assumption.adjust(ASSUMED_CLOSED_INTERVAL_0_TO_1, 1, proof))
        self.assertEqual(True, assumption.adjust(ASSUMED_0_OR_1, 1, proof))
        self.assertEqual(True, assumption.adjust(ASSUMED_0, 1, proof))
        self.assertEqual(False, assumption.adjust(ASSUMED_0_OR_1, 1, proof))
        self.assertEqual(False, assumption.adjust(ASSUMED_CLOSED_INTERVAL_0_TO_1, 1, proof))

    def test_adjust_throws_correct(self):
        proof = DummyProof()

        assumption = RawAssumption(ASSUMED_0, 'test')
        with self.assertRaises(Contradiction):
            assumption.adjust(ASSUMED_1, 1, proof)


    def test_adjust_name_correct(self):
        assumption = RawAssumption(ASSUMED_0, 'test')
        self.assertEqual("test", assumption.name)
        self.assertEqual("test = 0", str(assumption))

    def test_assumed_type_correct(self):
        assumption = RawAssumption(ASSUMED_0, 'test')
        self.assertEqual(ASSUMED_0, assumption.assumed_type)
        assumption = RawAssumption(ASSUMED_1, 'test')
        self.assertEqual(ASSUMED_1, assumption.assumed_type)

class MultipliedAssumptionsTestCase(unittest.TestCase):
    def test_assumed_type_correct(self):
        proof = DummyProof()

        test_combs = [
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1 ),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0, ASSUMED_0),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_1, ASSUMED_CLOSED_INTERVAL_0_TO_1),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1),

            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_OPEN_INTERVAL_0_TO_1),
            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_0, ASSUMED_0),
            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1, ASSUMED_OPEN_INTERVAL_0_TO_1),
            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_0_OR_1, ASSUMED_CLOSED_INTERVAL_0_TO_1),

            (ASSUMED_0, ASSUMED_0, ASSUMED_0),
            (ASSUMED_0, ASSUMED_1, ASSUMED_0),
            (ASSUMED_0, ASSUMED_0_OR_1, ASSUMED_0),

            (ASSUMED_1, ASSUMED_1, ASSUMED_1),
            (ASSUMED_1, ASSUMED_0_OR_1, ASSUMED_0_OR_1),

            (ASSUMED_0_OR_1, ASSUMED_0_OR_1, ASSUMED_0_OR_1),
        ]

        for type1, type2, result in test_combs:
            assumption1 = RawAssumption(type1, 'test1')
            assumption2 = RawAssumption(type2, 'test2')
            product1 = MultipliedAssumptions2(assumption1, assumption2)
            self.assertEqual(result, product1.assumed_type)
            # should be commutative
            product2 = MultipliedAssumptions2(assumption2, assumption1)
            self.assertEqual(result, product2.assumed_type)

    def test_adjust_correct(self):
        proof = DummyProof()

        test_combs = [
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_CLOSED_INTERVAL_0_TO_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, False, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ]),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_OPEN_INTERVAL_0_TO_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_0, True, ASSUMED_0, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, True, ASSUMED_0, -1)
                ], ),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, True, ASSUMED_OPEN_INTERVAL_0_TO_1, -1),
                    (ASSUMED_0, True, ASSUMED_0, -1),
                    (ASSUMED_1, True, ASSUMED_1, -1),
                    (ASSUMED_0_OR_1, True, ASSUMED_0_OR_1, -1)
                ], ),
            (ASSUMED_CLOSED_INTERVAL_0_TO_1, ASSUMED_0_OR_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, True, ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, False, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),

            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_OPEN_INTERVAL_0_TO_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_0, Contradiction, -1, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, Contradiction, -1, -1)
                ], ),
            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_0,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),
            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_0, Contradiction, -1, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, Contradiction, -1, -1)
                ], ),
            (ASSUMED_OPEN_INTERVAL_0_TO_1, ASSUMED_0_OR_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, True, -1, ASSUMED_1),
                    (ASSUMED_0, True, -1, ASSUMED_0),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, True, -1, ASSUMED_0)
                ], ),

            (ASSUMED_0, ASSUMED_0,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),
            (ASSUMED_0, ASSUMED_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),
            (ASSUMED_0, ASSUMED_0_OR_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, Contradiction, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),

            (ASSUMED_1, ASSUMED_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, Contradiction, -1, -1),
                    (ASSUMED_1, False, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),

            (ASSUMED_1, ASSUMED_0_OR_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, True, -1, ASSUMED_0),
                    (ASSUMED_1, True, -1, ASSUMED_1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),

            (ASSUMED_0_OR_1, ASSUMED_0_OR_1,
                [
                    (ASSUMED_CLOSED_INTERVAL_0_TO_1, False, -1, -1),
                    (ASSUMED_OPEN_INTERVAL_0_TO_1, Contradiction, -1, -1),
                    (ASSUMED_0, False, -1, -1),
                    (ASSUMED_1, False, -1, -1),
                    (ASSUMED_0_OR_1, False, -1, -1)
                ], ),
        ]

        for type1_base, type2_base, test_vectors in test_combs:
            for new_product_type, result, op1_base, op2_base in test_vectors:
                for (type1, type2, op1, op2) in ((type1_base, type2_base, op1_base, op2_base ),
                                                 (type2_base, type1_base, op2_base, op1_base)):
                    assumption1 = RawAssumption(type1, 'test1')
                    assumption2 = RawAssumption(type2, 'test2')
                    product = MultipliedAssumptions2(assumption1, assumption2)
                    if result is Contradiction:
                        with self.assertRaises(Contradiction):
                            product.adjust(new_product_type, 1, proof)
                    else:
                        ret = product.adjust(new_product_type, 1, proof)
                        self.assertEqual(result, ret)
                        if op1 != -1:
                            self.assertEqual(op1, assumption1.assumed_type)
                        if op2 != -1:
                            self.assertEqual(op2, assumption2.assumed_type)








if __name__ == '__main__':
    unittest.main()
