import unittest as ut
from proof import substitute

class TestSubstitute(ut.TestCase):

    def test_empty_sub(self):
        symbols = ("a", "b", "c")
        substitution = {}
        expected_result = ("a", "b", "c")
        actual_result = substitute(symbols, substitution)
        self.assertEqual(expected_result, actual_result)

    def test_noop_sub(self):
        pass

    def test_singleton_sub(self):
        pass

if __name__ == '__main__':
    ut.main()
