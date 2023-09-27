"""
Run from parent directory with
$ python -m tests.tests
"""
import os
import unittest as ut
from src.proof import substitute, verify_all
# from src.parse import parse as parse, Database
from src.database import parse as read

class TestSubstitute(ut.TestCase):

    def test_empty_sub(self):
        symbols = ("a", "b", "c")
        substitution = {}
        expected_result = ("a", "b", "c")
        actual_result = substitute(symbols, substitution)
        self.assertEqual(expected_result, actual_result)

    def test_complex_sub(self):
        symbols = ("a", "b", "c")
        substitution = {"a" : ('B -> C',), "c" : ('C -> D',)}
        expected_result = ("B -> C", "b", "C -> D")
        actual_result = substitute(symbols, substitution)
        self.assertEqual(expected_result, actual_result)

    def test_singleton_sub(self):
        symbols = ("a", "b", "c")
        substitution = {"a" : ('b',)}
        expected_result = ("b", "b", "c")
        actual_result = substitute(symbols, substitution)
        self.assertEqual(expected_result, actual_result)

# class TestParse(ut.TestCase):

#     def test_good_parse(self):
#         fpath = os.path.join('tests', 'p2.mm')
#         db = parse(fpath)
#         self.assertEqual(len(db.statements), 21)

#     def test_bad_parse(self):
#         fpath = os.path.join('tests', 'badparse.mm')
#         db = parse(fpath)
#         self.assertEqual(len(db.statements), 0)

#     def test_medium_parse(self):
#         fpath = os.path.join('tests', 'test.mm')
#         db = parse(fpath)
#         self.assertEqual(len(db.statements), 18)

#     def test_good_parse_rules(self):
#         fpath = os.path.join('tests', 'p2.mm')
#         db = parse(fpath)
#         self.assertEqual(len(db.rules), 10)

#     def test_bad_parse_rules(self):
#         fpath = os.path.join('tests', 'badparse.mm')
#         db = parse(fpath)
#         self.assertEqual(len(db.rules), 0)

#     def test_medium_parse_rules(self):
#         fpath = os.path.join('tests', 'test.mm')
#         db = parse(fpath)
#         self.assertEqual(len(db.rules), 9)

class TestVerify(ut.TestCase):
    def test_good_parse(self):
        fpath = os.path.join('tests', 'p2.mm')
        db = read(fpath)
        verify_all(db)

    def test_bad_parse(self):
        fpath = os.path.join('tests', 'badparse.mm')
        db = read(fpath)
        verify_all(db)

class TestDatabase(ut.TestCase):
    ## Bit confused on the Database version of parse, it always gives the same value for the rule parameter as statement however the Parse version gives seemingly a more accurate value
    def test_good_parse(self):
        fpath = os.path.join('tests', 'p2.mm')
        db = read(fpath)
        self.assertEqual(len(db.rules), 21)

    def test_bad_parse(self):
        fpath = os.path.join('tests', 'badparse.mm')
        db = read(fpath)
        self.assertEqual(len(db.rules), 0)

    def test_medium_parse(self):
        fpath = os.path.join('tests', 'test.mm')
        db = read(fpath)
        self.assertEqual(len(db.rules), 18)

if __name__ == '__main__':
    ut.main()
