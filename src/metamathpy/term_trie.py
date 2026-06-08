"""
Trie-like implementation of cterm set indexing structure
"""
try:
    profile
except NameError:
    profile = lambda x: x

import src.metamathpy.database as md
import src.metamathpy.proof as mp

class TermTrieNode:
    # self.tokens
    # self.variables

    def __init__(self, result=None):
        self.result = result
        self.token_children = {}

    def __str__(self, prefix=""):
        s = [f"{prefix}<{self.result}>"]
        for tok, child in self.token_children.items():
            s.append(f"{prefix} [{tok}] {child.__str__(prefix+' ')}")
        return "\n".join(s)        

    def incorporate(self, term, result):

        if len(term) == 0:
            assert self.result is None
            self.result = result
            return

        tok, length = term[0]
        if tok not in self.token_children:
            self.token_children[tok] = TermTrieNode()
        self.token_children[tok].incorporate(term[1:], result)

    def instantiate(self, term):
        """
        find substitution of a term indexed in self that instantiate provided term
        "one-way" version of unification
        for example, term = substitution of a rule statement indexed in self
        fails if the term is not an instance of the token sequence
        returns substitution and index data at self's corresponding leaf, or None if failure
        """
        # i, s = 0, {}
        # for tok in tokens:
        #     if tok in variables:
        #         s[tok] = term[i:i+term[i][1]]
        #         i += term[i][1]
        #     else:
        #         if self.encode(tok) != term[i][0]: return None
        #         i += 1
        # return s
        return None, None

if __name__ == "__main__":    

    import src.metamathpy.cterms as mt
    import src.metamathpy.setmm as ms

    db = ms.load_pl()
    rules = db.rules_up_to("mp2")
    tm = mt.TermManager([rule for rule in rules["wff"] if rule.consequent.tag == "$a"])
    t1 = tm.parse("( ph -> ps )".split(), ["ph","ps"])

    trie = TermTrieNode()
    print(trie)
    trie.incorporate([[0,2],[10,1]], "done")
    print(trie)

    # s, _ = ct_index.instantiate(t1)
    # print(s)
