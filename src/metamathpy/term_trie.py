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

    def __init__(self, result=None):
        self.result = result
        self.branches = {}

    def __str__(self, prefix=""):
        s = [f"{prefix}<{self.result}>"]
        for (t, n), child in self.branches.items():
            s.append(f"{prefix} [{t},{n}] {child.__str__(prefix+' ')}")
        return "\n".join(s)        

    def incorporate(self, term, result):

        if len(term) == 0:
            assert self.result is None
            assert len(self.branches) == 0
            self.result = result
            return

        head = tuple(term[0])
        if head not in self.branches:
            self.branches[head] = TermTrieNode()
        self.branches[head].incorporate(term[1:], result)

    def look_ahead(self, n):
        if n == 0:
            yield self
        else:
            for child in self.branches.values():
                yield from child.look_ahead(n-1)

    def instantiate(self, variables, term):
        """
        find substitution of a term indexed in self that instantiate provided term
        "one-way" version of unification
        for example, term = substitution of a rule statement indexed in self
        fails if the term is not an instance of the token sequence
        returns substitution and index data at self's corresponding leaf, or None if failure
        """
        if len(term) == len(self.branches) == 0:
            return {}, self.result

        if (len(term) == 0) or (len(self.branches) == 0):
            return None, None
        
        for (tok, n), child in self.branches.items():
            if tok in variables:
                for descendent in child.look_ahead(n-1): # already took 1 step to get to child
                    sub, result = descendent.instantiate(variables, term[n:])
                    if sub is not None:
                        sub[tok] = term[:n]
                        return sub, result
                return None, None
            else:
                if tok != term[0][0]: return None, None
                return child.instantiate(variables, term[1:])
            
        # i, s = 0, {}
        # for tok in tokens:
        #     if tok in variables:
        #         s[tok] = term[i:i+term[i][1]]
        #         i += term[i][1]
        #     else:
        #         if self.encode(tok) != term[i][0]: return None
        #         i += 1
        # return s

if __name__ == "__main__":    

    import src.metamathpy.cterms as mt
    import src.metamathpy.setmm as ms

    db = ms.load_pl()
    rules = db.rules_up_to("mp2")
    tm = mt.TermManager([rule for rule in rules["wff"] if rule.consequent.tag == "$a"])
    t1 = tm.parse("( ph -> ps )".split(), ["ph","ps"])

    trie = TermTrieNode()
    print(trie)
    trie.incorporate([[0,2],[1,1]], "one")
    trie.incorporate([[0,2],[10,1]], "done")
    trie.incorporate([[0,1],[3,3]], "tone")
    trie.incorporate([[1,2],[4,4]], "4one")
    trie.incorporate([[3,5],[6,6]], "6tone")
    trie.incorporate([[0,2],[1,1],[22,2]], "bone")
    # trie.incorporate([[3,5]], "crash!")
    print(trie)

    trie = TermTrieNode()
    trie.incorporate([[0,5],[1,1],[2,1],[3,1],[4,1]], "wi")
    trie.incorporate([[5,2],[1,1]], "wn")
    print(trie)
    
    this worked but redo with tm.parsed versions, already started above
    sub, res = trie.instantiate([1,3], [[0,5],[1,1],[2,1],[1,1],[4,1]])
    assert sub is not None
    assert res == "wi"
    print(sub)
    print(res)
    # s, _ = ct_index.instantiate(t1)
    # print(s)
