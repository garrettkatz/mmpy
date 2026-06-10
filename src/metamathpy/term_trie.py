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

    @profile
    def unifications_with(self, term, variables, sub=None):
        """
        yield unifications of terms in self with given term
        assumes self and term are standardized apart
        variables: set of integer ids representing substitutable variables
        sub: substitution accumulator (defaults to empty)
        yields substitutions and index data for successfully unifying leaves
        """

        also here doublecheck any written brainstorms about this

        if sub is None:
            sub = {}

        if len(term) == len(self.branches) == 0:
            yield ({}, self.result)
            return

        if (len(term) == 0) or (len(self.branches) == 0):
            return

        for (tok, n), child in self.branches.items():

            if tok in sub:
                replace tok if in sub... and invoke mt(sub[tok]:term, term[:n]) unify?
                recurse on tail after 

            if tok == term[0][0]:
                yield from child.unifications_with(term[1:], variables, sub):
                    
            elif tok in variables:
                replacement = term[:term[0][1]]
    
                # do not yield if variable tok occurs in its replacement
                if any(u==tok for (u, _) in replacement): continue
    
                # otherwise incorporate substitution and advance to tails
                yield from child.unifications_with(term[term[0][1]:], variables, sub | {tok: replacement}) <- check | precedence here

            elif term[0][0] in variables:
                for replacements in child.look_ahead(n-1):

            # at this point term heads do unify, yield nothing and continue to next branch

        # # build up substitution while consuming term heads until empty
        # s = {}
        # while len(t1) > 0 and len(t2) > 0: t1 becomes self, t2 becomes term
    
        #     # if heads match, advance to tails
        #     if t1[0][0] == t2[0][0]:
        #         t1 = t1[1:]
        #         t2 = t2[1:]
        #         continue
    
        #     # check if either term head is a variable
        #     v1 = (t1[0][0] in variables)
        #     v2 = (t2[0][0] in variables)
        #     if v1 or v2:
    
        #         # swap if needed so t1 has the variable head
        #         if not v1: t1, t2 = t2, t1
    
        #         # extract variable and subterm
        #         v = t1[0][0] # variable integer id
        #         n = t2[0][1] # length of replacement term
        #         st = t2[:n] # replacement term
    
        #         # fail if v occurs in st
        #         if any(u==v for (u, _) in st): return None
    
        #         # otherwise incorporate substitution and advance to term tails
        #         s = compose_single(v, st, s)
        #         t1 = substitute_single(t1[1:], v, st)
        #         t2 = substitute_single(t2[n:], v, st)
        #         # new_s = {v: st}
        #         # s = compose(new_s, s)
        #         # t1 = substitute(t1[1:], new_s)
        #         # t2 = substitute(t2[n:], new_s)
    
        #     # otherwise term heads are distinct constants so fail
        #     else: return None
    
        # # success if both terms fully consumed
        # if len(t1) == len(t2) == 0: return s
    
        # # otherwise failure
        # return None


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

    # this worked but redo with tm.parsed versions, already started above
    trie = TermTrieNode()
    trie.incorporate([[0,5],[1,1],[2,1],[3,1],[4,1]], "wi")
    trie.incorporate([[5,2],[1,1]], "wn")
    sub, res = trie.instantiate([1,3], [[0,5],[1,1],[2,1],[1,1],[4,1]])
    assert sub is not None
    assert res == "wi"

    trie = TermTrieNode()
    trie.incorporate(tm.parse("( ph -> ps )".split(), ["ph","ps"]), "wi")
    trie.incorporate(tm.parse("-. ph".split(), ["ph"]), "wn")
    sub, res = trie.instantiate([tm.encode("ph"),tm.encode("ps")], tm.parse("( ph -> ph )".split(), ["ph"]))
    assert sub is not None
    assert res == "wi"
    print(f"ph => {tm.encode('ph')}")
    print(f"ps => {tm.encode('ps')}")
    print(sub)
    print(res)
    # s, _ = ct_index.instantiate(t1)
    # print(s)
