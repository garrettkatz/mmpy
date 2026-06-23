"""
Trie-like implementation of cterm set indexing structure
"""
try:
    profile
except NameError:
    profile = lambda x: x

import src.metamathpy.database as md
import src.metamathpy.proof as mp
import src.metamathpy.terms as mt

class TermTrieNode:

    def __init__(self, data=None):
        self.data = data
        self.branches = {}

    def tree_string(self, term_manager, prefix=""):
        # if len(self.branches) == 0: return str(self.data)
        s = ["" if self.data is None else str(self.data)]
        for (t,n), child in self.branches.items():
            cs = child.tree_string(term_manager, prefix+" ")
            s.append(f"{prefix}{term_manager.decode(t)} [{t},:{n}] {cs}")
        return "\n".join(s)

    def incorporate(self, term, data=None):
        """
        Incorporates term into self and returns associated node
        If data is not None:
            if node already has non-None data, error is raised
            otherwise, data is stored at node
        """

        if len(term) == 0:
            if data is not None:
                assert self.data is None
                self.data = data
            return self

        head = tuple(term[0])
        if head not in self.branches:
            self.branches[head] = TermTrieNode()
        return self.branches[head].incorporate(term[1:], data)

    def look_ahead(self, n):
        """
        yields (term, node) where
           node is a descendent at depth n
           term is the leading term associated with the path from self to node
        """
        if n == 0:
            yield [], self
        else:
            for head, child in self.branches.items():
                for term, node in child.look_ahead(n-1):
                    yield [list(head)] + term, node

    def instantiate(self, variables, term):
        """
        find substitution of a term indexed in self that instantiates provided term
        "one-way" version of unification
        for example, term = substitution of a rule statement indexed in self
        fails if the term is not an instance of any term in the trie
        returns substitution and index data at self's corresponding leaf, or None if failure
        todo: generate all instead of returning at most one? or maybe not...
        """

        if len(term) == 0:
            if self.data is None: return None, None
            return {}, self.data

        for (tok, n), child in self.branches.items():
            if tok in variables:
                for _, descendent in child.look_ahead(n-1): # already took 1 step to get to child
                    sub, result = descendent.instantiate(variables, term[n:])
                    if sub is not None:
                        sub[tok] = term[:n]
                        return sub, result
            else:
                if tok != term[0][0]: continue
                sub, result = child.instantiate(variables, term[1:])
                if sub is not None: return sub, result

        return None, None

    def prepend(self, term):
        """
        prepend a chain of trie nodes for term ending at self
        returns the root of the chain (self if term is empty)
        used for lazy substitution in unifications_with
        """
        if len(term) == 0: return self
        node = TermTrieNode()
        node.branches[tuple(term[0])] = self.prepend(term[1:])
        return node

    @profile
    def unifications_with(self, term, variables, sub=None, path_term=None):
        """
        yield unifications of terms in self with given term
        assumes self and term are standardized apart
        variables: set of integer ids representing substitutable variables
        sub: substitution accumulator (defaults to empty)
        path_term: path term accumulator (defaults to empty)
        yields accumulated (sub, path_term, data) for successfully unifying leaves (non-None data)
        """

        # defaults
        if sub is None:
            sub = {}
        if path_term is None:
            path_term = []

        # base cases
        if len(term) == 0:
            if self.data is not None:
                yield (sub, path_term, self.data)
                # print("goodbase")
            return

        elif len(self.branches) == 0:
            # print("badbase")
            # print(term)
            # print(self.branches)
            return

        # lazy substitution on term
        if term[0][0] in sub:
            term = sub[term[0][0]] + term[1:]
            # print(f"{term[0][0]} was in sub, lazy sub recursing on:")
            # print(term)
            yield from self.unifications_with(term, variables, sub, path_term)
            return

        # recurse on self's children
        # print(f"no bases, looping over {list(self.branches.items())}, term is:")
        # print(term)
        for (tok, n), child in self.branches.items():

            # lazy substitution on tok
            if tok in sub:
                # print(f"tok {tok} in sub {sub}")
                subtrie = child.prepend(sub[tok])
                yield from subtrie.unifications_with(term, variables, sub, path_term)

            # does tok match term head?
            elif tok == term[0][0]:
                # print(f"tok {tok} == term[0][0] {term[0][0]}")
                yield from child.unifications_with(term[1:], variables, sub, path_term + [[tok, n]])

            # can tok be replaced?
            elif tok in variables:
                # print(f"tok {tok} in variables {variables}")
                rep_len = term[0][1]
                replacement, tail = term[:rep_len], term[rep_len:]
                replacement = mt.substitute(replacement, sub) # lazy substitution

                # do not yield if variable tok occurs in its replacement
                if any(u==tok for (u, _) in replacement): continue

                # otherwise incorporate into substitution and advance to tails
                new_sub = mt.compose_single(tok, replacement, sub)  # result of performing substitution sub followed by {tok: replacement}
                yield from child.unifications_with(tail, variables, new_sub, path_term + [[tok, n]])

            # can term head be replaced?
            elif term[0][0] in variables:
                # print(f"term[0][0] {term[0][0]} in variables {variables}")
                for replacement, node in child.look_ahead(n-1):

                    # extract variable and replacement
                    v = term[0][0] # variable integer id
                    replacement = [[tok, n]] + replacement # include head
                    replacement = mt.substitute(replacement, sub) # lazy substitution

                    # print(f" {n}-step lookahead replacement {replacement} for variable {v}")

                    # do not yield if v occurs in replcement
                    if any(u==v for (u, _) in replacement):
                        # print(f" occurs check failed")
                        continue

                    # otherwise incorporate into substitution and advance to tails
                    new_sub = mt.compose_single(v, replacement, sub)
                    # print(f" occurs check passed, new sub:")
                    # print(new_sub)
                    yield from node.unifications_with(term[1:], variables, new_sub, path_term + replacement)

            # at this point heads do unify, yield nothing and continue to next branch
            # else: continue # noop

        # print("loopdone")
        return # end of def


if __name__ == "__main__":

    import src.metamathpy.setmm as ms

    db = ms.load_pl()
    rules = db.rules_up_to("exormid")
    tm = mt.TermManager([rule for rule in rules["wff"] if rule.consequent.tag == "$a"])
    t1 = tm.parse("( ph -> ps )".split(), ["ph","ps"])

    trie = TermTrieNode()
    print(trie.tree_string(tm))
    leaf = trie.incorporate([[0,2],[1,1]], "one")
    assert leaf.data == "one"
    leaf = trie.incorporate([[0,2],[10,1]], "done")
    assert leaf.data == "done"
    trie.incorporate([[0,1],[3,3]], "tone")
    trie.incorporate([[1,2],[4,4]], "4one")
    trie.incorporate([[3,5],[6,6]], "6tone")
    trie.incorporate([[0,2],[1,1],[22,2]], "bone")
    # trie.incorporate([[3,5]], "crash!")
    print(trie.tree_string(tm))

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

    # bigger tests
    data = [
        # token string, variables, index data
        ["( ph -> ps )", ("ph", "ps"), "wi"],
        ["-. ph", ("ph",), "wn"],
        ["( ph -> ( ps -> ph ) )", ("ph","ps"), "ax-1"],
        ["( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )", ("ph","ps","ch"), "ax-2"],
        ["( ( -. ph -> -. ps ) -> ( ps -> ph ) )", ("ph","ps"), "ax-3"],
        ["( ph -> ph )", ("ph",), "id"],
    ]

    trie = TermTrieNode()
    for (toks, variables, label) in data:
        term = tm.parse(toks.split(), variables)
        trie.incorporate(term, label)

    trie_vars = tuple(tm.encode(v) for v in ("ph","ps","ch"))
    print(trie.tree_string(tm))

    for (toks, variables, label) in data:
        term = tm.parse(toks.split(), variables)
        sub, res = trie.instantiate(tuple(tm.encode(v) for v in variables), term)
        assert sub is not None
        for (v,t) in sub.items(): assert t == [[v,1]]
        assert res == label

    # singleton variable term should unify with all
    term = tm.parse(("ta",), ("ta",))
    print(term)
    subs, path_terms, results = zip(*trie.unifications_with(term, (term[0][0],) + trie_vars))
    assert len(subs) == len(data)
    for (toks, variables, label) in data:
        assert label in results

        print(toks)
        tterm = tm.parse(toks.split(), variables)
        sub = {term[0][0]: tterm}
        idx = results.index(label)

        assert sub == subs[idx]

    # special cases, standardized apart
    print("\n special cases \n")
    print(trie.tree_string(tm))
    tests = [
        ["( ta -> ta )", ("ta",), ("id","wi")],
        ["( ta -> et )", ("ta","et"), ("wi", "ax-1", "ax-2", "ax-3", "id")],
        ["-. ( ta -> ta )", ("ta",), ("wn",)],
        ["( -. ta -> ta )", ("ta",), ("wi",)],
        ["( -. ta -> ( ta -> ta ) )", ("ta",), ("wi",)],
        ["( ta /\ et )", ("ta","et"), ()],
    ]
    trie_labels = [lab for (_,_,lab) in data]
    for (toks, variables, labels) in tests:
        print(toks)
        term_vars = tuple(tm.encode(v) for v in variables)
        assert len(set(term_vars) & set(trie_vars)) == 0 # standardized apart
        term = tm.parse(toks.split(), variables)
        if len(labels) == 0:
            emptygen = list(trie.unifications_with(term, term_vars + trie_vars))
            assert len(emptygen) == 0
            subs, results = (), ()
        else:
            subs, path_terms, results = zip(*trie.unifications_with(term, term_vars + trie_vars))
        print(sorted(results))
        print(sorted(labels))
        for sub, res in zip(subs, results):
            print(res, {tm.decode(v): " ".join(tm.serialize(t)) for (v,t) in sub.items()})
            idx = trie_labels.index(res)
            dterm = tm.parse(data[idx][0].split(), data[idx][1])
            assert mt.substitute(dterm, sub) == mt.substitute(term, sub)
        assert set(results) == set(labels)

    print("bigger tests passed")

    trie = TermTrieNode()
    trie_vars = set()
    for rule in rules["wff"]:
        if rule.consequent.tag != "$a": continue
        trie_vars |= set([tm.encode(v) for v in rule.mandatory])
        term = tm.parse(rule.consequent.tokens[1:], set(rule.mandatory.keys()))
        trie.incorporate(term, rule.consequent.label)

    for rule in rules["wff"]:
        if rule.consequent.tag != "$a": continue
        term = tm.parse(rule.consequent.tokens[1:], set(rule.mandatory.keys()))
        term_vars = {tm.encode(v) for v in rule.mandatory}

        # standardize apart term
        term, term_vars = tm.standardize_apart(trie_vars, term, term_vars)

        num = 0
        for (sub, path_term, res) in trie.unifications_with(term, term_vars | trie_vars):
            num += 1
            assert res == rule.consequent.label
            print('term'," ".join(tm.serialize(term)))
            print('term',term)
            print('pterm'," ".join(tm.serialize(path_term)))
            print('pterm',path_term)
            print('sub',sub)
            assert mt.substitute(term, sub) == mt.substitute(path_term, sub)

    print(trie.tree_string(tm))

