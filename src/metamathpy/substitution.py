try:
    profile
except NameError:
    profile = lambda x: x

# @profile
def substitute(symbols, substitution):
    """
    direct substitution into symbol string
    symbols[n]: nth token in symbol string
    substitution[v]: symbol string to put in place of symbol v
    returns result[n]: nth token after substitutions applied
    """
    result = ()
    for symbol in symbols:
        if symbol in substitution: result += substitution[symbol]
        else: result += (symbol,)
    return result
# from substitute import substitute # cython version

def compose(t, s):
    """
    equivalent substitution to performing s followed by t
    """
    ts = {}
    for k, v in s.items():
        tv = substitute(v, t)
        if tv[0] != k: ts[k] = tv
    for k, v in t.items():
        if k not in s: ts[k] = v
    return ts

@profile
def match_helper(vartoks, chunks, tokens, substitution):
    """
    recursive helper for Scheme.matches
    matches the tail of a token string against the tails of a scheme.vartoks[i:] and .chunks[i+1:]
    schemes have one more chunk than vartok and the leading chunk should be omitted in the top-level call
    substition should start empty at the top-level call and is populated during the recursion
    """

    # base case: no chunks left in the tail
    if len(chunks) == 0:
        # current substitution works if no tokens left either
        if len(tokens) == 0: yield substitution

    # otherwise, iterate over each possible position for next chunk
    else:

        n = len(chunks[0])
        v = vartoks[0]

        # need to reserve at least this many tokens for tail after vartoks[0]
        reserved = sum(map(len, chunks)) + len(vartoks)-1

        # scan remaining positions
        for t in range(1, len(tokens)-reserved+1):
            # check for match and consistent substitution
            if chunks[0] == tokens[t:t+n] and substitution.get(v, tokens[:t]) == tokens[:t]:
                next_sub = substitution | {v: tokens[:t]}
                # recurse on the remaining tails with the new substitution
                yield from match_helper(vartoks[1:], chunks[1:], tokens[t+n:], next_sub)

@profile
def pile_match_helper(vartoks, chunks, node, varfix, substitution):
    """
    recursive helper for Scheme.matches
    matches the tokens under pile trie node against scheme tail zip(vartoks[i:], chunks[i+1:])
    schemes have one more chunk than vartok and the leading chunk should be omitted in the top-level call
    varfix is leading token sequence to be substituted for vartoks[0], start empty and fill during the recursion
    substition should start empty at the top-level call and is populated during the recursion
    """

    # base case: no chunks left in the tail
    if len(chunks) == 0:
        # current substitution works if there is a matching step with no tokens left either
        if node.step is not None: yield (substitution, node.step)

    # otherwise, iterate over possibilities for current vartok
    else:

        # if current vartok already substituted, need to apply here too
        if vartoks[0] in substitution:
            # will only work if substitution still matches
            descendent = node.traverse(substitution[vartoks[0]] + chunks[0])
            if descendent is not None:
                # advance to tail with same substitution
                yield from pile_match_helper(vartoks[1:], chunks[1:], descendent, (), substitution)

        # otherwise, continue searching current vartok's candidate substitutions
        else:

            # if varfix not empty, try ending current vartok substitution here
            if len(varfix) > 0:
                # will only work if next chunk can be matched
                descendent = node.traverse(chunks[0])
                if descendent is not None:
                    # update substitution for current vartok and advance to next one
                    next_sub = substitution | {vartoks[0]: varfix}
                    yield from pile_match_helper(vartoks[1:], chunks[1:], descendent, (), next_sub)
    
            # also try recursively appending each possible next token (if any) to varfix
            for (token, child) in node.children.items():
                yield from pile_match_helper(vartoks, chunks, child, varfix + (token,), substitution)

class Scheme:
    """
    Wrapper for symbol strings to support matching and unification
    tokens[i]: the ith token in the scheme's symbol sequence
    variables: the subset of tokens that are substitutable variables
    the scheme's symbol string is split into the form
        tokens == chunks[0] + vartoks[0] + chunks[1] + vartoks[1] + ... + vartoks[n] + chunks[n+1]
    where chunks are constants and vartoks are variable occurrances that can be substituted
    """
    def __init__(self, tokens, variables):
        self.tokens = tuple(tokens)
        self.variables = tuple(variables)
        self.multiplicities = tuple(tokens.count(v) for v in self.variables)
        self.offsets = tuple(t for (t, token) in enumerate(tokens) if token in variables)
        self.vartoks = tuple(self.tokens[t] for t in self.offsets)
        self.chunks = tuple(self.tokens[s+1:t] for (s,t) in zip((-1,)+self.offsets, self.offsets+(len(tokens),)))

    def __repr__(self):
        return f"Scheme({' '.join(self.tokens)}, v={self.variables})"

    def substitute(self, substitution):
        """
        returns the scheme's symbol string with some variables replaced
        substitution[v] = token sequence to replace v with
        variables not in the substitution are left unchanged
        """
        insertions = [substitution.get(self.tokens[t], (self.tokens[t],)) for t in self.offsets]
        result = self.chunks[0]
        for (insertion, chunk) in zip(insertions, self.chunks[1:]):
            result = result + insertion + chunk
        return result           

    @profile
    def matches(self, tokens):
        """
        Generator that yields all substitutions which match this scheme with the given token sequence
        Wraps the top-level call to match_helper
        """

        # typecast to tuple if not already
        tokens = tuple(tokens)

        # no matches if prefix chunk does not match
        if self.chunks[0] != tokens[:len(self.chunks[0])]: return

        # otherwise initiate recursive helper on remainder
        yield from match_helper(self.vartoks, self.chunks[1:], tokens[len(self.chunks[0]):], {})

    @profile
    def pile_matches(self, root):
        """
        Generator that yields all (sub, step) pairs such that self.substitute(sub) matches step in pile
        Input should be root of pile trie
        """

        # no matches if prefix chunk does not match
        node = root.traverse(self.chunks[0])
        if node is None: return

        # otherwise initiate recursive helper on remainder
        yield from pile_match_helper(self.vartoks, self.chunks[1:], node, (), {})

    def unifiers_with(self, other, max_depth=-1, prefix=None):
        """
        Generate unifiers with other scheme
        assumes already standardized apart
        """
        for s, v in unify_words(self.tokens, other.tokens, set(self.variables) | set(other.variables), max_depth=max_depth, prefix=prefix):
            assert self.substitute(s) == other.substitute(s)
            yield s, v

def standardize(schemes, base="v", start=0):
    """
    Renames scheme variables to {base}{start}, {base}{start+1}, ...
    todo: better way of ensuring no name collisions
    """
    # collect all variables
    variables = set(sum([s.variables for s in schemes], ()))
    standardizer = {v: (f"{base}{start+d}",) for (d, v) in enumerate(variables)}
    standardized = []
    for s in schemes:
        tokens = s.substitute(standardizer)
        variables = [standardizer[v][0] for v in s.variables]
        standardized.append(Scheme(tokens, variables))
    return standardized, standardizer

@profile
def multibinder(schemes, pile):
    # yield every substitution s such that all(scheme.sub(s) in pile.keys for scheme in schemes)
    # also yields the corresponding steps in the pile

    # try matching first scheme against each token sequence in the pile
    for tokens, step in pile.items():
        for bindings in schemes[0].matches(tokens):

            # base case: this is the last scheme, so done
            if len(schemes) == 1:
                yield bindings, (step,)
                continue

            # recursive case: check if these bindings also work for remaining schemes
            sub_schemes = []
            for scheme in schemes[1:]:
                sub_schemes.append(Scheme(
                    scheme.substitute(bindings),
                    set(scheme.variables) - set(bindings.keys())
                ))

            for sub_bindings, steps in multibinder(sub_schemes, pile):
                yield (bindings | sub_bindings), ((step,) + steps)

@profile
def pilebinder(schemes, pile_trie_root):
    # like multibinder but with a pile trie data structure

    for (bindings, step) in schemes[0].pile_matches(pile_trie_root):

        # base case: this is the last scheme, so done
        if len(schemes) == 1:
            yield bindings, (step,)
            continue

        # recursive case: check if these bindings also work for remaining schemes
        sub_schemes = []
        for scheme in schemes[1:]:
            sub_schemes.append(Scheme(
                scheme.substitute(bindings),
                set(scheme.variables) - set(bindings.keys())
            ))

        for sub_bindings, steps in pilebinder(sub_schemes, pile_trie_root):
            yield (bindings | sub_bindings), ((step,) + steps)

@profile
def unify_words(xt, yt, vts, xh=(), yh=(), u=0, max_depth=-1, s=None, prefix=None):
    """
    warning - may not terminate
    generates all substitutions s such that sub(xt,s) == sub(yt,s)
    xt, yt are token string tails, assumes standardized apart at top-level call
    vts are variable tokens
    _h are current substitution heads for current variables xt[0] and yt[0] (or () if non-variables)
    u is counter for fresh work variables
    max_depth: limit to recursive calls to guard against non-termination (-1 means no limit)
    s is the substitution, built up during recursion
    prefix: None or "" in top-level call for verbosity
    cf "word unification", Schulz 1991 "Word unification and transformation of generalized equations"
    """

    if s is None: s = {}

    # base case: both strings done, substitution works
    if xt == yt == (): yield s, vts

    # base case: only one string done, failure
    if () in (xt, yt): return

    # base case: max depth
    if max_depth == 0: return

    if prefix is not None:
        ss = {k: ' '.join(v) for k,v in s.items()}
        print(f"{prefix}unify({' '.join(xt)}, {' '.join(yt)}, {vts}, xh={' '.join(xh)}, yh={' '.join(yh)}, s={ss}")
        prefix = prefix + " "

    # if current tokens both variables:
    if (xt[0] in vts) and (yt[0] in vts):

        # if same variable, no new substitution needed, advance both
        if xt[0] == yt[0]:
            yield from unify_words(xt[1:], yt[1:], vts, (), (), u, max_depth-1, s, prefix)

        # otherwise introduce new variable for any overlap and advance in at least one sequence
        else:

            # name fresh overlap variable
            v = f"u{u}"

            # advance in x, committing to substitution for xt[0]
            assert xt[0] not in xh + (v,) # occurs check?
            xs = {xt[0]: xh + (v,)}
            yield from unify_words(substitute(xt[1:], xs), substitute(yt, xs), vts | {v}, (), substitute(yh, xs) + (v,), u+1, max_depth-1, compose(xs, s), prefix)

            # advance in y, committing to substitution for yt[0]
            assert yt[0] not in yh + (v,) # occurs check?
            ys = {yt[0]: yh + (v,)}
            yield from unify_words(substitute(xt, ys), substitute(yt[1:], ys), vts | {v}, substitute(xh, ys) + (v,), (), u+1, max_depth-1, compose(ys, s), prefix)

            # advance in both, committing to both substitutions one at a time
            xys = compose(xs, ys) # need to compose since xt[0] might be in yh or vice versa
            if prefix is not None:
                print(f"{prefix}both!")
                print(prefix + str({a:' '.join(b) for a,b in xys.items()}))
            yield from unify_words(substitute(xt[1:], xys), substitute(yt[1:], xys), vts | {v}, (), (), u+1, max_depth-1, compose(xys, s), prefix)

    # if only one is variable:
    elif xt[0] in vts:

        # only advance in y, extending current substitution for xt[0]
        yield from unify_words(xt, yt[1:], vts, xh + yt[:1], (), u, max_depth-1, s, prefix)

        # advance in both, committing to substitution for xt[0]
        xs = {xt[0]: xh + yt[:1]}
        assert xt[0] not in xh + yt[:1] # occurs check?
        yield from unify_words(substitute(xt[1:], xs), substitute(yt[1:], xs), vts, (), (), u, max_depth-1, compose(xs, s), prefix)

    elif yt[0] in vts:

        # only advance in x, extending current substitution for yt[0]
        yield from unify_words(xt[1:], yt, vts, (), yh + xt[:1], u, max_depth-1, s, prefix)

        # advance in both, committing to substitution for yt[0]
        ys = {yt[0]: yh + xt[:1]}
        assert yt[0] not in yh + xt[:1] # occurs check?
        yield from unify_words(substitute(xt[1:], ys), substitute(yt[1:], ys), vts, (), (), u, max_depth-1, compose(ys, s), prefix)

    # both constants:
    else:

        # unification fails if constants do not match
        if xt[0] != yt[0]: return

        # otherwise, advance both
        yield from unify_words(xt[1:], yt[1:], vts, (), (), u, max_depth-1, s, prefix)


if __name__ == "__main__":

    import metamathpy.database as md
    import metamathpy.proof as mp
    import metamathpy.setmm as ms

    db = ms.load_pl()
    # db = ms.load_all()

    scheme = Scheme("wff ph".split(), {"ph"})
    print(scheme)
    print("sub'd by ph->ps:", " ".join(scheme.substitute({"ph": ("ps",)})))
    string = "wff ch"
    print(f"matches to {string}:")
    for subst in scheme.matches(string.split()):
        subd = scheme.substitute(subst)
        assert subd == tuple(string.split())
        print({v: ' '.join(s) for (v,s) in subst.items()}, " ".join(subd))
    # input('.')

    scheme = Scheme("wff ( ph -> ph )".split(), {"ph"})
    print(scheme)
    print(" ".join(scheme.substitute({"ph": ("ps",)})))
    string = "wff ( ch -> ch )"
    print(f"matches to {string}:")
    for subst in scheme.matches(string.split()):
        print({v: ' '.join(s) for (v,s) in subst.items()}, " ".join(scheme.substitute(subst)))
    # input('.')

    # this more complex one works, but does not filter non-wff substitutions since you dont recursively prove yet (thats done in backsearch.py)
    scheme = Scheme("wff ( ph -> ps )".split(), {"ph", "ps"})
    print(scheme)
    print(" ".join(scheme.substitute({"ph": ("ps",)})))
    string = "wff ( ch -> ( ph -> ch ) )"
    print(f"matches to {string}:")
    for subst in scheme.matches(string.split()):
        print({v: ' '.join(s) for (v,s) in subst.items()}, " ".join(scheme.substitute(subst)))

    # test multibinder
    schemes = [Scheme("|- ph".split(), ('ph',)), Scheme("|- ( ph -> ps )".split(), ('ps', 'ph'))]
    pile = {
        tuple("|- ps".split()): mp.ProofStep(tuple("|- ps".split()), db.rules["mp2.2"]),
        tuple("|- ( ps -> ch )".split()): mp.ProofStep(tuple("|- ( ps -> ch )".split()), db.rules["ax-mp"]),
    }
    schemes, _ = standardize(schemes)
    print("multibinder schemes:", schemes)
    print("multibinder vv")
    multibinds = []
    for binding, steps in multibinder(schemes, pile):
        print(binding, steps)
        multibinds.append((binding, steps))
    print("multibinder ^^ [should be one match]")

    # test pile trie matching
    from metamathpy.piletrie import trieify
    root = trieify(pile)
    print(root.tree_string())

    for scheme in schemes:
        print(f"pile matching {scheme}")
        for (sub, step) in scheme.pile_matches(root):
            print("sub:", sub)
            print("stp:", step)
    print("scheme pile matching ^^")

    pilebinds = []
    print("pilebinder vv")
    for binding, steps in pilebinder(schemes, root):
        print(binding, steps)
        pilebinds.append((binding, steps))
    print("pilebinder results ^^")
    for binding, steps in pilebinds:
        assert (binding, steps) in multibinds
    for binding, steps in multibinds:
        assert (binding, steps) in pilebinds
    print("assertions passed, pilebinder = multibinder")

    # particular pilebinder test case
    schemes = [
        Scheme("|- ( v0 -> ( v0 -> v1 ) )".split(), ('v0', 'v1')),
    ]
    pile = {
        tuple("|- ( ph -> ( ps -> ( ps -> ch ) ) )".split()): mp.ProofStep(tuple("|- ( ph -> ( ps -> ( ps -> ch ) ) )".split()), db.rules["pm2.43d.1"]),
    }
    root = trieify(pile)
    print(root.tree_string())
    print("pile trie^^, scheme to match against it:", schemes[0])
    num_subs = 0
    for sub, step in schemes[0].pile_matches(root):
        subd = schemes[0].substitution(sub)
        print("sub", sub)
        print("subd", subd)
        print("step", step)
        assert subd == step.conclusion, "subd != step"
        num_subs += 1
    assert num_subs == 0
    print(f"^^ all matches (there are {num_subs})")

    # ## test unify schemes (assumes already standardized)
    # x = Scheme("|- ph".split(), ("ph",))
    # y = Scheme("|- ps".split(), ("ps",))
    # print(f"unifying {x} with {y}:")
    # for sub in unify_schemes(x, y):
    #     print({k: " ".join(v) for k,v in sub.items()})

    # x = Scheme("|- -. ph".split(), ("ph",))
    # y = Scheme("|- ps".split(), ("ps",))
    # print(f"unifying {x} with {y}:")
    # for s in unify_schemes(x, y):
    #     print({k: " ".join(v) for k,v in s.items()})
    #     print(" ".join(x.substitute(s)))
    #     assert x.substitute(s) == y.substitute(s)

    # x = Scheme("|- ( ph -> ch )".split(), ("ph","ch"))
    # y = Scheme("|- ps".split(), ("ps",))
    # print(f"unifying {x} with {y}:")
    # for s in unify_schemes(x, y):
    #     print({k: " ".join(v) for k,v in s.items()})
    #     print(" ".join(x.substitute(s)))
    #     assert x.substitute(s) == y.substitute(s)

    # x = Scheme("|- -. ph".split(), ("ph",))
    # y = Scheme("|- ps -.".split(), ("ps",))
    # print(f"unifying {x} with {y}:")
    # for s in unify_schemes(x, y):
    #     print({k: " ".join(v) for k,v in s.items()})
    #     print(" ".join(x.substitute(s)))
    #     assert x.substitute(s) == y.substitute(s)

    # # unbalanced but should still work syntactically
    # x = Scheme("|- ( ph -> ( ps -> ph )".split(), ("ph","ps"))
    # y = Scheme("|- ( ch -> ta )".split(), ("ch","ta"))
    # print(f"unifying {x}\nwith     {y}:")
    # for s in unify_schemes(x, y):
    #     print({k: " ".join(v) for k,v in s.items()})
    #     print(" ".join(x.substitute(s)))
    #     print(" ".join(y.substitute(s)))
    #     assert x.substitute(s) == y.substitute(s)

    # test composition
    ts = compose({"y": ("z",)}, {"x": ("y",)})
    assert ts == {"y": ("z",), "x": ("z",)}

    ## test unify sequences (assumes already standardized)
    # unify_words(xt, yt, xv, yv, xh=(), yh=(), u=0, s=None):
    x = Scheme("|- ph".split(), ("ph",))
    y = Scheme("|- ps".split(), ("ps",))
    print(f"unifying {' '.join(x.tokens)} with {' '.join(y.tokens)}:")
    # for s, _ in unify_words(x.tokens, y.tokens, set(x.variables) | set(y.variables)):
    for s, _ in x.unifiers_with(y):
        print({k: " ".join(v) for k,v in s.items()})
        print(" ".join(x.substitute(s)))
        assert x.substitute(s) == y.substitute(s)

    x = Scheme("|- -. ph".split(), ("ph",))
    y = Scheme("|- ps".split(), ("ps",))
    print(f"unifying {' '.join(x.tokens)} with {' '.join(y.tokens)}:")
    for s, _ in x.unifiers_with(y):
        print({k: " ".join(v) for k,v in s.items()})
        print(" ".join(x.substitute(s)))
        assert x.substitute(s) == y.substitute(s)

    x = Scheme("|- ( ph -> ch )".split(), ("ph","ch"))
    y = Scheme("|- ps".split(), ("ps",))
    print(f"unifying {' '.join(x.tokens)} with {' '.join(y.tokens)}:")
    for s, _ in x.unifiers_with(y):
        print({k: " ".join(v) for k,v in s.items()})
        print(" ".join(x.substitute(s)))
        assert x.substitute(s) == y.substitute(s)

    x = Scheme("|- -. ph".split(), ("ph",))
    y = Scheme("|- ps -.".split(), ("ps",))
    print(f"unifying {' '.join(x.tokens)} with {' '.join(y.tokens)}:")
    for s, _ in x.unifiers_with(y):
        print({k: " ".join(v) for k,v in s.items()})
        print(" ".join(x.substitute(s)))
        assert x.substitute(s) == y.substitute(s)

    x = Scheme("ph -> ch".split(), ("ph","ch"))
    y = Scheme("ps -> ta".split(), ("ps","ta"))
    print(f"unifying {' '.join(x.tokens)} with {' '.join(y.tokens)}:")
    for s, _ in x.unifiers_with(y):
        print({k: " ".join(v) for k,v in s.items()})
        print(" ".join(x.substitute(s)))
        assert x.substitute(s) == y.substitute(s)
        # break

    x = Scheme("ph -> ph".split(), ("ph",))
    y = Scheme("ps -> ta".split(), ("ps","ta"))
    print(f"unifying {' '.join(x.tokens)} with {' '.join(y.tokens)}:")
    for s, _ in x.unifiers_with(y):
        print({k: " ".join(v) for k,v in s.items()})
        print(" ".join(x.substitute(s)))
        print(" ".join(y.substitute(s)))
        assert x.substitute(s) == y.substitute(s)
        # break

    # unbalanced should still work syntactically
    xs = [ 
        Scheme("|- ( ph -> ( ps -> ph )".split(), ("ph","ps")),
        Scheme("|- ( ph -> ( ps -> et )".split(), ("ph","ps","et")),
        Scheme("|- ( ph -> ( ps -> et ) )".split(), ("ph","ps","et")),
    ]
    y = Scheme("|- ( ch -> ta )".split(), ("ch","ta"))
    for x in xs:
        print(f"unifying {' '.join(x.tokens)}\nwith     {' '.join(y.tokens)}:")
        for s, _ in x.unifiers_with(y):
            s = {k: v for (k,v) in s.items() if k in set(x.variables) | set(y.variables)}
            print({k: " ".join(v) for k,v in s.items()})
            print(" ".join(x.substitute(s)))
            print(" ".join(y.substitute(s)))
            assert x.substitute(s) == y.substitute(s)

    # non-terminating case? from schulz 1991
    x = Scheme("x y x y".split(), ("x","y"))
    # y = Scheme("a X Y X Y a".split(), ("X","Y"))
    y = Scheme("a x y x y a".split(), ("x","y"))
    print(x)
    print(y)
    print("\nnon-terminating?\n")
    for i, s in enumerate(unify_words(x.tokens, y.tokens, set(x.variables) | set(y.variables), prefix="")):
        # print(i,s)
        print(i,x.substitute(s))
    input("^^")

    # what would modus ponens look like?
    print("\n * mp * \n")
    x = Scheme("|- ph".split(), ("ph",))
    mj = Scheme("|- a -> b".split(), ("a","b"))
    mn = Scheme("|- a".split(), ("a","b"))
    y = Scheme("|- b".split(), ("a","b"))
    z = Scheme("|- A -> ( B -> A )".split(), ("A", "B"))
    for s, v in x.unifiers_with(y):
        print(s)
        mjs = mj.substitute(s)
        mns = mn.substitute(s)
        ys = y.substitute(s)
        mjs = Scheme(mjs, v & set(mjs))
        mns = Scheme(mns, v & set(mns))
        ys = Scheme(ys, v & set(ys))
        print("mj", mjs)
        print("mn", mns)
        print("y", ys)
        for t, u in mj.unifiers_with(z):
            print(mj)
            print(mn)
            print(y)
            print(z)
            print("", t, " ".join(z.substitute(t)))
        # for t in unify_words(z, ... this already shows that substitute is not enough, the result should still be a scheme

