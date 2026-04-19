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
    return standardized

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
    input('.')

    scheme = Scheme("wff ( ph -> ph )".split(), {"ph"})
    print(scheme)
    print(" ".join(scheme.substitute({"ph": ("ps",)})))
    string = "wff ( ch -> ch )"
    print(f"matches to {string}:")
    for subst in scheme.matches(string.split()):
        print({v: ' '.join(s) for (v,s) in subst.items()}, " ".join(scheme.substitute(subst)))
    input('.')

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
    schemes = standardize(schemes)
    print("multibinder schemes:", schemes)
    print("multibinder vv")
    for binding, steps in multibinder(schemes, pile):
        print(binding, steps)
    print("multibinder ^^ [should be one match]")


