"""
symbols[n]: nth token in symbol string
substitution[v]: symbol string to put in place of symbol v
returns result[n]: nth token after substitutions applied
"""
# @profile
def substitute(symbols, substitution):
    result = ()
    for symbol in symbols:
        if symbol in substitution: result += substitution[symbol]
        else: result += (symbol,)
    return result
# from substitute import substitute # cython version

# a subform function for set.mm
def subform_set(s):
    pass

# unify essential hypotheses of a rule with a sequence of dependencies
# each dependency is a ProofStep object
# also required function handle subform
#   subform(s) returns leading string s[:n] that is a well-formed formula
def unify(rule, dependencies, subform):

    # need enough dependencies to match essential hypotheses
    if len(dependencies) < len(rule.essentials):
        return False, {}

    # match with dependencies at top of stack
    dependencies = dependencies[len(dependencies)-len(rule.essentials):]

    # concatenate single symbol strings for essentials and dependencies
    hyp_tokens, dep_tokens = (), ()
    for hyp, dep in zip(rule.essentials, dependencies):
        hyp_tokens += hyp.tokens
        dep_tokens += dep.conclusion.tokens

    # standardize apart the rule variables, assuming dependencies have no $n tokens
    standardizer = {v: f"${n}" for n, v in enumerate(rule.variables)}
    hyp_tokens = substitute(hyp_tokens, standardizer)

    while hyp_tokens != dep_tokens:
        pass

## string version

# def occurrences(string, substring):
#     result = ()
#     while True:
#         idx = string.find(substring)
#         if idx < 0: return result
#         string = string[idx+len(substring):]

# class Scheme:
#     def __init__(self, string, variables):
#         self.string = str(string)
#         # self.offsets = occurrences(string, tuple(t for (t, token) in enumerate(tokens) if token in variables)
#         # self.chunks = tuple(self.tokens[s+1:t] for (s,t) in zip((-1,)+self.offsets, self.offsets+(len(tokens),)))

#     def substitute(self, substitution):
#         insertions = [substitution[self.tokens[t]] for t in self.offsets]
#         result = self.chunks[0]
#         for (insertion, chunk) in zip(insertions, self.chunks[1:]):
#             result = result + insertion + chunk
#         return result           

#     def matches(self, tokens):
#         if tokens[:len(self.chunks[0])] != self.chunks[0]: return
#         tokens[len(self.chunks[0])+1:].find(self.chunks[1])

## tuple version

# all n-tuples (n>0) of positive integers with constant sum s>=n
def constant_sum(s, n):
    if n == 1: yield (s,)
    else:
        for i in range(1,s-n+2):
            for t in constant_sum(s-i, n-1): yield (i,) + t


# all n-tuples (n>0) of positive integers p[i]>0 with multiplicity m[i], such that <p,m> = constant sum s
def constant_multisum(s, m):
    if len(m) == 1:
        q = s // m[0]
        if s == q*m[0]: yield (q,)
    else:
        slack = s - sum(m[1:])
        q = slack // m[0]
        if slack == q*m[0]:
            for i in range(1,q+1):
                for t in constant_multisum(s-i*m[0], m[1:]): yield (i,) + t

def match_helper(vartoks, chunks, tokens, substitution=None):
    # omit the first chunk, so schema tail is vartoks[0]+chunks[0]+vartoks[1]+chunks[1]+...
    if substitution is None: substitution = {}

    # base case: no chunks left
    if len(chunks) == 0:
        # current substitution works if no tokens left either
        if len(tokens) == 0: yield substitution

    # otherwise, iterate over each possible position for next chunk
    else:
        n = len(chunks[0])
        v = vartoks[0]
        # scan remaining positions
        for t in range(1, len(tokens)-n+1):
            # check for match and consistent substitution
            if chunks[0] == tokens[t:t+n] and substitution.get(v, tokens[:t]) == tokens[:t]:
                next_sub = substitution | {v: tokens[:t]}
                yield from match_helper(vartoks[1:], chunks[1:], tokens[t+n:], next_sub)
                

class Scheme:
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
        # variables not in the substitution are left unchanged
        insertions = [substitution.get(self.tokens[t], (self.tokens[t],)) for t in self.offsets]
        result = self.chunks[0]
        for (insertion, chunk) in zip(insertions, self.chunks[1:]):
            result = result + insertion + chunk
        return result           

    def matches(self, tokens):
        # generator that yields matching substitutions
        # could also perhaps save room if some duplicated operations below get pushed into the constant_multisum generator

        # typecast to tuple if not already
        tokens = tuple(tokens)

        # no matches if prefix chunk does not match
        if self.chunks[0] != tokens[:len(self.chunks[0])]: return

        # # use helper on remainder
        yield from match_helper(self.vartoks, self.chunks[1:], tokens[len(self.chunks[0]):])

        # # no matches if prefix or suffix chunks do not match
        # if self.chunks[0] != tokens[:len(self.chunks[0])]: return
        # if self.chunks[-1] != tokens[len(tokens)-len(self.chunks[-1]):]: return

        # # calculate slack, i.e. required sum of substitution lengths to match
        # slack = len(tokens) - sum(map(len, self.chunks))

        # # enumerate possible lengths of each variable substitution string
        # for sub_lens in constant_multisum(slack, self.multiplicities):

        #     # try building substitution for current substitution lengths
        #     substituted = self.chunks[0]
        #     substitution = {}
        #     failure = False
        #     for t, c in zip(self.offsets, self.chunks[1:]):
        #         v = self.tokens[t]
        #         h = sub_lens[self.variables.index(v)]
        #         s = tokens[len(substituted):len(substituted)+h]
        #         if v not in substitution:
        #             substitution[v] = s
        #         if substitution[v] != s:
        #             failure = True
        #             break
        #         if c != tokens[len(substituted)+h:len(substituted)+h+len(c)]:
        #             failure = True
        #             break
        #         substituted = substituted + s + c

        #     if failure: continue

        #     assert substituted == tokens
        #     yield substitution

    # # this version uses constant_sum without multiplicity
    # def matches(self, tokens):
    #     slack = len(tokens) - sum(map(len, self.chunks))
    #     for holes in constant_sum(slack, len(self.offsets)):
    #         # could filter more if constant sum constrains same lengths for occurrences of same variables
    #         # basically a constant_sum with multiplicities
    #         # could also perhaps save room if some duplicated operations below get pushed into the constant sum generator

    #         print(self.chunks, holes)
    #         all_chunks_match = True
    #         replacements = []
    #         tail = tuple(tokens)
    #         for c,chunk in enumerate(self.chunks[:-1]):
    #             if tail[:len(chunk)] != chunk:
    #                 all_chunks_match = False
    #                 break
    #             replacements.append(tail[len(chunk):len(chunk)+holes[c]])
    #             tail = tail[len(chunk)+holes[c]:]
    #         all_chunks_match = all_chunks_match & (tail == self.chunks[-1])
    #         if not all_chunks_match: continue

    #         # all chunks match, now try substitutions
    #         substitution = {}
    #         substitutions_consistent = True
    #         for (t, replacement) in zip(self.offsets, replacements):
    #             variable = self.tokens[t]
    #             if variable not in substitution:
    #                 substitution[variable] = replacement
    #             elif substitution[variable] != replacement:
    #                 substitutions_consistent = False
    #                 break
    #         if not substitutions_consistent: continue

    #         # substitutions consistent, so yield match
    #         yield substitution

if __name__ == "__main__":

    import numpy as np
    import metamathpy.setmm as ms
    import metamathpy.database as md
    import metamathpy.proof as mp

    # # for t in constant_sum(5, 3): print(t)
    # s, m = 7, (2,1,)
    # for t in constant_multisum(s, m):
    #     print(t)
    #     assert sum(p*mp for (p,mp) in zip(t,m)) == s
    # input('.')

    db = ms.load_pl()
    # db = ms.load_all()

    scheme = Scheme("wff ph".split(" "), {"ph"})
    print(scheme)
    print("sub'd by ph->ps:", " ".join(scheme.substitute({"ph": ("ps",)})))
    string = "wff ch"
    print(f"matches to {string}:")
    for subst in scheme.matches(string.split(" ")):
        subd = scheme.substitute(subst)
        assert subd == tuple(string.split(" "))
        print({v: ' '.join(s) for (v,s) in subst.items()}, " ".join(subd))
    input('.')

    scheme = Scheme("wff ( ph -> ph )".split(" "), {"ph"})
    print(scheme)
    print(" ".join(scheme.substitute({"ph": ("ps",)})))
    string = "wff ( ch -> ch )"
    print(f"matches to {string}:")
    for subst in scheme.matches(string.split(" ")):
        print({v: ' '.join(s) for (v,s) in subst.items()}, " ".join(scheme.substitute(subst)))
    input('.')

    # this more complex one works, but does not filter non-wff substitutions since you dont recursively prove yet.
    scheme = Scheme("wff ( ph -> ps )".split(" "), {"ph", "ps"})
    print(scheme)
    print(" ".join(scheme.substitute({"ph": ("ps",)})))
    string = "wff ( ch -> ( ph -> ch ) )"
    print(f"matches to {string}:")
    for subst in scheme.matches(string.split(" ")):
        print({v: ' '.join(s) for (v,s) in subst.items()}, " ".join(scheme.substitute(subst)))
    input('.')

    consequent = md.Statement("test", "$p", "wff ( ph -> ph )".split(" "), ())
    essentials = []
    # floatings = [md.Statement("test2", "$f", "wff ph".split(" "), ())]
    floatings = [db.rules["wph"].consequent]
    disjoint = set()
    variables = {"wph"}
    prove_rule = md.Rule(consequent, essentials, floatings, disjoint, variables)
    prove_rule.finalize()
    print(prove_rule)

    # check known proof
    known_proof = "wph wph wi".split(" ")
    prove_rule.consequent = md.Statement("test", "$p", consequent.tokens, known_proof)
    root, steps = mp.verify_normal_proof(db, prove_rule)
    print(root)

    rule_labels = ["wph", "wi"] # or all p|a labels up to prove_label
    # (should e|f should be handled differently? no hyps of their own, so no substitutions, maybe still works transparently)

    # want something like partial proof steps?

    prove_tokens = consequent.tokens
    for rule_label in rule_labels:
        rule = db.rules[rule_label]
        print('hyps', rule.hypotheses)

        # queue up dependency stubs to match each hyp?
        
        # when do you prune? use the 'skeleton' around the rule's vars, i.e. the constants


        # find first variable occurrence
        for offset, token in enumerate(rule.consequent.tokens):
            if token in rule.variables: break
        if rule.consequent.tokens[:offset] != prove_tokens[:offset]: continue
        print(f"{offset=}: {rule_label} lead {' '.join(rule.consequent.tokens[:offset])} matches {' '.join(prove_tokens)}")

        # set up its floating proof

        # queue up hypothesis proofs? substitutions are built while proving them
        for hyp in rule.hypotheses: pass
        
        # pstep = mp.ProofStep(consequent.tokens, db.rules[rule], dependencies=None, substitution=None, disjoint=None)
        # partial_steps.append(pstep)

    

    # potential_rules = list(premises)
    # for t in range(1, len(consequent.tokens)+1):
    #     for rule_label in list(potential_rules):
    #         rule_tokens = db.rules[rule_label].consequent.tokens
    #         if rule_tokens[:t] != consequent.tokens[:t]:
    #             if rule_tokens[t-1] in db.rules[rule_label].variables:
    #                 # set up recursive proof
    #                 pass
    #             else:
    #                 potential_rules.remove(rule_label)
    #     print(t, consequent.tokens[:t], potential_rules)
    #     if len(potential_rules) == 0: break

    # if len(potential_rules) > 0:
    #     print("potential proof with", potential_rules)
    # else:
    #     print("no matching rules")
