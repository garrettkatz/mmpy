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


# all n-tuples (n>0) of (p>0,m>0) pairs if positive integers p with multiplicities m, with constant sum s>=sum(m)
def constant_multisum(s, m):
    # print(f"starting cms({s=},{m=})")
    if len(m) == 1:
        q = s // m[0]
        if s == q*m[0]: yield (q,)
    else:
        slack = s - sum(m[1:])
        # print(f"{slack=}")
        q = slack // m[0]
        # print(f"{q=}")
        if slack == q*m[0]:
            for i in range(1,q+1):
                # print(f"{i=}, im={i*m[0]}, {s=}, s-im={s-i*m[0]}")
                for t in constant_multisum(s-i*m[0], m[1:]):
                    yield (i,) + t

class Scheme:
    def __init__(self, tokens, variables):
        self.tokens = tuple(tokens)
        self.offsets = tuple(t for (t, token) in enumerate(tokens) if token in variables)
        self.chunks = tuple(self.tokens[s+1:t] for (s,t) in zip((-1,)+self.offsets, self.offsets+(len(tokens),)))

    def substitute(self, substitution):
        insertions = [substitution[self.tokens[t]] for t in self.offsets]
        result = self.chunks[0]
        for (insertion, chunk) in zip(insertions, self.chunks[1:]):
            result = result + insertion + chunk
        return result           

    def matches(self, tokens):
        slack = len(tokens) - sum(map(len, self.chunks))
        for holes in constant_sum(slack, len(self.offsets)):
            # could filter more if constant sum constrains same lengths for occurrences of same variables
            # basically a constant_sum with multiplicities
            # could also perhaps save room if some duplicated operations below get pushed into the constant sum generator

            print(self.chunks, holes)
            all_chunks_match = True
            replacements = []
            tail = tuple(tokens)
            for c,chunk in enumerate(self.chunks[:-1]):
                if tail[:len(chunk)] != chunk:
                    all_chunks_match = False
                    break
                replacements.append(tail[len(chunk):len(chunk)+holes[c]])
                tail = tail[len(chunk)+holes[c]:]
            all_chunks_match = all_chunks_match & (tail == self.chunks[-1])
            if not all_chunks_match: continue

            # all chunks match, now try substitutions
            substitution = {}
            substitutions_consistent = True
            for (t, replacement) in zip(self.offsets, replacements):
                variable = self.tokens[t]
                if variable not in substitution:
                    substitution[variable] = replacement
                elif substitution[variable] != replacement:
                    substitutions_consistent = False
                    break
            if not substitutions_consistent: continue

            # substitutions consistent, so yield match
            yield substitution

if __name__ == "__main__":

    import numpy as np
    import metamathpy.setmm as ms
    import metamathpy.database as md
    import metamathpy.proof as mp

    # for t in constant_sum(5, 3): print(t)
    s, m = 3, (2,2,)
    for t in constant_multisum(s, m):
        print(t)
        assert sum(p*mp for (p,mp) in zip(t,m)) == s
    input('.')

    db = ms.load_pl()
    # db = ms.load_all()

    scheme = Scheme("wff ph".split(" "), {"ph"})
    print(" ".join(scheme.substitute({"ph": ("ps",)})))
    for subst in scheme.matches("wff ch".split(" ")):
        print(subst, " ".join(scheme.substitute(subst)))
    input('.')

    scheme = Scheme("wff ( ph -> ph )".split(" "), {"ph"})
    print(" ".join(scheme.substitute({"ph": ("ps",)})))
    for subst in scheme.matches("wff ( ch -> ch )".split(" ")):
        print(subst, " ".join(scheme.substitute(subst)))
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
