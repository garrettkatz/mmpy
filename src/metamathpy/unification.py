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

## tuple version

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

        # typecast to tuple if not already
        tokens = tuple(tokens)

        # no matches if prefix chunk does not match
        if self.chunks[0] != tokens[:len(self.chunks[0])]: return

        # # use helper on remainder
        yield from match_helper(self.vartoks, self.chunks[1:], tokens[len(self.chunks[0]):])

def backsearch(rules, variables, tokens, max_depth=-1, verbose=False):
    # parameters:
    #   rules: list of rule objects to use as justifications
    #   variables: list of tokens that are metavariables
    #   tokens: token sequence to parse
    #   max_depth: if >= 0, dont search past this depth
    #   verbose: if True, print debug messages
    # returns (success, result)
    #   success: true or false
    #   result: (tokens, rule, dependencies, substitution) needed to reconstruct proof step
    # todo:
    #   extend from wff to rules that dont introduce work variables

    # depth limit reached
    if verbose: print(" "*max_depth + f">>> {' '.join(tokens)}")
    if max_depth == 0: return False, None

    # or-loop (only one rule needs to justify)
    for rule in rules:

        # a hypothesis-less "rule" (ie, hypothesis of whats being currently proved) has to match without substitutions
        if len(rule.hypotheses) == 0:
            if tuple(rule.consequent.tokens) == tokens: # todo: in finalize, change token list to tuple?
                if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}_/(0)")
                return True, (tokens, rule, {}, {})

        # else try all possible substitutions
        else:

            # if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}")
            for substitution in rule.scheme.matches(tokens):
                psub = {k:' '.join(v) for k,v in substitution.items()}
                if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}")
    
                # and-loop: all dependencies must be proved (base case: all([]) is True)
                dependencies = {}
                for hyp in rule.hypotheses:
    
                    # try satisfying
                    success, result = backsearch(rules, variables, substitute(hyp.tokens, substitution), max_depth-1)
                    if not success: break
                    if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}_/{hyp.label}")
                    
                    # satisfied, can use result as dependency 
                    dependencies[hyp.label] = result
    
                # if some hypotheses not satisfied, this substitution and rule does not work
                if len(dependencies) < len(rule.hypotheses):
                    if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}X({len(dependencies)}|{len(rule.hypotheses)})")
                    continue
    
                if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}_/({len(dependencies)})")
    
                # otherwise, it worked, return result
                result = (tokens, rule, dependencies, substitution) # todo: disjoint?
                return True, result

    # no rules worked
    return False, None

if __name__ == "__main__":

    import numpy as np
    import metamathpy.setmm as ms
    import metamathpy.database as md
    import metamathpy.proof as mp

    # helper to reconstruct parse result
    # todo: move to another file to avoid circular unification<->proof imports?
    def reconstruct_proof(parse_result):
        (conclusion, rule, dependencies, substitution) = parse_result
        dependencies = {k: reconstruct_proof(v) for (k,v) in dependencies.items()}
        return mp.ProofStep(conclusion, rule, dependencies, substitution)

    # # for t in constant_sum(5, 3): print(t)
    # s, m = 7, (2,1,)
    # for t in constant_multisum(s, m):
    #     print(t)
    #     assert sum(p*mp for (p,mp) in zip(t,m)) == s
    # input('.')

    db = ms.load_pl()
    # db = ms.load_all()

    # try parsing a wff with schemes for each rule
    wff_vars = {"ph", "ps", "ch"}
    # wff_rules = [db.rules[k] for k in ("wph", "wps", "wch", "wi", "wn")]
    # wff_rules = [db.rules[k] for k in db.rules if k[0] == "w"]
    wff_rules = list(db.rules.values())

    # filter out rules with essentials
    wff_rules = [rule for rule in wff_rules if len(rule.essentials)==0]

    tests = [
        ("wff ph", True),
        ("wff ps", True),
        ("wff ch", True),
        ("wff ( ph -> ph )", True),
        ("wff ( ph -> ps )", True),
        ("wff ( ps -> ch )", True),
        ("wff ps -> ch", False),
        ("wff ( ps ->", False),
        ("wff ps ch", False),
        ("wff -. ps", True),
        ("wff -.", False),
        ("|- ( ph -> ph )", True), # hits recursion depth
    ]
    for s, r in tests:
        tokens = tuple(s.split(" "))
        success, result = backsearch(wff_rules, wff_vars, tokens)#, max_depth=3) # may need max depth if rules with essentials included
        assert success == r, tokens
        if success:
            print(f"^^ token string: {s}")
            # (conclusion, rule, dependencies, substitution) = result
            # print(f"root rule = {rule.consequent.label}")
            rootstep = reconstruct_proof(result)
            print("Final proof:")
            print(rootstep.tree_string())
        else:
            print(f"-- false token string {s}")
    input('no assertions failed...')

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
