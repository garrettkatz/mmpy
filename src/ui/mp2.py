# just search for the first non-instananeous, mp2
from time import perf_counter
import itertools as it

from metamathpy.unification import substitute
import metamathpy.setmm as ms
import metamathpy.proof as mp

def dfs(db, rule_labels, prove_label, max_depth, steps=None):
    # steps[typecode][conclusion] = proof step
    # returns status, final step or None

    # initialize steps if needed
    if steps is None: steps = {"wff": {}, "|-": {}}

    # get goal tokens
    goal = tuple(db.rules[prove_label].consequent.tokens)

    # base case: stop if goal conclusion is in steps
    if goal in steps["|-"]:
        return "success", steps["|-"][goal]

    # base case: stop if max depth reached
    if max_depth == 0:
        return "failure", None

    # try applying each rule
    for rule_label in rule_labels:
        # print(" "*max_depth + rule_label)
        rule = db.rules[rule_label]

        # apply rule to all wff combinations for metavariables
        wffs = list(steps["wff"].values())
        for deps in it.product(wffs, repeat=len(rule.floatings)):

            # set up substitution
            substitution = {}
            for (hyp, dep) in zip(rule.floatings, deps):
                # assert matching types (only works for PL)
                assert hyp.tokens[0] == dep.conclusion[0] == "wff"
        
                # update substitution
                variable = hyp.tokens[1]
                substitution[variable] = dep.conclusion[1:]

            # apply substitution and check if essentials are satisfied
            satisfied = True
            for hyp in rule.essentials:
                substituted = substitute(hyp.tokens, substitution)
                if substituted not in steps["|-"]:
                    satisfied = False
                    break
                deps = deps + (steps["|-"][substituted],)

            # if not, move on to next combo
            if not satisfied: continue

            # otherwise, get conclusion and make sure inference checks out
            step, status = mp.perform(rule, deps)
            assert status == ""

            # move on if redundant step
            tokens = step.conclusion
            typecode = tokens[0] # wff or |-
            if tokens in steps[typecode]: continue

            # add resulting proof step and recurse
            steps[typecode][tokens] = step
            result, proof = dfs(db, rule_labels, prove_label, max_depth-1, steps)

            # propagate any solutions
            if result == "success": return result, proof

            # otherwise backtrack step for next combo
            steps[typecode].pop(tokens)

    return "failure", None
    

if __name__ == "__main__":

    db = ms.load_pl()

    prove_label = "mp2"
    rule_labels = tuple(db.rules.keys())
    rule_labels = rule_labels[:rule_labels.index(prove_label)]
    # rule_labels = [label for label in rule_labels if db.rules[label].consequent.tag[1] in "pfa"]
    rule_labels = [label for label in rule_labels if db.rules[label].consequent.tag[1] in "pa"]
    rule_labels = [f.label for f in db.rules[prove_label].floatings] + rule_labels
    rule_labels += [e.label for e in db.rules[prove_label].essentials]

    # sanity check: preselect premises
    rule_labels = ["wps","wch","mp2.2","wph","wi","mp2.1","mp2.3","ax-mp"]

    for label in rule_labels: print(db.rules[label])
    print(f"{len(rule_labels)} rules (branch factor)")

    input('..')
    for max_depth in range(1,10):

        start = perf_counter()
        result, proof = dfs(db, rule_labels, prove_label, max_depth)
        duration = perf_counter()-start
        print(f"{max_depth=}: {result} in {duration:.3f}s")
        if result == "success": print(proof.normal_proof())


