"""
mvp: forward dfs search with:
init pile with subwffs and essential hypotheses in goal
only try |- rules, use backsearch for any wff rules
only iter over wff dependencies for essentialess rules or work variables
"""
import itertools as it
import metamathpy.database as md
import metamathpy.proof as mp
import metamathpy.backsearch as mb
from metamathpy.substitution import Scheme, substitute, standardize, multibinder

try:
    profile
except NameError:
    profile = lambda x: x

def init_search(db, goal_label):
    """
    Sets up rules and initial step pile for given goal
    """
    # available rules before goal
    rules = {"wff": [], "|-": [], "all": []}
    for label, rule in db.rules.items():
        if label == goal_label: break

        # special cases based on mm conventions
        if label in ("idi", "a1ii"): continue # special rules only useful in mm proof assistants
        if label in ("4syl",): continue # new usage is discouraged

        if rule.consequent.tag not in ("$f", "$p", "$a"): continue
        typecode = rule.consequent.tokens[0]
        rules[typecode].append(rule)
        rules["all"].append(rule)

    # init pile
    steps = {"wff": {}, "|-": {}}
    goal_rule = db.rules[goal_label]

    # all subwffs
    token_sequences = [goal_rule.consequent.tokens] + [e.tokens for e in goal_rule.essentials]
    for tokens in token_sequences:
        tokens = ("wff",) + tuple(tokens[1:])
        success, rootstep = mb.backsearch(tokens, rules["wff"], disjoint=None, pile=None, max_depth=-1, verbose=False)
        assert success # should all be well-formed
        for step in rootstep.all_steps():
            steps["wff"][step.conclusion] = step

    # essential hypotheses
    for h in goal_rule.essentials:
        steps["|-"][tuple(h.tokens)], status = mp.perform(db.rules[h.label], {})
        assert status == ""

    return rules, steps

@profile
def closure_step(rules, steps):
    """
    One step of deductive closure
        rules[typecode]: list of rule objects
        steps[typecode][conc]: proof step with conclusion conc
    returns new_steps, same format as steps
    """
    new_steps = {"wff": {}, "|-": {}}
    for rule in rules["|-"]:
        # check if essentials contain all mandatories
        contained = len(rule.mandatory - set(sum([e.tokens for e in rule.essentials], []))) == 0
        
        # only match contained against |- steps in pile and backsearch wffs
        if contained:

            # schemes for hypotheses
            schemes = [Scheme(h.tokens, rule.mandatory & set(h.tokens)) for h in rule.hypotheses]
            schemes = standardize(schemes) # needed for multibinder to work correctly

            # try all essential matches
            for bindings, essential_dependencies in multibinder(schemes[len(rule.floatings):], steps["|-"]):

                # backsearch on floating hypotheses under binding
                floating_dependencies = []
                for s in schemes[:len(rule.floatings)]:
                    subgoal = s.substitute(bindings)
                    success, step = mb.backsearch(subgoal, rules["wff"], disjoint=None, pile=None, max_depth=-1, verbose=False)
                    if not success:
                        # print(f"backsearch failed on {' '.join(subgoal)}")
                        break
                    floating_dependencies.append(step)

                # if backsearch worked, update closure
                if len(floating_dependencies) == len(rule.floatings):
                    step, status = mp.perform(rule, tuple(floating_dependencies) + essential_dependencies)
                    assert status == "", status # if this point reached, rule should apply
                    new_steps["|-"][step.conclusion] = step # should all substeps including wffs also be added?                    

        # otherwise try performing rule on all pile wff combos
        else:
            # continue # skip for now, proliferates too many essentialless rule applications? but needed for a1i.

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
                assert status == "", status
                new_steps["|-"][step.conclusion] = step


    return new_steps

if __name__ == "__main__":

    from time import perf_counter
    import pickle as pk
    import metamathpy.setmm as ms
    db = ms.load_pl()

    # goal_label = "mp2"
    # goal_label = "mp2b"
    # goal_label = "a1i"
    # goal_label = "2a1i"
    # goal_label = "mp1i"
    # goal_label = "a2i"
    # goal_label = "mpd"
    # goal_label = "imim2i"
    # goal_label = "syl"
    # goal_label = "3syl"
    # goal_label = "4syl"
    # goal_label = "mpi"
    # goal_label = "mpisyl"

    goal_labels = [label for (label, rule) in db.rules.items() if rule.consequent.tag == "$p"]
    saved up to but not including 90: com45
    goal_times = []
    goal_proofs = []
    for gl, goal_label in enumerate(goal_labels):

        print(f"\n *** attempting {goal_label} ({gl} of {len(goal_labels)})... ***\n")
        start_time = perf_counter()
    
        rules, steps = init_search(db, goal_label)
        goal_tokens = tuple(db.rules[goal_label].consequent.tokens)
    
        # print("rules:")
        # for tc in rules.keys():
        #     print(f"{tc}: {' '.join(r.consequent.label for r in rules[tc])}")
    
        # print("initial pile:")
        # for tc in steps.keys():
        #     for conc, step in steps[tc].items():
        #         print(' '.join(conc))
    
        print(f"initial pile: {len(steps['|-'].keys())} |- steps")
    
        # two steps of deductive closure
        forsolved = backsolved = False
        for dstep in range(2):
            print(f"** dstep {dstep} **")
    
            # try backsearching against current pile
            backpile = steps["wff"] | steps["|-"]
            success, backstep = mb.backsearch(goal_tokens, rules["all"], disjoint=None, pile=backpile, max_depth=dstep+1, verbose=False)
            if success:
                backsolved = True
                print("backsolved!")
                break
    
            new_steps = closure_step(rules, steps)
            for conc, step in new_steps["|-"].items():
                if conc not in steps["|-"]:
                    steps["|-"][conc] = step
    
            print(f"{len(steps['|-'].keys())} current |- closure steps")
            # print("current closure steps:")
            # for conc in steps["|-"].keys(): print(' '.join(conc))
    
            # stop if goal is contained
            if goal_tokens in steps["|-"]:
                forsolved = True
                print("forsolved!")
                break

        total_time = perf_counter()-start_time

        # verify proof
        if forsolved or backsolved:
            claim = db.rules[goal_label]
            if forsolved:
                proof = steps["|-"][goal_tokens].normal_proof()
            else:
                proof = backstep.normal_proof()
            claim.consequent = md.Statement(claim.consequent.label, claim.consequent.tag, claim.consequent.tokens, proof)
            mp.verify_normal_proof(db, claim) # raises assertion error if unverified
            print("Verified!")
            print("proof: " + " ".join(proof))
            print(f"total time: {total_time:.3f}s")

            goal_times.append(total_time)
            goal_proofs.append(proof)
            with open("search_results.pkl", "wb") as f:
                pk.dump((goal_labels[:len(goal_times)], goal_times, goal_proofs), f)

        else:
            print("no proof found ...")
            break

    with open("search_results.pkl", "rb") as f:
        results = pk.load(f)
        for (label, time, proof) in zip(*results):
            print(f"{label} proved in {time:.3f}s: {' '.join(proof)}")

