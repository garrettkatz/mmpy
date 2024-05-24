# run from mmpy with $ python -m src.mmmine.scratch
import os
import itertools as it
from time import perf_counter
from ..metamathpy import database as md
from ..metamathpy import proof as mp

def load_pl():

    # According to set.mm, prop logic has 194 axioms, definitions, and theorems, but this looks to be outdated.
    # last label before any FOL (universal quantifier) is xorexmid, it is "rule" 2849 (including hypotheses)
    print('loading..')
    db = md.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"), max_rules=2850)
    return db

if __name__ == "__main__":

    db = load_pl()
    # db.print()

    # get axioms only, split into wff and |-
    wff_vars = {}
    axioms = {"wff": {}, "|-": {}}
    inf_axioms = {}
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$f":
            wff_vars[label] = rule
        if rule.consequent.tag == "$a":
            axioms[rule.consequent.tokens[0]][label] = rule

    print(f"\n*** wff vars ***\n")
    for v, (label, rule) in enumerate(wff_vars.items()):
        print(v, rule)

    for key, axs in axioms.items():
        print(f"\n*** {key} ***\n")
        for a, (label, rule) in enumerate(axs.items()):
            print(a, rule)

    # BFS on wffs
    max_depth = 2
    explored_wffs = {}
    for label, rule in wff_vars.items():
        tokens = tuple(rule.consequent.tokens)
        explored_wffs[" ".join(tokens)] = mp.ProofStep(tokens, rule)

    print(f"\n *** depth 0: {len(explored_wffs)} ***")
    print(explored_wffs)

    for depth in range(max_depth):
        more_wffs = {}
        for (label, rule) in axioms["wff"].items():
            hyps = len(rule.hypotheses)
            for deps in it.product(explored_wffs.values(), repeat=hyps):
                step, msg = mp.perform(rule, deps)
                assert msg == ""
                more_wffs[" ".join(step.conclusion)] = step
        explored_wffs.update(more_wffs)

        print(f"\n *** depth {depth}: {len(explored_wffs)} ***")
        # print(explored_wffs)

    
        


    # a = 0
    # for r, (label, rule) in enumerate(db.rules.items()):
    #     if rule.consequent.tag != "$a": continue
    #     print(a, rule)
    #     a += 1

    # db.dump("")
    
    # proof_roots = {}
    # proof_steps = {}
    
    # # According to set.mm, prop logic has 194 axioms, definitions, and theorems, but this looks to be outdated.
    # # last label before any FOL (universal quantifier) is xorexmid, it is "rule" 2849 (including hypotheses)
    # last_pl = "xorexmid"
    
    # for r, (label, rule) in enumerate(db.rules.items()):
    
    #     if rule.consequent.tag == "$p":
    #         print(r,label,rule)
    #         root, steps = mp.verify_proof(db, rule)
    #         proof_roots[label] = root
    #         proof_steps[label] = steps
    
    #     if label == last_pl: break
    
    
    # print('num pl', num_pl)
    # # stats on number of proof steps?
    # print('num proofs', len(proof_steps))
    # print('shortest proof', min(map(len, proof_steps.values())))
    # print('longest proof', max(map(len, proof_steps.values())))
    # print('total proof steps', sum(map(len, proof_steps.values())))
    
    # # how many proof steps are redundant?
    # distinct_steps = {}
    # for label, steps in proof_steps.items():
    #     hyps = tuple(" ".join(hyp.tokens) for hyp in db.rules[label].hypotheses)
    #     for step_conclusion in steps.keys():
    #         key = (" ".join(step_conclusion),) + hyps
    #         if key not in distinct_steps: distinct_steps[key] = []
    #         distinct_steps[key].append(label)
    
    # print('distinct', len(distinct_steps))
    
    
