# run from mmpy with $ python -m src.mmmine.scratch
import os
import random
import itertools as it
from time import perf_counter
from ..metamathpy import database as md
from ..metamathpy import proof as mp
from ..metamathpy import environment as me

def load_ni():
    # last label before any new boolean operator definitions is bijust, "rule" 441
    print('loading..')
    db = md.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"), max_rules=442)
    return db

def load_imp():
    # last label before any ax-3 proofs is loowoz, "rule" 264
    print('loading..')
    db = md.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"), max_rules=265)
    return db

def load_pl():

    # According to set.mm, prop logic has 194 axioms, definitions, and theorems, but this looks to be outdated.
    # last label before any FOL (universal quantifier) is xorexmid, it is "rule" 2849 (including hypotheses)
    print('loading..')
    db = md.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"), max_rules=2850)
    return db

if __name__ == "__main__":

    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    db = load_imp()
    # db = load_ni()
    # db = load_pl()
    # db.print()

    # # find stop point for sub-logics
    # for r, label in enumerate(db.rules.keys()):
    #     print(r, label)
    #     if label == "loowoz": break # load_imp
    #     # if label == "bijust": break # load_ni
    # input('..')

    # get axioms only, split into wff and |-
    wff_vars = {}
    axioms = {"wff": {}, "|-": {}}
    for r, (label, rule) in enumerate(db.rules.items()):
        # if rule.consequent.tag == "$f":
        #     wff_vars[label] = rule
        for hyp in rule.floatings:
            wff_vars[hyp.label] = db.rules[hyp.label]
        if rule.consequent.tag == "$a":
            axioms[rule.consequent.tokens[0]][label] = rule

    # implicational logic only
    axioms["wff"].pop("wn")
    axioms["|-"].pop("ax-3")

    print(f"\n*** wff vars ***\n")
    for v, (label, rule) in enumerate(wff_vars.items()):
        print(v, rule)
        print(f" {len(rule.hypotheses)} hypotheses")

    for key, axs in axioms.items():
        print(f"\n*** {key} ***\n")
        for a, (label, rule) in enumerate(axs.items()):
            print(a, rule)
            print(f" {len(rule.hypotheses)} hypotheses")

    # wff BFS is just too large, even at very shallow depth (12 -> 6k -> oom)
    # let's limit initial exploration as follows:
    # only essential hypotheses appearing in set.mm pl are terminals for the raw |- graph
    # only wffs appearing as proof steps in set.mm pl are nodes in the raw wff graph

    essential_labels = []
    essentials = {}
    step_wffs = {}
    proof_roots, proof_steps = {}, {}
    num_props = 0
    for label, rule in db.rules.items():

        if rule.consequent.tag != "$p": continue
        num_props += 1

        for hyp in rule.essentials:
            toks = tuple(hyp.tokens)
            essentials[toks] = essentials.get(toks, 0) + 1
            essential_labels.append(hyp.label)

        root, steps = mp.verify_proof(db, rule)
        for conclusion in steps.keys():
            wff = conclusion[1:]
            step_wffs[wff] = step_wffs.get(wff, 0) + 1

        proof_roots[label] = root
        proof_steps[label] = steps

    print(f"{len(essentials)} distinct essential hypotheses across {num_props} props")
    print(f"{len(step_wffs)} distinct wffs across {num_props} proofs")

    print("least|most frequent hypotheses:")
    sort_ess = sorted([(v,k) for (k,v) in essentials.items()])
    print(" ".join(sort_ess[0][1]))
    print(" ".join(sort_ess[-1][1]))

    print("least|most frequent wffs:")
    sort_wffs = sorted([(v,k) for (k,v) in step_wffs.items()])
    print(" ".join(sort_wffs[0][1]))
    print(" ".join(sort_wffs[-1][1]))

    # input('..')

    # fig, axs = pt.subplots(1,2, figsize=(6.5,2.5))
    # # axs[0].bar(range(len(essentials)), sorted(essentials.values()))
    # axs[0].plot(sorted(essentials.values()))
    # axs[0].set_xlabel("Essential hypothesis")
    # axs[0].set_ylabel("Occurrences in theorems")
    # axs[0].set_yscale('log')
    # # axs[1].bar(range(len(step_wffs)), sorted(step_wffs.values()))
    # axs[1].plot(sorted(step_wffs.values()))
    # axs[1].set_xlabel("Well-formed formula")
    # axs[1].set_ylabel("Occurences in proofs")
    # axs[1].set_yscale('log')
    # pt.tight_layout()
    # # pt.savefig("wff_freqs.png", dpi=600)
    # pt.savefig("wff_freqs.eps")
    # pt.show()

    # fig, axs = pt.subplots(1,1, figsize=(6.5,2.5))
    # axs = [axs] # 1,1
    # axs[0].hist(list(map(len, proof_steps.values())))
    # axs[0].set_xlabel("Proof length")
    # axs[0].set_ylabel("Frequence")
    # pt.tight_layout()
    # pt.savefig("proof_lens.eps")
    # pt.show()

    # still having trouble figuring out how to organize the search effectively.
    # different approach: forward search on valid proof strings.

    # ax_labels = essential_labels + list(axioms['wff'].keys()) + list(axioms["|-"].keys())
    ax_labels = list(axioms['wff'].keys()) + list(axioms["|-"].keys())
    fl_labels = list(wff_vars.keys()) # uncompressed proofs also push $f statements

    env = me.Environment(db)

    envs = {0: [env]}

    max_depth = 13
    for depth in range(max_depth):
        envs[depth+1] = []

        # try applying rules to each environment
        for e,env in enumerate(envs[depth]):

            # set up labels to try, don't skip floatings
            fl_so_far = set(env.proof) & set(fl_labels)
            if len(fl_so_far) == 0:
                fl_idx = 1
            else:
                fl_idx = max(map(fl_labels.index, fl_so_far))+2
            try_labels = ax_labels + fl_labels[:fl_idx]

            # try applying each rule
            for l,label in enumerate(try_labels):

                # skip envs with no hope of completing by max depth.
                # ax-mp is most-reducing rule; pops 4 and pushes 1, net -3
                # can only complete if current length <= 1 + 3*(max_depth-depth)
                # at max_depth-depth==1, at most 4 in stack
                # at max_depth-depth==2, at most 7 in stack
                # etc
                if len(env.stack) > 1 + 3*(max_depth - depth): continue

                # copy env and step
                new_env = env.copy()
                _, msg = new_env.step(label)

                # skip invalid steps
                if msg != "": continue

                # save new environment
                envs[depth+1].append(new_env)
                # print(f" env, label {e}, {l} of {len(envs[depth]), len(ax_labels)}")
            # print(f" env {e} of {len(envs[depth])}")

        print(f"depth {depth+1} envs: {len(envs[depth+1])}")

    for depth, envs_d in envs.items():
        print(f"depth {depth}: {len(envs_d)} envs")

    # Depth & Valid partial proofs \\
    # 1 & 6 \\
    # 2 & 42 \\
    # 3 & 402 \\
    # 4 & 3822 \\
    # 5 & 35358 \\
    # 6 & 326562 \\
    # 7 & 3023610 \\
    # 8 & 13806006

    # 0 & 1 \\
    # 1 & 1 \\
    # 2 & 3 \\
    # 3 & 16 \\
    # 4 & 86 \\
    # 5 & 485 \\
    # 6 & 2935 \\
    # 7 & 18956 \\
    # 8 & 129553 \\
    # 9 & 931517 \\
    # 10 & 6467657 \\
    # 11 & 14119609

    # 0 & 1 \\
    # 1 & 1 \\
    # 2 & 2 \\
    # 3 & 9 \\
    # 4 & 40 \\
    # 5 & 192 \\
    # 6 & 1000 \\
    # 7 & 5636 \\
    # 8 & 33929 \\
    # 9 & 216220 \\
    # 10 & 1447866 \\
    # 11 & 6576611 \\
    # 12 & 7564433 


    # extract all complete proofs
    proved = {}
    for depth, envs_d in envs.items():
        for env in envs_d:

            # complete means exactly one left on stack
            if len(env.stack) != 1: continue

            (step,) = env.stack
            conc = step.conclusion
            if conc not in proved: proved[conc] = []
            proved[conc].append(depth)

    ents = {k: v for (k,v) in proved.items() if k[0] == "|-"}

    print(f"{len(proved)} distinct conclusions proved")
    print(f"{len(ents)} are |- statements")
    print("some random ones:")
    for p, (conc, deps) in enumerate(random.sample(list(ents.items()), 20)):
        print(p, " ".join(conc), deps)
        if p == 20: break

    print("how many with exactly 1 proof?")
    print(len([v for v in ents.values() if len(v) == 1]))
    print("how many with > 1 proof?")
    print(len([v for v in ents.values() if len(v) > 1]))
    print("how many with different length proofs?")
    print(len([v for v in ents.values() if len(set(v)) > 1]))

    print("how many complete proofs at each depth?")
    proofs_at = {}
    for (conc, deps) in ents.items():
        for dep in deps:
            proofs_at[dep] = proofs_at.get(dep, 0) + 1

    for dep in sorted(proofs_at.keys()): print(dep, proofs_at[dep])
        


    # # BFS on wffs
    # max_depth = 2
    # explored_wffs = {}
    # for label, rule in wff_vars.items():
    #     tokens = tuple(rule.consequent.tokens)
    #     explored_wffs[" ".join(tokens)] = mp.ProofStep(tokens, rule)

    # print(f"\n *** depth 0: {len(explored_wffs)} ***")
    # print(explored_wffs)

    # for depth in range(max_depth):
    #     more_wffs = {}
    #     for (label, rule) in axioms["wff"].items():
    #         hyps = len(rule.hypotheses)
    #         for deps in it.product(explored_wffs.values(), repeat=hyps):
    #             step, msg = mp.perform(rule, deps)
    #             assert msg == ""
    #             more_wffs[" ".join(step.conclusion)] = step
    #     explored_wffs.update(more_wffs)

    #     print(f"\n *** depth {depth+1}: {len(explored_wffs)} ***")
    #     # print(explored_wffs)

    # # a = 0
    # # for r, (label, rule) in enumerate(db.rules.items()):
    # #     if rule.consequent.tag != "$a": continue
    # #     print(a, rule)
    # #     a += 1

    # # db.dump("")
    
    # # proof_roots = {}
    # # proof_steps = {}
    
    # # # According to set.mm, prop logic has 194 axioms, definitions, and theorems, but this looks to be outdated.
    # # # last label before any FOL (universal quantifier) is xorexmid, it is "rule" 2849 (including hypotheses)
    # # last_pl = "xorexmid"
    
    # # for r, (label, rule) in enumerate(db.rules.items()):
    
    # #     if rule.consequent.tag == "$p":
    # #         print(r,label,rule)
    # #         root, steps = mp.verify_proof(db, rule)
    # #         proof_roots[label] = root
    # #         proof_steps[label] = steps
    
    # #     if label == last_pl: break
    
    
    # # print('num pl', num_pl)
    # # # stats on number of proof steps?
    # # print('num proofs', len(proof_steps))
    # # print('shortest proof', min(map(len, proof_steps.values())))
    # # print('longest proof', max(map(len, proof_steps.values())))
    # # print('total proof steps', sum(map(len, proof_steps.values())))
    
    # # # how many proof steps are redundant?
    # # distinct_steps = {}
    # # for label, steps in proof_steps.items():
    # #     hyps = tuple(" ".join(hyp.tokens) for hyp in db.rules[label].hypotheses)
    # #     for step_conclusion in steps.keys():
    # #         key = (" ".join(step_conclusion),) + hyps
    # #         if key not in distinct_steps: distinct_steps[key] = []
    # #         distinct_steps[key].append(label)
    
    # # print('distinct', len(distinct_steps))
    
    
