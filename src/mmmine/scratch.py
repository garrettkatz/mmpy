# run from mmpy with $ python -m src.mmmine.scratch
import sys
import os
import random
import itertools as it
import numpy as np
from time import perf_counter
from ..metamathpy import database as md
from ..metamathpy import proof as mp
from ..metamathpy import environment as me
from ..metamathpy import setmm as ms

if __name__ == "__main__":

    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    db = ms.load_imp()
    # db = ms.load_ni()
    # db = ms.load_pl()
    # db.print()

    # get axioms, split into wff and |-
    axioms = {"wff": {}, "|-": {}}
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$a":
            axioms[rule.consequent.tokens[0]][label] = rule

    # get all wff floating labels
    wff_labels = {}
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$f" and rule.consequent.tokens[0] == "wff":
            # maintain original sort order
            if label not in wff_labels: wff_labels[label] = 1
    print(wff_labels.keys())

    # get all wff variable labels appearing in proofs
    wff_vars = {}
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$p":
            root, _ = mp.verify_proof(db, rule)
            labels = set(wff_labels.keys()) & set(root.normal_proof())
            for label in labels:
                wff_vars[label] = db.rules[label]

    # sort wff vars for lexicographic enumeration
    # fl_labels = list(wff_vars.keys())
    # fl_labels = sorted(wff_vars.keys())
    wff_labels = tuple(label for label in wff_labels.keys() if label in wff_vars)
    wff_vars = {label: wff_vars[label] for label in wff_labels}

    print("axioms: " + " ".join(k for axs in axioms.values() for k in axs.keys()))
    print("metavars: " + " ".join(wff_labels))

    # make base proof steps for metavars
    wff_steps = {label: mp.perform(db.rules[label], ()) for label in wff_labels}
    print("wff steps: ", wff_steps)

    # # initialize base of theory dag, starting with floating wffs
    # wff_nodes = {}
    # for label, rule in wff_vars.items():
    #     step, msg = mp.perform(rule, ())
    #     proof = step.normal_proof()
    #     metavars = tuple(set(wff_labels) & set(proof))
    #     wff_nodes[proof] = (step, metavars)

    # print("\n*** wff nodes ***\n")
    # for proof, (step, metavars) in wff_nodes.items():
    #     print('step:', step)
    #     print('metavars:', metavars)
    #     print('proof:', proof)

    # input('.')

    # ent_nodes = {}

    # # apply one round of inference
    # new_nodes = {}

    # # try each rule
    # for rule in axioms["wff"].values():

    #     # try each combination of dependencies
    #     for fdeps in it.product(wff_nodes.values(), repeat=len(rule.floatings)):

    #         fdeps, metavars = zip(*fdeps)

    #         # skip combinations where metavars are not lexicographic
    #         lexo = True
    #         for d in range(1,len(metavars)+1):
    #             mv = set([v for mv in metavars[:d] for v in mv])
    #             if mv != set(wff_labels[:len(mv)]):
    #                 lexo = False
    #                 break
    #         if not lexo: continue

    #         # attempt rule on dependencies, continue if invalid
    #         node, msg = mp.perform(rule, fdeps)
    #         if msg != "": continue
            
    #         # save result
    #         new_nodes[node.normal_proof()] = node            

    #     # in raw graph, only ax-mp has essentials, so shortcut the possible dependencies

    # print("\n*** new nodes ***\n")
    # for proof, node in new_nodes.items():
    #     print('node:', node)
    #     print('proof:', proof)


    ### some stats about the database

    # for label, rule in db.rules.items():

    #     if rule.consequent.tag != "$p": continue
    #     num_props += 1

    #     for hyp in rule.essentials:
    #         toks = tuple(hyp.tokens)
    #         essentials[toks] = essentials.get(toks, 0) + 1
    #         essential_labels.append(hyp.label)

    #     print(label, rule)
    #     root, steps = mp.verify_proof(db, rule)
    #     for conclusion in steps.keys():
    #         wff = conclusion[1:]
    #         step_wffs[wff] = step_wffs.get(wff, 0) + 1

    #     proof_roots[label] = root
    #     proof_steps[label] = steps

    # print(f"\n*** wff vars ***\n")
    # for v, (label, rule) in enumerate(wff_vars.items()):
    #     print(v, rule)
    #     print(f" {len(rule.hypotheses)} hypotheses")

    # for key, axs in axioms.items():
    #     print(f"\n*** {key} ***\n")
    #     for a, (label, rule) in enumerate(axs.items()):
    #         print(a, rule)
    #         print(f" {len(rule.hypotheses)} hypotheses")

    # # wff BFS is just too large, even at very shallow depth (12 -> 6k -> oom)
    # # let's limit initial exploration as follows:
    # # only essential hypotheses appearing in set.mm pl are terminals for the raw |- graph
    # # only wffs appearing as proof steps in set.mm pl are nodes in the raw wff graph

    # essential_labels = []
    # essentials = {}
    # step_wffs = {}
    # proof_roots, proof_steps = {}, {}
    # num_props = 0
    # for label, rule in db.rules.items():

    #     if rule.consequent.tag != "$p": continue
    #     num_props += 1

    #     for hyp in rule.essentials:
    #         toks = tuple(hyp.tokens)
    #         essentials[toks] = essentials.get(toks, 0) + 1
    #         essential_labels.append(hyp.label)

    #     print(label, rule)
    #     root, steps = mp.verify_proof(db, rule)
    #     for conclusion in steps.keys():
    #         wff = conclusion[1:]
    #         step_wffs[wff] = step_wffs.get(wff, 0) + 1

    #     proof_roots[label] = root
    #     proof_steps[label] = steps

    # print(f"{len(essentials)} distinct essential hypotheses across {num_props} props")
    # print(f"{len(step_wffs)} distinct wffs across {num_props} proofs")

    # print("least|most frequent hypotheses:")
    # sort_ess = sorted([(v,k) for (k,v) in essentials.items()])
    # print(" ".join(sort_ess[0][1]))
    # print(" ".join(sort_ess[-1][1]))

    # print("least|most frequent wffs:")
    # sort_wffs = sorted([(v,k) for (k,v) in step_wffs.items()])
    # print(" ".join(sort_wffs[0][1]))
    # print(" ".join(sort_wffs[-1][1]))

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

    ### still having trouble figuring out how to organize the search effectively.
    ### different approach: forward search on valid proof strings.

    ax_labels = tuple(list(axioms['wff'].keys()) + list(axioms["|-"].keys()))

    env = me.Environment(db)

    envs = {0: [env]}

    max_depth = int(sys.argv[1]) #11
    for depth in range(max_depth):
        envs[depth+1] = []

        # try applying rules to each environment
        for e,env in enumerate(envs[depth]):

            # try every axiom
            try_labels = ax_labels

            # can also push previous proof steps
            try_labels += tuple(n for (n,lab) in enumerate(env.proof) if type(lab) is str)

            # can also push a new metavariable floating hypothesis, in lexicographic order
            fl_idx = len(set(env.proof) & set(wff_labels))
            try_labels += wff_labels[fl_idx:fl_idx+1]

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

                # skip non-int labels that reconstruct a previous proof step
                if type(label) is str:
                    step_proofs = [step.normal_proof() for step in new_env.steps]
                    if step_proofs[-1] in set(step_proofs[:-1]): continue

                # save new environment
                envs[depth+1].append(new_env)
                # print(f" env, label {e}, {l} of {len(envs[depth]), len(ax_labels)}")
            # print(f" env {e} of {len(envs[depth])}")

        print(f"depth {depth+1} envs: {len(envs[depth+1])}")

    for depth, envs_d in envs.items():
        print(f"depth {depth}: {len(envs_d)} envs")


    # ## OLD approach without proof backpointers    

    # # ax_labels = essential_labels + list(axioms['wff'].keys()) + list(axioms["|-"].keys())
    # ax_labels = list(axioms['wff'].keys()) + list(axioms["|-"].keys())
    # wff_labels = list(wff_vars.keys()) # uncompressed proofs also push $f statements

    # env = me.Environment(db)

    # envs = {0: [env]}

    # max_depth = 6
    # for depth in range(max_depth):
    #     envs[depth+1] = []

    #     # try applying rules to each environment
    #     for e,env in enumerate(envs[depth]):

    #         # set up labels to try, don't skip floatings
    #         fl_so_far = set(env.proof) & set(wff_labels)
    #         if len(fl_so_far) == 0:
    #             fl_idx = 1
    #         else:
    #             fl_idx = max(map(wff_labels.index, fl_so_far))+2
    #         try_labels = ax_labels + wff_labels[:fl_idx]

    #         # try applying each rule
    #         for l,label in enumerate(try_labels):

    #             # skip envs with no hope of completing by max depth.
    #             # ax-mp is most-reducing rule; pops 4 and pushes 1, net -3
    #             # can only complete if current length <= 1 + 3*(max_depth-depth)
    #             # at max_depth-depth==1, at most 4 in stack
    #             # at max_depth-depth==2, at most 7 in stack
    #             # etc
    #             if len(env.stack) > 1 + 3*(max_depth - depth): continue

    #             # copy env and step
    #             new_env = env.copy()
    #             _, msg = new_env.step(label)

    #             # skip invalid steps
    #             if msg != "": continue

    #             # save new environment
    #             envs[depth+1].append(new_env)
    #             # print(f" env, label {e}, {l} of {len(envs[depth]), len(ax_labels)}")
    #         # print(f" env {e} of {len(envs[depth])}")

    #     print(f"depth {depth+1} envs: {len(envs[depth+1])}")

    # for depth, envs_d in envs.items():
    #     print(f"depth {depth}: {len(envs_d)} envs")

    # # Depth & Valid partial proofs \\
    # # 1 & 6 \\
    # # 2 & 42 \\
    # # 3 & 402 \\
    # # 4 & 3822 \\
    # # 5 & 35358 \\
    # # 6 & 326562 \\
    # # 7 & 3023610 \\
    # # 8 & 13806006

    # # 0 & 1 \\
    # # 1 & 1 \\
    # # 2 & 3 \\
    # # 3 & 16 \\
    # # 4 & 86 \\
    # # 5 & 485 \\
    # # 6 & 2935 \\
    # # 7 & 18956 \\
    # # 8 & 129553 \\
    # # 9 & 931517 \\
    # # 10 & 6467657 \\
    # # 11 & 14119609

    # # 0 & 1 \\
    # # 1 & 1 \\
    # # 2 & 2 \\
    # # 3 & 9 \\
    # # 4 & 40 \\
    # # 5 & 192 \\
    # # 6 & 1000 \\
    # # 7 & 5636 \\
    # # 8 & 33929 \\
    # # 9 & 216220 \\
    # # 10 & 1447866 \\
    # # 11 & 6576611 \\
    # # 12 & 7564433 


    # extract all complete proofs
    proved = {}
    proofs = {}
    for depth, envs_d in envs.items():
        for e, env in enumerate(envs_d):

            # complete means exactly one left on stack
            if len(env.stack) != 1: continue

            (step,) = env.stack
            conc = step.conclusion
            if conc not in proved: proved[conc] = []
            proved[conc].append((depth,e))
            proofs[conc] = step.normal_proof()

    ents = {k: v for (k,v) in proved.items() if k[0] == "|-"}

    print(f"{len(proved)} distinct conclusions proved")
    print(f"{len(ents)} are |- statements")
    print("some random ones:")
    for p, (conc, pts) in enumerate(random.sample(list(ents.items()), min(len(ents), 10))):
        deps, idxs = zip(*pts)
        print(p, " ".join(conc), list(deps), idxs)

    print("how many with exactly 1 proof?")
    print(len([v for v in ents.values() if len(v) == 1]))
    print("how many with > 1 proof?")
    print(len([v for v in ents.values() if len(v) > 1]))
    print("how many with different length proofs?")
    print(len([v for v in ents.values() if len(set(list(zip(*v))[0])) > 1]))

    print("how many complete proofs at each depth?")
    proofs_at = {}
    for (conc, pts) in ents.items():
        deps, idxs = zip(*pts)
        for dep in deps:
            proofs_at[dep] = proofs_at.get(dep, 0) + 1

    for dep in sorted(proofs_at.keys()): print(dep, proofs_at[dep])

    # 3 & 2 \\
    # 4 & 5 \\
    # 5 & 12 \\
    # 6 & 62 \\
    # 7 & 119 \\
    # 8 & 936 \\
    # 9 & 1659 \\
    # 10 & 17612 


    # show two proofs for same claim
    print("2 different proofs:")
    for (conc, pts)in ents.items():
        if len(pts) == 1: continue

        print(" ".join(conc))
        for d,e in pts:
            print(envs[d][e].proof)        

        break
    print()

    # check that as long as there are no claims with multiple proofs, is every proof_step a distinct conclusion?
    all_steps = {} # memory address -> step object
    for depth, envs_d in envs.items():
        for e, env in enumerate(envs_d):
            for step in env.steps:
                all_steps[id(step)] = step
                # print(depth,e,id(step),step)

    all_concs = set()
    for sid, step in all_steps.items():
        all_concs.add(step.conclusion)
        # print(sid, " ".join(step.conclusion))

    # This check is wrong!! different environments can duplicate "wff ps" used at different times during the different proofs.
    print(f"Surprise: {len(all_concs)} distinct conclusions != {len(all_steps)} distinct steps in memory")

    # print("the normal proofs themselves:")
    # for (conc, proof) in proofs.items():
    #     print(" ".join(conc))
    #     print("   ", " ".join(proof))

    # for each proof, count how many other proofs use it.
    # another proof "uses" it if its normal proof is a substring of the other proof,
    # and the other proof has one more stack entry after the subsequence than before
    # in fact, given that it itself is a valid proof, the second condition is already implied.
    # (of course, shallower steps will be used by more, but within layer?)
    # (can you say anything stronger past max_depth?  will all proof steps eventually be used equally?)
    # (something like the exponential(?) growth rate of superproofs that use each theorem?)

    print("\n*** depth containment relations:\n")

    subdeps, superdeps = {}, {}
    for (conc, prf1), prf2 in it.product(proofs.items(), proofs.values()):
        if len(prf1) >= len(prf2): continue
        
        if conc not in subdeps:
            subdeps[conc] = len(prf1)
            superdeps[conc] = []

        if " ".join(prf1) in " ".join(prf2):
            superdeps[conc].append(len(prf2))

    # for conc in subdeps:
    #     # if len(superdeps[conc]) == 0: continue
    #     # if conc[0] == "wff": continue
    #     print(subdeps[conc], ": ", " ".join(conc))
    #     print("is in:", superdeps[conc])

    # scatdat = np.array([(subdeps[conc], d) for conc in subdeps for d in superdeps[conc]])
    # x, y = (scatdat + .5*np.random.rand(*scatdat.shape)).T
    # pt.plot(x, y, 'k.')

    histdat = np.array([(subdeps[conc], len(superdeps[conc])) for conc in subdeps])
    deps = [d for d in range(2,max_depth+1) if (histdat[:,0] == d).any() and (histdat[histdat[:,0]==d,1] > 0).any()]
    fig, axs = pt.subplots(1, len(deps), figsize=(6.5,2))
    for d,dep in enumerate(deps):
        idx = histdat[:,0] == dep
        axs[d].hist(histdat[idx,1])#, bins = np.arange(histdat[idx,1].max()+1)-.5)
        axs[d].set_title(f"Proof length {dep}")
        if d > 0: axs[d].set_yscale("log")
    fig.supxlabel("Number of superproofs")
    fig.supylabel("Frequency")
    pt.tight_layout()
    pt.savefig("superproofs.eps")
    pt.show()

    # containers = {}
    # for d1 in range(max_depth);
    #     for env1 in envs[d1]:
    #         (step,) = env1.stack
    #         subconc = step.conclusion
    #         subproof = step.normal_proof()
    #         for d2 in range(1,max_depth+1):
    #             for env2 in envs[d2]:
    #                 (step,) = env2.stack
    #                 superproof = step.normal_proof()

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
    
    
