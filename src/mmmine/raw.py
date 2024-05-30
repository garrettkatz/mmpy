# run from mmpy with $ python -m src.mmmine.raw
import sys
import os
import random
import itertools as it
import numpy as np
from time import perf_counter
from ..metamathpy import database as md
from ..metamathpy import proof as mp
from ..metamathpy import setmm as ms

# proof length and size (uncompressed)
def proof_metrics(root):
    size = len(root.conclusion)
    leng = 1
    for dep in root.dependencies.values():
        dsize, dleng = proof_metrics(dep)
        size += dsize
        leng += dleng
    return size, leng

if __name__ == "__main__":

    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    db = ms.load_imp()
    # db = ms.load_ni()
    # db = ms.load_pl()
    # db.print()

    # get axioms, split into wff and |-
    axioms = {"wff": {}, "|-": {}, "all": {}}
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$a":
            axioms[rule.consequent.tokens[0]][label] = rule
            axioms["all"][label] = rule
    ax_labels = tuple(axioms["all"].keys())

    # get all wff floating labels in standardized metamath order
    wff_labels = {} # label: rule
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$f" and rule.consequent.tokens[0] == "wff":
            # maintain original sort order
            if label not in wff_labels: wff_labels[label] = 1
    print(wff_labels.keys())

    # get all wff variable labels actually appearing in proofs, in case different
    wff_vars = {} # label: rule
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$p":
            root, _ = mp.verify_proof(db, rule)
            labels = set(wff_labels.keys()) & set(root.normal_proof())
            for label in labels:
                wff_vars[label] = db.rules[label]

    # sort wff_vars to standardized metamath order and discard unused floating labels
    wff_labels = tuple(label for label in wff_labels.keys() if label in wff_vars)
    wff_vars = {label: wff_vars[label] for label in wff_labels}

    print("axioms: " + " ".join(axioms["all"].keys()))
    print("metavars: " + " ".join(wff_labels))

    # all valid proofs (ending with singleton stacks)
    valid_proofs = {} # [proof string] = (proof step, proof length)

    # organize proof stacks by proof size
    stacks = {0: {(): []}} # [size][proof string] = stack

    for size in range(30):

        # skip sizes with no proofs
        if size not in stacks: continue

        print(f"size {size}: {len(valid_proofs)} valid proofs so far, {len(stacks[size])} frontier stacks")
        print(", ".join(f"{sz}:{len(stacks[sz])}" for sz in sorted(stacks.keys())))

        # try appending to all stacks of current size
        for proof, stack in stacks[size].items():

            # try every axiom
            try_labels = ax_labels

            # can also push a new metavariable floating hypothesis, in lexicographic order
            fl_idx = len(set(proof) & set(wff_labels))
            try_labels += wff_labels[:fl_idx+1]

            # try applying each rule
            for label in try_labels:

                new_proof = proof + (label,)
                new_stack = list(stack) # modified in-place
                new_step, msg = mp.conduct(db.rules[label], new_stack)

                # skip if invalid
                if msg != "": continue

                # replace top of stack with existing proof_step if trail is a valid proof
                for start in reversed(range(len(proof))):
                    trail = new_proof[start:]
                    if trail in valid_proofs:
                        (new_step, _) = valid_proofs[trail]
                        break

                # calculate the new proof size
                new_size = size + len(new_step.conclusion)
                if new_size not in stacks:
                    stacks[new_size] = {}

                # push the new step and save the new stack
                new_stack.append(new_step)
                stacks[new_size][new_proof] = new_stack

                # if new stack is singleton, new proof is valid; save it
                if len(new_stack) == 1:
                    valid_proofs[new_proof] = (new_step, new_size)
                    # print("new valid proof:", " ".join(new_proof), " ".join(new_step.conclusion))
   


    # # this method is too coarse iterations; itr 4 takes too long with too many combos

    # # start constructing raw proofs for wff and |=
    # proofs = {"wff": {}, "|-": {}} # proof string: proof_step
    # fails = set() # invalid proof strings

    # # initialize with hypothesis-less proofs (floating hypotheses)
    # proofs["wff"][wff_labels[:1]], msg = mp.perform(db.rules[wff_labels[0]], ())
    # assert msg == ""
    # print(proofs)

    # for itr in range(4):

    #     print(f"\n *** itr {itr}\n")

    #     # apply inferences to existing proofs
    #     new_proofs = {"wff": {}, "|-": {}}
    
    #     for key in axioms:
    #         for label, rule in axioms[key].items():
    #             wff_it = it.product(proofs["wff"], repeat=len(rule.floatings))
    #             ent_it = it.product(proofs["|-"], repeat=len(rule.essentials))


    #             # ! ONCe you commit to the wffs, just substitute into the essentials and they are already determined.
    #             # if you dict all conclusions so far, you can lookup immediately if essential has been proved, skip if not.
    
    #             for wff_proofs, ent_proofs in it.product(wff_it, ent_it):
    
    #                 # lexo substitutions
    
    #                 full_proof = tuple(lab for wff_proof in wff_proofs for lab in wff_proof)
    #                 full_proof += tuple(lab for ent_proof in ent_proofs for lab in ent_proof)
    #                 full_proof += (label,)
    
    #                 if full_proof in proofs[key]: continue
    #                 if full_proof in new_proofs[key]: continue
    #                 if full_proof in fails: continue
    
    #                 deps = tuple(proofs["wff"][wff_proof] for wff_proof in wff_proofs)
    #                 deps += tuple(proofs["|-"][ent_proof] for ent_proof in ent_proofs)
    #                 new_step, msg = mp.perform(rule, deps)
    
    #                 if msg != "":
    #                     fails.add(full_proof)
    #                 else:
    #                     new_proofs[key][full_proof] = new_step
    
    #     for key in proofs: proofs[key].update(new_proofs[key])
    #     # print(proofs)
    #     print(f"\n{len(proofs['wff'])} wff proofs, {len(proofs['|-'])} |- proofs")

    # concs = set()
    # sizes = {}
    # lengs = {}
    # for p, (proof, step) in enumerate(proofs["|-"].items()):
    #     print(p, " ".join(proof), " ".join(step.conclusion))
    #     if " ".join(step.conclusion) == "( ph -> ph )": input('!')
    #     concs.add(step.conclusion)
    #     sizes[step.conclusion], lengs[step.conclusion] = proof_metrics(step)

    # print(f"{len(concs)} distinct conclusions, {len(proofs['|-'])} distinct proofs, {len(fails)} invalid proofs")
    # print(f"max size, leng = {max(sizes.values())}, {max(lengs.values())}")



