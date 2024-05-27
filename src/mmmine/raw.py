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

    print("axioms: " + " ".join(k for axs in axioms.values() for k in axs.keys()))
    print("metavars: " + " ".join(wff_labels))

    # start constructing raw proofs for wff and |=
    proofs = {"wff": {}, "|-": {}} # proof string: proof_step
    fails = set() # invalid proof strings

    # initialize with hypothesis-less proofs (floating hypotheses)
    proofs["wff"][wff_labels[:1]], msg = mp.perform(db.rules[wff_labels[0]], ())
    assert msg == ""
    print(proofs)

    for itr in range(3):

        print(f"\n *** itr {itr}\n")

        # apply inferences to existing proofs
        new_proofs = {"wff": {}, "|-": {}}
    
        for key in axioms:
            for label, rule in axioms[key].items():
                wff_it = it.product(proofs["wff"], repeat=len(rule.floatings))
                ent_it = it.product(proofs["|-"], repeat=len(rule.essentials))


                ! ONCe you commit to the wffs, just substitute into the essentials and they are already determined.
                if you dict all conclusions so far, you can lookup immediately if essential has been proved, skip if not.
    
                for wff_proofs, ent_proofs in it.product(wff_it, ent_it):
    
                    # lexo substitutions
    
                    full_proof = tuple(lab for wff_proof in wff_proofs for lab in wff_proof)
                    full_proof += tuple(lab for ent_proof in ent_proofs for lab in ent_proof)
                    full_proof += (label,)
    
                    if full_proof in proofs[key]: continue
                    if full_proof in new_proofs[key]: continue
                    if full_proof in fails: continue
    
                    deps = tuple(proofs["wff"][wff_proof] for wff_proof in wff_proofs)
                    deps += tuple(proofs["|-"][ent_proof] for ent_proof in ent_proofs)
                    new_step, msg = mp.perform(rule, deps)
    
                    if msg != "":
                        fails.add(full_proof)
                    else:
                        new_proofs[key][full_proof] = new_step
    
        for key in proofs: proofs[key].update(new_proofs[key])
        # print(proofs)
        print(f"\n{len(proofs['wff'])} wff proofs, {len(proofs['|-'])} |- proofs")

    concs = set()
    for p, (proof, step) in enumerate(proofs["|-"].items()):
        print(p, " ".join(proof), " ".join(step.conclusion))
        if " ".join(step.conclusion) == "( ph -> ph )": input('!')
        concs.add(step.conclusion)

    print(f"{len(concs)} distinct conclusions, {len(proofs['|-'])} distinct proofs, {len(fails)} invalid proofs")



