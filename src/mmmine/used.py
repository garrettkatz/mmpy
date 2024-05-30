# run from mmpy with $ python -m src.mmmine.used
import sys
import os
import random
import pickle as pk
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

    do_count = False

    if do_count:

        # db = ms.load_pl()
        db = ms.load_all()

        theorem_labels = set()
        definition_labels = set()
        proof_lengths = {}
        form_lengths = {}
        label_counts = {}
        for r, (label, rule) in enumerate(db.rules.items()):
            print(f"rule {r} ({label}) of {len(db.rules)}...")

            # definitions are axioms
            if rule.consequent.tag == "$a" and label[:3] == "df-":
                definition_labels.add(label)

            # only look at proofs of propositions
            if rule.consequent.tag != "$p": continue

            # save labels of theorems
            theorem_labels.add(label)
    
            # uncompress proof
            root, steps = mp.verify_proof(db, rule)

            # track metrics
            # proof = root.normal_proof()
            # proof_lengths[len(proof)] = 1 + proof_lengths.get(len(proof), 0)
            proof_lengths[len(steps)] = 1 + proof_lengths.get(len(steps), 0)
            for step in steps.values():
                form_lengths[len(step.conclusion)] = 1 + form_lengths.get(len(step.conclusion), 0)

                lab = step.rule.consequent.label
                label_counts[lab]  = 1 + label_counts.get(lab, 0)

            # for lab in proof:
            #     label_counts[lab]  = 1 + label_counts.get(lab, 0)
    
        with open("used.pkl", "wb") as f:
            pk.dump((label_counts, theorem_labels, definition_labels, proof_lengths, form_lengths), f)

    with open("used.pkl", "rb") as f:
        label_counts, theorem_labels, definition_labels, proof_lengths, form_lengths = pk.load(f)

    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    # limit to labels of actual theorems and definitions
    thm_counts = {k:v for (k,v) in label_counts.items() if k in theorem_labels}
    def_counts = {k:v for (k,v) in label_counts.items() if k in definition_labels}

    print("theorems:")
    count_labels = sorted([(v,k) for (k,v) in thm_counts.items()])
    print(count_labels[:10])
    print(count_labels[-10:])

    print("definitions:")
    count_labels = sorted([(v,k) for (k,v) in def_counts.items()])
    print(count_labels[:10])
    print(count_labels[-10:])

    # print("form lengths:")
    # print(form_lengths)

    # calculate total formulation size
    formulation_size = 0
    for form_leng, count in form_lengths.items():
        formulation_size += form_leng * count
    print("Total formulation size:", formulation_size)

    # bucket the proof and form lengths
    pbs = 100
    for leng in sorted(proof_lengths.keys()):
        if leng % pbs == 0:
            continue
        num = proof_lengths.pop(leng)
        key = pbs * (leng // pbs)
        if key not in proof_lengths: proof_lengths[key] = 0
        proof_lengths[key] += num
    fbs = 350
    for leng in sorted(form_lengths.keys()):
        if leng % fbs == 0:
            continue
        num = form_lengths.pop(leng)
        key = fbs * (leng // fbs)
        if key not in form_lengths: form_lengths[key] = 0
        form_lengths[key] += num

    pt.figure(figsize=(8,2.5))
    pt.subplot(1,2,1)
    pt.plot(sorted(thm_counts.values()))
    pt.xlabel("Theorem")
    pt.ylabel("Usage")
    pt.yscale('log')
    pt.subplot(1,2,2)
    pt.plot(sorted(def_counts.values()))
    pt.xlabel("Definition")
    # pt.ylabel("Usage")
    pt.yscale('log')
    pt.tight_layout()
    pt.savefig("usage.eps")
    pt.show()

    pt.figure(figsize=(8,2.5))
    pt.subplot(1,2,1)
    pt.bar(list(proof_lengths.keys()), list(proof_lengths.values()), width=.8*pbs)
    pt.xlabel("Proof length")
    pt.ylabel("Frequency")
    pt.yscale('log')
    pt.subplot(1,2,2)
    pt.bar(list(form_lengths.keys()), list(form_lengths.values()), width=.8*fbs)
    pt.xlabel("Formula length")
    pt.yscale('log')
    # pt.xscale('log')
    pt.tight_layout()
    pt.savefig("sizing.eps")
    pt.show()

