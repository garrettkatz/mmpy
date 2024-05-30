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

def sample_formulation(db, sample_size, verbose=False):

    # collect all the theorem labels
    thm_labels = set()
    for label, rule in db.rules.items():
        if rule.consequent.tag == "$p":
            thm_labels.add(label)

    if verbose: print(f"{len(thm_labels)} theorems total")

    # sub-sample some theorem labels
    sample_labels = set(random.sample(list(thm_labels), sample_size))
    if verbose: print(sample_labels)

    # populate all labels of formulation
    formulation_labels = set()

    # recursive helper to add all other rules used in sample's proofs
    # modifies formulation_labels in place
    def add_all(label):

        # if label already included, don't repeat
        if label in formulation_labels: return

        # include current label
        formulation_labels.add(label)

        # only recurse on labels of propositions
        rule = db.rules[label]
        if rule.consequent.tag != "$p": return

        # expand proof to get all other rules it needs
        root, steps = mp.verify_proof(db, rule)

        # recurse on rules used to justify each step
        for step in steps.values():
            add_all(step.rule.consequent.label)

    # use recursive helper on every sampled label
    for i,label in enumerate(sample_labels):
        if verbose: print(i, label, len(formulation_labels))
        add_all(label)

    # now formulation labels are populated, return
    return formulation_labels

def formulation_size(db, formulation_labels):
    # tally size over all steps of all proofs
    size = 0
    for label in formulation_labels:
        rule = db.rules[label]

        # only propositions have proof, otherwise skip
        if rule.consequent.tag != "$p": continue 

        # generate proof steps
        root, steps = mp.verify_proof(db, rule)

        # add up step lengths, conclusions are keys
        for conclusion in steps: size += len(conclusion)

    return size

if __name__ == "__main__":

    db = ms.load_pl()
    # db = ms.load_all()

    num_samples = 100
    sample_size = 30

    samples = []
    for s in range(num_samples):
        formulation_labels = sample_formulation(db, sample_size)
        samples.append(formulation_labels)
        print(f"{s}: {len(formulation_labels)} labels in formulation")

    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    pt.figure(figsize=(8,2.5))
    pt.subplot(1,2,1)
    pt.hist(list(map(len, samples)), rwidth=.8)
    pt.xlabel("Rules in formulation")
    pt.ylabel("Frequency")

    pt.subplot(1,2,2)
    pt.hist([formulation_size(db, sample) for sample in samples], rwidth=.8)
    pt.xlabel("Formulation size")
    # pt.ylabel("Frequency")

    pt.tight_layout()
    pt.savefig("formsamples.eps")
    pt.show()

