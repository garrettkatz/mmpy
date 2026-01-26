# run from mmpy with $ python -m src.mmmine.raw_heuristic
import sys
import os
import random
import itertools as it
import numpy as np
from time import perf_counter
from collections import deque
from ..metamathpy import database as md
from ..metamathpy import proof as mp
from ..metamathpy import setmm as ms

if __name__ == "__main__":

    max_proofs = 500_000
    max_queued = 5_000_000

    # import matplotlib.pyplot as pt
    # from matplotlib import rcParams
    # rcParams["font.family"] = "serif"

    # db = ms.load_imp()
    db = ms.load_ni()

    # get axioms, split into wff and |-
    axioms = {"wff": {}, "|-": {}, "all": {}}
    for r, (label, rule) in enumerate(db.rules.items()):
        if rule.consequent.tag == "$a":
            # axioms type specific
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

    print("axioms: " + " ".join(f"{label}[{len(axioms['all'][label].hypotheses)}]" for label in axioms["all"].keys()))
    print("metavars: " + " ".join(wff_labels))
    input("Enter to start search...")

    # set up queues of partial proofs
    # queues[k][n] = (label sequence, stack) for nth partial proof of priority k
    # priority is label sequence length (L) + heuristic (x)
    # x = ceil( (S-1) / (H-1) ), where S is stack length and H is the maximum hypothesis count for any axiom
    # this ensures "admissibility" (at least x more inference steps will be needed for a complete proof)
    queues = {0: deque([((), [])])}
    H = max(len(rule.hypotheses) for rule in axioms["all"].values())
    num_queued = 1

    # set up storage of complete proofs and proved statements
    # complete_proofs[label_sequence] = conclusion proof step
    complete_proofs = {}
    proven_statements = {}

    # start queue-based proof search
    while True:
        # stopping criteria
        if len(complete_proofs) >= max_proofs: break
        if num_queued >= max_queued: break

        # pop next partial proof (infinitely many proofs so there will always be at least one)
        k = min([k for k,v in queues.items() if len(v)>0])
        label_sequence, stack = queues[k].popleft()

        # try applying every axiom
        try_labels = ax_labels

        # can also push a new metavariable floating hypothesis, in lexicographic order
        fl_idx = len(set(label_sequence) & set(wff_labels))
        try_labels += wff_labels[:fl_idx+1]

        # try applying each rule
        for label in try_labels:

            new_label_sequence = label_sequence + (label,)
            new_stack = list(stack) # modified in-place
            new_step, msg = mp.conduct(db.rules[label], new_stack)

            # skip if invalid
            if msg != "": continue

            # push the new step
            new_stack.append(new_step)

            # calculate priority for new partial proof
            L = len(new_label_sequence)
            S = len(new_stack)
            x = int(np.ceil( (S-1) / (H-1) ))
            k = L + x
            if k not in queues: queues[k] = deque()

            # update the search queues
            new_entry = (new_label_sequence, new_stack)
            queues[k].append(new_entry)
            num_queued += 1

            # if new stack is singleton, new proof is valid; save it along with the proven statement
            if len(new_stack) == 1:
                complete_proofs[new_label_sequence] = new_step
                conclusion = ' '.join(new_step.conclusion)

                if conclusion not in proven_statements:
                    proven_statements[conclusion] = []
                proven_statements[conclusion].append(new_label_sequence)

                print(f"proof {len(complete_proofs)} [{num_queued} queued, {len(proven_statements)} proven, k<={max(queues.keys())}]: {conclusion} $= {' '.join(new_label_sequence)}")

    input("Search terminated, Enter to list proven theorems...")
    for t, (conclusion, proofs) in enumerate(proven_statements.items()):
        print(f"{t} [{len(proofs)} proofs]: {conclusion}:")
        for p, proof in enumerate(proofs): print(f" $= {' '.join(proof)}")

