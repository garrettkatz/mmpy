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

        rule = db.rules[label]

        # if label already included, don't repeat
        if label in formulation_labels: return

        # if label is essential hypothesis, don't include as valid inference rule
        if rule.consequent.tag == "$e": return

        # include current label if it is axiom, floating hypothesis, or proposition
        formulation_labels.add(label)

        # only recurse on labels of propositions
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

def forward_search(db, formulation_labels, max_depth):

    valid_proofs = {d: {} for d in range(max_depth+1)} # depth -> proof string -> conclusion step
    valid_proofs["all"] = {} # depth|all
    stacks = {0: {(): []}} # depth -> proof string -> stack

    # search by depth
    for depth in range(max_depth):

        # allocate stacks for new depth
        stacks[depth+1] = {}

        # try appending labels to each current stack
        for proof, stack in stacks[depth].items():
            for label in formulation_labels:

                new_proof = proof + (label,)
                new_stack = list(stack) # will be modified in-place
                new_step, msg = mp.conduct(db.rules[label], new_stack)

                # skip if invalid
                if msg != "": continue

                # push the new step and save the new stack
                new_stack.append(new_step)
                stacks[depth+1][new_proof] = new_stack

                # if new stack is singleton, new proof is valid; save it
                if len(new_stack) == 1:
                    valid_proofs["all"][new_proof] = new_step
                    valid_proofs[depth+1][new_proof] = new_step
                    # print("new valid proof:", " ".join(new_proof), " ".join(new_step.conclusion))

    return valid_proofs, stacks

if __name__ == "__main__":

    db = ms.load_pl()
    # db = ms.load_all()

    num_samples = 500
    sample_size = 1
    max_depth = 5

    do_expansion = False

    if do_expansion:

        samples = []
        membranes = [] # new theorem sets after expansion
        growths = [] # per-depth search growth
        for s in range(num_samples):
            formulation_labels = sample_formulation(db, sample_size)
            samples.append(formulation_labels)
            print(f"{s}: {len(formulation_labels)} labels in formulation")
    
            # get conclusions of existing formulation labels
            existing = set()
            for label in formulation_labels:
                existing.add(tuple(db.rules[label].consequent.tokens))
    
            # try expanding
            valid_proofs, stacks = forward_search(db, formulation_labels, max_depth)
            for depth in range(max_depth+1):
                print(f"  depth {depth}: {len(valid_proofs[depth])} valid proofs, {len(stacks[depth])} stacks")
    
            # count distinct conclusions separate from what is already in formulation
            conclusions = {} # conclusion -> [proof strings]
            for proof, final_step in valid_proofs["all"].items():
                conc = final_step.conclusion
                if conc not in conclusions: conclusions[conc] = []
                conclusions[conc].append(proof)
    
            new_theorems = {k: v for (k,v) in conclusions.items() if k not in existing}
    
            print(f" {len(valid_proofs['all'])} valid proofs, {len(conclusions)} distinct conclusions, {len(new_theorems)} new")

            membranes.append((conclusions, new_theorems))
            growths.append([len(valid_proofs[d]) for d in range(max_depth+1)])

        with open("expansion.pkl", "wb") as f:
            pk.dump((samples, membranes, growths), f)

    with open("expansion.pkl", "rb") as f:
        (samples, membranes, growths) = pk.load(f)

    form_sizes = [formulation_size(db, sample) for sample in samples]
    thm_counts = [len(new_theorems) for (_, new_theorems) in membranes]
    dist_concs = [len(conclusions) for (conclusions, _) in membranes]
    growths = np.array(growths)


    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    pt.figure(figsize=(8,2.5))
    pt.subplot(1,2,1)
    pt.hist(list(map(len, samples)), rwidth=.8)
    pt.xlabel("Rules in formulation")
    pt.ylabel("Frequency")

    pt.subplot(1,2,2)
    pt.hist(form_sizes, rwidth=.8)
    pt.xlabel("Formulation size")
    # pt.ylabel("Frequency")

    pt.tight_layout()
    pt.savefig("formsamples.eps")

    pt.figure(figsize=(8,2.5))
    pt.subplot(1,2,1)
    pt.plot(growths.T, 'k-', alpha=.05)
    pt.plot(growths.mean(axis=0), 'b-')
    pt.xlabel("Search depth")
    pt.ylabel("Valid proofs")
    pt.yscale('log')

    # pt.subplot(1,3,2)
    # pt.plot(dist_concs, growths.sum(axis=1), 'k.')
    # pt.xlabel("Distinct conclusions")
    # pt.ylabel("Valid proofs")

    pt.subplot(1,2,2)
    pt.plot(form_sizes, thm_counts, 'k.')
    pt.xlabel("Formulation size")
    pt.ylabel(f"{max_depth}-expansion")

    pt.tight_layout()
    pt.savefig("expansion.pdf")

    pt.show()

