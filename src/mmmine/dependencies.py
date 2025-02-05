# run from mmpy with $ python -m src.mmmine.dependencies
import sys
import os
import random
import itertools as it
import pickle as pk
import numpy as np
from time import perf_counter
from ..metamathpy import database as md
from ..metamathpy import proof as mp
from ..metamathpy import setmm as ms

if __name__ == "__main__":

    do_deps = False

    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    # db = ms.load_imp()
    # db = ms.load_ni()
    db = ms.load_pl()
    # db = ms.load_all()
    # db.print()

    # build direct dependency graph
    direct_dependencies = {} # rule label -> set of labels in rule's proof
    proof_lengths = {}

    for r, (label, rule) in enumerate(db.rules.items()):
        # only propositions have proofs
        if rule.consequent.tag != "$p": continue

        # get proof labels (assumes proof in compressed format)
        split = rule.consequent.proof.index(")")
        step_labels = rule.consequent.proof[1:split]

        direct_dependencies[label] = set(step_labels)

        # get proof size
        root, steps = mp.verify_proof(db, rule)
        proof_lengths[label] = len(steps)


    # direct dependency histogram
    num_deps = sorted(map(len, direct_dependencies.values()))

    # pt.plot(num_deps)
    # pt.xlabel("Sorted rule index")
    # pt.ylabel("# direct dependencies")
    # pt.show()

    if do_deps:

        # dependents: how many other rules depend on this one, either directly or indirectly
        num_dependents = {label: 0 for label in direct_dependencies}
    
        # recursive helper
        def increment_indirect_dependencies(label):
            if label not in direct_dependencies: return
            for dep in direct_dependencies[label]:
                if dep not in direct_dependencies: continue
                num_dependents[dep] = num_dependents.get(dep, 0) + 1
                increment_indirect_dependencies(dep)
        for label in direct_dependencies:
            increment_indirect_dependencies(label)
    
        # direct dependency histogram
        labels = tuple(num_dependents.keys())
        num_deps = np.array([num_dependents[label] for label in labels])
        plens = np.array([proof_lengths[label] for label in labels])

        with open("dependencies.pkl","wb") as f: pk.dump((num_deps, plens), f)
        
    with open("dependencies.pkl","rb") as f: num_deps, plens = pk.load(f)

    pt.figure(figsize=(5,4))
    pt.scatter(num_deps + 1 + np.random.randn(len(num_deps))*0.1, plens + np.random.randn(len(plens))*0.1, marker='.', color='k')
    pt.xlabel("Number of dependents (+1)")
    pt.ylabel("Proof length")
    pt.xscale("log")
    pt.yscale("log")
    pt.ylim([1,101])
    pt.savefig("dependencies.eps")
    pt.tight_layout()
    pt.show()




