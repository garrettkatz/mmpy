# run from mmpy with $ python -m src.mmmine.dependencies
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

    # build direct dependency graph
    direct_dependencies = {} # rule label -> set of labels in rule's proof

    for r, (label, rule) in enumerate(db.rules.items()):
        # only propositions have proofs
        if rule.consequent.tag != "$p": continue

        # get proof labels (assumes proof in compressed format)
        split = rule.consequent.proof.index(")")
        step_labels = rule.consequent.proof[1:split]

        direct_dependencies[label] = set(step_labels)

    # direct dependency histogram
    num_deps = sorted(map(len, direct_dependencies.values()))

    pt.plot(num_deps)
    pt.xlabel("Sorted rule index")
    pt.ylabel("# direct dependencies")
    pt.show()


