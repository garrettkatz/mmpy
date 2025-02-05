"""
run from mmpy with $ python -m src.mmmine.wff_repeats

Plot wff length vs frequency across all assertions and proof steps
"normalize" variable names
color-code the ones that are already definitions
ideally, parse wffs and include sub-wffs
"""

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

# parse ( definiendum <-> definiens )
# return definiendum, definiens
def parse_def(tokens):

    depth = 0
    for t, token in enumerate(tokens):
        # track parenthesis depth
        if token == "(": depth += 1
        if token == ")": depth -= 1

        # split on shallowest biconditional
        if token == "<->" and depth == 1:
            return tokens[1:t-1], tokens[t+1:-1]

    # parse error if not returned yet
    return None, None

# approximate parentheses-based parse
def parse_wff(tokens):
    sub_wffs = set([tokens])
    open_idx = {}
    depth = 0
    for t, token in enumerate(tokens):
        # track parenthesis depth
        if token == "(":
            depth += 1
            open_idx[depth] = t
        if token == ")":
            sub_wff = tokens[open_idx[depth]:t+1]
            sub_wffs.add(sub_wff)
            depth -= 1
    return sub_wffs    

canon_t = ("ph","ps","ch","th","ta","et","ze","si","rh","mu","la","ka")
canon_s = set(canon_t)

def normalize(tokens):
    subst = {}
    for t, token in enumerate(tokens):
        if token not in canon_s: continue
        if token in subst: continue
        subst[token] = canon_t[len(subst)]
    return tuple(subst.get(tok, tok) for tok in tokens)

if __name__ == "__main__":

    do_count = False

    if do_count:

        db = ms.load_pl()
        # db = ms.load_all()

        wff_counts = {}
        def_wffs = set()
        parse_errors = []

        for r, (label, rule) in enumerate(db.rules.items()):
            print(f"rule {r} ({label}) of {len(db.rules)}...")

            # include consequent wff
            wff = tuple(rule.consequent.tokens)
            wff = wff[1:] # exclude leading wff or |-
            sub_wffs = parse_wff(wff)
            for sub_wff in map(normalize, sub_wffs):
                wff_counts[sub_wff] = wff_counts.get(sub_wff, 0) + 1

            # mark wffs that are already definitions
            if rule.consequent.tag == "$a" and label[:3] == "df-":
                definiendum, definiens = parse_def(wff)
                if definiens is None:
                    parse_errors.append(wff)
                else:
                    definiens = normalize(definiens)
                    wff_counts[definiens] = wff_counts.get(definiens, 0) + 1
                    def_wffs.add(definiens)

            # only look at proofs of propositions
            if rule.consequent.tag != "$p": continue

            # uncompress proof
            root, steps = mp.verify_proof(db, rule)

            # count wffs in each step
            for step in steps.values():
                wff = tuple(step.conclusion)
                wff = wff[1:] # exclude leading wff or |-
                sub_wffs = parse_wff(wff)
                for sub_wff in map(normalize, sub_wffs):
                    wff_counts[sub_wff] = wff_counts.get(sub_wff, 0) + 1
    
        with open("wff_repeats.pkl", "wb") as f:
            pk.dump((wff_counts, def_wffs, parse_errors), f)

    with open("wff_repeats.pkl", "rb") as f:
        wff_counts, def_wffs, parse_errors = pk.load(f)

    print(f"{len(wff_counts)} wffs, {len(def_wffs)} are defs")
    print(f"{len(parse_errors)} parse errors:")
    for tokens in parse_errors: print(" ".join(tokens))


    wffs, counts = zip(*wff_counts.items())
    lens = np.array(list(map(len, wffs)))
    counts = np.array(counts)
    is_def = np.array([wff in def_wffs for wff in wffs])

    sorter = np.argsort(-counts)
    wffs = tuple(wffs[i] for i in sorter)
    lens = lens[sorter]
    counts = counts[sorter]
    is_def = is_def[sorter]

    dominators = np.zeros(len(counts))
    for i in range(len(counts)):
        dominators[i] = ((lens >= lens[i]) & (counts >= counts[i])).sum() - 1

    print("non-dominated non-def wffs:")
    for idx in np.flatnonzero((dominators == 0) & ~is_def):
        print(f"{counts[idx]:4d}: {' '.join(wffs[idx])[:50]}")

    # print("top most frequent wffs:")
    # sorter = np.argsort(-counts)
    # for idx in sorter[:30]:
    #     print(f"{counts[idx]: 4d}: {' '.join(wffs[idx])}")

    import matplotlib.pyplot as pt
    from matplotlib import rcParams
    rcParams["font.family"] = "serif"

    pt.figure(figsize=(3.75,3))
    pt.plot(lens[is_def], counts[is_def], mfc='w', mec='k', marker='o', markersize=10, linestyle='none', label="Definition", zorder=2)
    pt.plot(lens[(dominators == 0) & ~is_def], counts[(dominators == 0) & ~is_def], 'k+', label="Pareto optimal", zorder=1)
    pt.plot(lens[(dominators >= 1) & ~is_def], counts[(dominators >= 1) & ~is_def], 'k.', label="other", zorder=0)
    pt.xlabel("Length")
    pt.ylabel("Frequency")
    pt.xscale("log")
    pt.yscale("log")
    pt.legend()
    pt.tight_layout()
    pt.savefig("wff_repeats.eps")
    pt.show()

