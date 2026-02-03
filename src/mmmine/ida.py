import numpy as np
import pickle as pk
from time import perf_counter
import itertools as it
import metamathpy.proof as mp

class Pile:

    # TODO?
    # - cache all valid rule applications to avoid re-checking?
    # - make rules, steps immutable and store in sets
    # - save all proof steps with same conclusion
    # - avoid repeating a previous rule application within dfs path (new rules for each proof step?)
    # - avoid duplicating same final proof steps in different orders across dfs paths (lexicographic floating introduction?)
    # - make sure you avoid any circular proofs (eg shorter path to id using things proved after it)

    def __init__(self, db=None, ax_only=False):
        self.rules = []
        # proof steps by type, keyed by conclusion
        self.steps = {"wff": {}, "|-": {}}
        self.trace = []

        if db is None: return

        # filter rules
        for rule in db.rules.values():

            # for now, omit "rules" for essential hypotheses
            if rule.consequent.tag == "$e": continue

            # if requested, omit any non-axiom propositions
            if ax_only and rule.consequent.tag == "$p": continue

            # otherwise keep the rule
            self.rules.append(rule)

        # maintain a record of valid rule applications?

    def __str__(self):
        s = "Pile:\n Rules:\n"
        for rule in self.rules:
            s += f" {' '.join(rule.consequent.tokens)}\n"
        s += "Steps:\n"
        # for step in list(self.steps["wff"].values()) + list(self.steps["|-"].values()):
        #     s += f" {step}\n"
        for step in self.trace: s += f" {step}\n"
        return s

    def copy(self):
        other = Pile()
        other.rules = list(self.rules)
        other.steps = {k: dict(v) for (k,v) in self.steps.items()}
        other.trace = list(self.trace)
        return other

    def contained_in(self, background):
        return all([
            step.conclusion in background
            for step in self.trace])

    def children(self):
        """
        Use with care; yields in-place modifications of self as each child
        """
        # try applying each rule
        for rule in self.rules:

            if len(rule.hypotheses) == 0:

                step, status = mp.perform(rule, ())
                assert status == "" # no hypotheses, should always be valid

                tokens = step.conclusion
                typecode = tokens[0] # wff or |-
                if tokens not in self.steps[typecode]:

                    self.steps[typecode][tokens] = step
                    self.trace.append(step)

                    yield self
    
                    # *** undo changes for next child, careful with this
                    self.steps[typecode].pop(tokens)
                    self.trace.pop()

            else:

                # rule signature: floating and essential
                wffs = list(self.steps["wff"].values())
                ents = list(self.steps["|-"].values())
                feeds = (wffs,)*len(rule.floatings) + (ents,)*len(rule.essentials)
                for deps in it.product(*feeds):

                    step, status = mp.perform(rule, deps)

                    # skip invalid rule applications
                    if status != "": continue

                    tokens = step.conclusion
                    typecode = tokens[0] # wff or |-
                    if tokens not in self.steps[typecode]:
                        self.steps[typecode][tokens] = step
                        self.trace.append(step)
    
                        yield self
        
                        # *** undo changes for next child, careful with this
                        self.steps[typecode].pop(tokens)
                        self.trace.pop()

        return

def dl_dfs(pile, max_depth=0):

    # check if max depth reached
    if max_depth <= 0:
        yield pile
        return

    # # skip if contained in background
    # if pile.contained_in(background):
    #     return

    # add to background

    # recurse search from each child
    for child in pile.children():
        yield from dl_dfs(child, max_depth=max_depth-1)

if __name__ == "__main__":

    import metamathpy.setmm as ms

    # loader = ms.load_ni
    loader = ms.load_pl
    # loader = lambda : ms.load_to("mpd")
    ax_only = False
    max_depth = 3
    max_time = 10#1 * 60 * 60

    # question: for a given max depth, how many set.mm theorems can you validly re-prove (without using their dependents)
    # quick way before piles add rules for proof steps: recursively find rules used in the proof step's proof and make sure all come before the re-proved one

    db = loader()
    print(db)

    pile = Pile(db, ax_only)

    # # quick id check: remove all unneeded rules
    # pile.rules = [r for r in pile.rules if r.consequent.label in ("wph", "wi", "ax-1", "mpd")]

    # print(pile)
    # input('..')

    # setup goals to prove
    goals = {}
    rule_labels = list(db.rules.keys())
    for n, (label, rule) in enumerate(db.rules.items()):
        # only look at propositions
        if rule.consequent.tag != "$p": continue

        # and only with no essential hypotheses
        if len(rule.essentials) > 0: continue

        # save conclusion and position in db
        goals[tuple(rule.consequent.tokens)] = (label, n)

    # get all goal conclusion sizes
    goal_sizes = set()
    for tok in goals.keys():
        goal_sizes.add(len(tok)-1) # -1 omits typecode

    # print("goal sizes:")
    # print(sorted(goal_sizes))
    # input('.')

    reproved = {}
    all_steps = {"wff": {}, "|-": {}}
    conc_freqs = {}
    num_leaves = 0
    start = perf_counter()
    for leaf in dl_dfs(pile, max_depth=max_depth):
        num_leaves += 1

        # check if a goal was proved
        for toks, step in leaf.steps["|-"].items():
            if toks in goals:
                _, n = goals[toks]
                proof = step.normal_proof()
                # reproved[toks] = proof
                if set(proof) <= set(rule_labels[:n]):
                    reproved[toks] = proof

        # track proof step frequencies
        for conc in list(leaf.steps["wff"].values()) + list(leaf.steps["|-"].values()):
            conc_freqs[conc] = conc_freqs.get(conc, 0) + 1

        # print(leaf)
        # print(conc_freqs)
        # input('.')

        # # get coefficients
        # typed_rules = {"wff":[], "|-":[]}
        # all_coefs = {"wff":[], "|-":[]}
        # for rule in leaf.rules:
        #     if rule.consequent.tag == "$f": continue

        #     typecode = rule.consequent.tokens[0] # organize by consequent typecode

        #     wffs = [f.tokens[1] for f in rule.floatings] # omit floating typecodes
        #     coefs = np.array([rule.consequent.tokens.count(wff) for wff in wffs])
        #     const = sum([t not in wffs for t in rule.consequent.tokens[1:]]) # omit typecode

        #     typed_rules[typecode].append(rule)
        #     all_coefs[typecode].append( (coefs, const) )

        #     # print(rule)
        #     # print(" + ".join([f"{c}|{w}|" for (c,w) in zip(coefs,wffs)] + [str(const)]))
        #     # input('.')

        # # get currently built wff sizes
        # wff_sizes = set()
        # for toks, step in leaf.steps["wff"].items():
        #     wff_sizes.add(len(toks)-1) # -1 omits typecode
        # print("wff sizes:")
        # print(sorted(wff_sizes))

        # # get n-hop sizes
        # hop_sizes = {"wff": set(wff_sizes), "|-": set()}
        # for hop in range(1):
        #     combos = {}
        #     next_hop_sizes = {}
        #     for typecode in ("wff", "|-"):
        #         next_hop_sizes[typecode] = set()

        #         for (rule, (coefs, const)) in zip(typed_rules[typecode], all_coefs[typecode]):
        #             if len(coefs) not in combos:
        #                 combos[len(coefs)] = np.array(tuple(it.product(hop_sizes["wff"], repeat=len(coefs))))

        #             print(rule)
        #             print(" + ".join([f"{c}|{w}|" for (c,w) in zip(coefs,wffs)] + [str(const)]))
        #             print("combos:")
        #             print(combos[len(coefs)])
        #             print("coefs:")
        #             print(coefs, const)
        #             print("combos @ coefs:")
        #             print(set((combos[len(coefs)] @ coefs + const).astype(int)))
        #             input('.')

        #             next_hop_sizes[typecode] |= set((combos[len(coefs)] @ coefs + const).astype(int))

        #     print(f"hop {hop+1} sizes:")
        #     for typecode in ("wff", "|-"):
        #         hop_sizes[typecode] |= next_hop_sizes[typecode]
        #         print(typecode, sorted(hop_sizes[typecode]))
        #     print("vs goal sizes:")
        #     print(sorted(goal_sizes))

        #     input('.')

        duration = perf_counter() - start
        if duration > max_time: break


    # print(leaf)
    unifreqs = set(conc_freqs.values())
    freq_freqs = {f: list(conc_freqs.values()).count(f) for f in unifreqs}
    print(freq_freqs)
    for conc, freq in conc_freqs.items():
        if freq == max(unifreqs): print(conc)
    # for conc, freq in conc_freqs.items():
    #     print(freq, conc)

    # print(f"\nDistinct wffs:")
    # for c, conc in enumerate(all_steps["wff"].keys()): print(c, " ".join(conc))
    # print(f"\nDistinct |-:")
    # for c, conc in enumerate(all_steps["|-"].keys()): print(c, " ".join(conc), conc)

    # si_tok = ("|-", "(", "si", "->", "(", "-.", "si", "->", "ta", ")", ")")
    # et_tok = ("|-", "(", "(", "(", "et", "->", "et", ")", "->", "si", ")", "->", "(", "-.", "et", "->", "si", ")", ")")
    # id_tok = ("|-", "(", "ph", "->", "ph", ")")

    # # print("\nlast leaf:\n")
    # # print(last)
    # print(f"\n{num_leaves} leaves total at depth {max_depth}, {len(all_steps['wff'])} wffs and {len(all_steps['|-'])} |-s")
    # print(f"Took {duration:.3f}s ({duration/60:.3f}min, {duration/(60*60):.3f}hr)")
    # print(f"si? {si_tok in all_steps['|-']}")
    # print(f"et? {et_tok in all_steps['|-']}")
    # print(f"id? {id_tok in all_steps['|-']}")

    # for n, (toks, proof) in enumerate(reproved.items()):
    #     lab, _ = goals[toks]
    #     step, _ = mp.verify_compressed_proof(db, db.rules[lab])
    #     print(f"{n: 3d}  |np|={len(proof)} [{lab}] {' '.join(toks)} <{' '.join(proof)}>  VS  <{' '.join(step.normal_proof())}>")
    # print(f"{len(reproved)} of {len(goals)} reproved")

    # with open(f"ida_d{max_depth}.pkl", "wb") as f: pk.dump(reproved, f)

