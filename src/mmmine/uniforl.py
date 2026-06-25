import numpy as np
from time import perf_counter

import src.metamathpy.proof as mp
import src.metamathpy.terms as mt
from src.metamathpy.term_trie import TermTrieNode
import src.metamathpy.unirule as mu

try:
    profile
except NameError:
    profile = lambda x: x

class SearchNode:
    def __init__(self, db, claim, rule_index, working_proof, offset, edge_count):
        """
        offset: offset for fresh variable ids, beyond ids in rule index and termified claim
        """
        self.db = db
        self.claim = claim
        self.rule_index = rule_index
        self.working_proof = working_proof
        self.offset = offset
        self.edge_count = edge_count

    def complete_essentialless(self):
        """
        Tries justifying each remaining unjustified node in self's working proof with essentialless rules
        Returns new working proof with justifications complete (or None on failure)
        """
        p = self.working_proof
        for i in range(len(p.claim.essentials), len(p.assertions)):
            if p.justifications[i] == "":
                assert len(p.dependencies[i]) == 0

                # instantiate is wrong? ax1 instantiated incorrectly?
                sub, data = self.rule_index.consequent_trie[0,0].instantiate(self.rule_index.consequent_variables[0,0], p.assertions[i])
                if data is None:
                    return None

                (rules, _, _) = data
                if len(rules) == 0:
                    return None # no way to justify this step

                # todo: yield from rules?
                (label, consequent) = rules[0]
                # print('sub', sub)
                # print(np.array(consequent).T)
                # print(self.rule_index.term_manager.serialize(consequent))
                # print(np.array(mt.substitute(consequent, sub)).T)
                # print(self.rule_index.term_manager.serialize(mt.substitute(consequent, sub)))
                p = p.replace_assertion(i, mt.substitute(consequent, sub), p.variables)
                p.justifications[i] = label

        return p

    @profile
    def dfs(self, step_index=None, timeout=None):

        # stop if out of time
        if timeout is not None and perf_counter() > timeout: return

        # print("current working proof:")
        # print(self.working_proof)
        # input('.')

        # default: start after last essential hypothesis
        if step_index is None:
            step_index = len(self.claim.essentials)

        num_edges = sum(map(len, self.working_proof.dependencies))
        proof_size = len(self.working_proof.assertions)

        if num_edges > self.edge_count: return # todo: prune before recursive call

        if step_index == proof_size:
            assert num_edges == self.edge_count
            yield self # only yield for exact edge count
            # if num_edges == self.edge_count: yield self # only yield for exact edge count
            return

        # Determine how many essentials are needed to use all steps
        max_essentials = self.rule_index.max_essentials
        num_unused = sum((not u) for u in self.working_proof.used) - 1 # -1 for claim consequent
        steps_remaining = proof_size - step_index
        min_essentials = max(0, num_unused - (steps_remaining - 1) * max_essentials)
        min_new_usage = min_essentials

        # maximum remaining edges you can create is steps_remaining * rule_index.max_essentials
        # minimum you can create is steps_remaining * (rule_index.min_essentials=0) == 0 (0 for PL)
        # number you need to create is self.edge_count
        # maximum you can create now while keeping self.edge_count reachable is:
            # self.edge_count, since after that essential-less rules would add no more edges (not accounting for usage requirements)
            # accounting for usage requirements, max you can create now is self.edge_count - (steps_remaining-1)
                # since each step remaining (except goal) needs at least one edge separate from current step_index to be used
        max_current_essentials = min(max_essentials, self.edge_count - (steps_remaining - 1))
        # minimum you need to create now to keep self.edge_count reachable is:

        # Don't do more essentials than there are edges left in the target edge count (or less at last step)
        # Do enough essentials to still be able to reach target edge count
        # you need to *enumerate in order of* increasing edge count **without** duplicating.  the max/min essentials for edge count is critical.

        # skip if impossible to use all steps
        if min_essentials > max_essentials: return

        # standardize working proof apart from rule index
        working_proof = self.working_proof.standardize(self.offset)

        # print(working_proof)
        # input('standardized ^^')

        # consequent-specific unifications at last step
        if step_index + 1 == proof_size:
            # for sub_working_proof in self.rule_index.consequent_specific_unifications_defer(working_proof, step_index, min_new_usage, 0, max_current_essentials):
            for sub_working_proof in self.rule_index.consequent_specific_unifications(working_proof, step_index, min_new_usage, 0, max_current_essentials):
                # print(working_proof)
                # input("consequent-specific generated this working_proof ^^")
                child = SearchNode(self.db, self.claim, self.rule_index, sub_working_proof, self.offset, self.edge_count)
                yield child

        # consequent-agnostic unifications at previous steps
        else:
            # for sub_working_proof in self.rule_index.consequent_agnostic_unifications_defer(working_proof, step_index, min_new_usage, 0, max_current_essentials):
            for sub_working_proof in self.rule_index.consequent_agnostic_unifications(working_proof, step_index, min_new_usage, 0, max_current_essentials):
                # print(working_proof)
                # input("consequent-agnostic generated this working_proof ^^")
                child = SearchNode(self.db, self.claim, self.rule_index, sub_working_proof, self.offset, self.edge_count)
                yield from child.dfs(step_index + 1, timeout)

        return

def ids(db, claim, entailment_rules, term_manager, max_proof_size, max_edge_count, max_time):
    """
    max_time: maximum time in seconds before early termination
    """
    print(f"proving {claim}")
    print(f"old proof: {' '.join(claim.consequent.proof)}")

    # build rule index from rules
    rule_index = mu.RuleIndex(entailment_rules, term_manager)
    # print(rule_index.full_string())
    # input('.')

    # termify claim
    consequent, essentials, mandatory = term_manager.termify(claim)

    # standardize claim variables apart from existing terms
    offset = len(term_manager.encoder) + 1
    standardizer = {v: offset+i for (i,v) in enumerate(mandatory)}
    consequent = mt.rename(consequent, standardizer)
    essentials = [(l, mt.rename(e, standardizer)) for (l,e) in essentials]
    sentinels = set(standardizer.keys())
    offset = offset + len(mandatory)

    timeout = perf_counter() + max_time

    # 2d IDS of #edge and #node, DP? different traversal orders?

    # every node (except last) needs at least one outgoing edge to be used.  So E is >= N-1, so N <= E+1, so N < E+2

    # iteratively deepen edge count
    for edge_count in range(len(essentials), max_edge_count+1): # len(essentials) == N-1

        # iteratively deepen proof size subject to edge count
        for proof_size in range(len(essentials)+1, min(max_proof_size+1, edge_count+2)):
            print(f"*** deepening to {edge_count=}, {proof_size=} ***")

            # try each proof up to current limit
            initial_proof = mu.WorkingProof.initialize(claim, consequent, essentials, offset, proof_size, term_manager)
            search_root = SearchNode(db, claim, rule_index, initial_proof, offset, edge_count)
            for search_leaf in search_root.dfs(timeout=timeout):

                # print(search_leaf.working_proof)
                # input("yielded proof ^^")

                # here, try complete essentialless
                completed_proof = search_leaf.complete_essentialless()
                if completed_proof is None: continue

                # print(completed_proof)
                # input("completed proof ^^")

                # check for proof
                root_step = completed_proof.finalize(standardizer, db.rules)

                if root_step is not None:
                    # print(root_step.tree_string())
                    # input("finalized proof ^^")
                    return root_step

            if perf_counter() > timeout: return None

    return None

if __name__ == "__main__":

    import pickle as pk
    import src.metamathpy.setmm as ms
    import src.metamathpy.database as md

    max_time = 10*60 # seconds
    max_node_depth = 10

    # PL |- rules have at most 10 essentials, though multiple essentials could conceivably bind the same proof step.  that's still 10 unifications and "edges".
    # if every non-claim-hypothesis essential proof step is justified by 10 essentials, then # edges is 10 * (# nodes - # claim essentials) = 10 * max_node_depth
    MAX_H_PL = 10

    max_edge_count = MAX_H_PL * max_node_depth
    # max_edge_count = 7 # 30

    do_run = True
    do_reload = True
    do_skip = True
    exclude_list = ms.new_usage_discouraged()
    start_from_goal_index = 0 # (d3->2) #175 jad # 1374 syl332anc took 24223s before unify_with_filter
    stop_after = -1

    db = ms.load_pl()
    # goal_labels = ["id"]
    goal_labels = [label for (label, rule) in db.rules.items() if rule.consequent.tag == "$p" and label[-3:] not in ("ALT", "OLD") and label not in exclude_list]

    if do_run:

        if do_reload:
            with open("ufrl.pkl","rb") as f: (goal_times, goal_proofs, novel, short) = pk.load(f)
        else:
            goal_times = {}
            goal_proofs = {}
            novel = set()
            short = set()

        new_attempt = new_proved = new_novel = 0
        new_short = set()

        for gl, goal_label in enumerate(goal_labels):
            if gl < start_from_goal_index: continue
            if goal_label in goal_proofs: continue
            if new_attempt == stop_after: break
            new_attempt += 1

            print(f"\n *** attempting {goal_label} ({gl} of {len(goal_labels)}). proved : novel : short (new) = {len(goal_proofs)} ({new_proved}) : {len(novel)} ({new_novel}) : {len(short)} ({len(new_short)}) ***\n")
            start_time = perf_counter()

            claim = db.rules[goal_label]
            rules = db.rules_up_to(goal_label, exclude_list)
            if "|-" not in rules: rules["|-"] = []
            term_manager = mt.TermManager(rules["wff"])

            # rules["|-"] = [r for r in rules["|-"] if r.consequent.label in ("ex", "a1i", "pm5.21ndd")] # 783 premise selection

            # print("Building rule index...")
            # rule_index = RuleIndex([r for r in rules["|-"] if r.consequent.label in ("ax-mp", "ax-1")], term_manager)

            print("ids searching...")
            max_proof_size = len(claim.essentials) + max_node_depth
            proof_root = ids(db, claim, rules["|-"], term_manager, max_proof_size, max_edge_count, max_time)

            total_time = perf_counter()-start_time
            goal_times[goal_label] = total_time

            if proof_root is None:
                print("Failure :(")
                # input('...')
            else:

                # verify and compare
                old_root, _ = mp.verify_compressed_proof(db, claim)
                old_normal_proof = old_root.normal_proof()
                new_normal_proof = proof_root.normal_proof()

                # new_size = len([s for s in proof_root.all_steps() if s.conclusion[0] == "|-"])
                # old_size = len([s for s in old_root.all_steps() if s.conclusion[0] == "|-"])
                new_size = len(proof_root.all_steps())
                old_size = len(old_root.all_steps())

                claim.consequent = md.Statement(claim.consequent.label, claim.consequent.tag, claim.consequent.tokens, new_normal_proof)
                new_root, new_steps = mp.verify_normal_proof(db, claim) # raises assertion error if unverified
                # print(len(new_steps), "new steps")
                # print(old_root.tree_string())
                # print(new_root.tree_string())

                print("Verified!")
                print(f"old proof ({old_size} steps): " + " ".join(old_normal_proof))
                # if new_size > old_size:
                #     print(old_root.tree_string())
                print(f"new proof ({new_size} steps): " + " ".join(new_normal_proof))
                # if new_size > old_size:
                #     print(proof_root.tree_string())
                print(f"total time: {total_time:.3f}s")
                if new_size < old_size:
                    short.add(goal_label)
                    new_short.add(goal_label)
                    print("You found one!!!")
                    # input('__')

                # # print(proof.to_string(term_manager))
                # print(proof.tree_string())
                # input('..')

                goal_proofs[goal_label] = new_normal_proof
                new_proved += 1

                if old_normal_proof != new_normal_proof:
                    novel.add(goal_label)
                    new_novel += 1

            with open("ufrl.pkl","wb") as f: pk.dump((goal_times, goal_proofs, novel, short), f)

        print("NEW SHORT")
        print(new_short)
        input('..')

    with open("ufrl.pkl","rb") as f: (goal_times, goal_proofs, novel, short) = pk.load(f)

    # reload for original compressed proofs
    db = ms.load_pl()

    print(f"Grand total time = {sum(goal_times.values())}s, {len(goal_proofs)} of {len(goal_times)} proved, {len(novel)} novel, {len(short)} short")

    if do_run:
        short_list = new_short
    else:
        short_list = short

    if len(short_list) > 0:
        if do_run: print("new short list:")
        else: print("short list:")
        for label in short:
            old_root, _ = mp.verify_compressed_proof(db, db.rules[label])
            old_normal_proof = old_root.normal_proof()
            print(f"label {label}:")
            print(f"new normal proof: {' '.join(goal_proofs[label])}")
            print(f"old normal proof: {' '.join(old_normal_proof)}")


