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

    def reconstruct_proof(self, standardizer, rules):
        """
        wrapper for working proof finalize
        """
        # TODO: disjoint variable requirements

        return self.working_proof.finalize(standardizer, rules)
        pass # unirule

    @profile
    def dfs(self, step_depth=None):

        # print("current working proof:")
        # print(self.working_proof)
        # input('.')

        # default: start after last essential hypothesis
        if step_depth is None:
            step_depth = len(self.claim.essentials)

        num_edges = sum(map(len, self.working_proof.dependencies))
        proof_size = len(self.working_proof.assertions)

        if num_edges > self.edge_count: return # todo: prune before recursive call

        if step_depth == proof_size:
            if num_edges == self.edge_count: yield self # only yield for exact edge count
            return

        # Determine how many essentials are needed to use all steps
        max_essentials = self.rule_index.max_essentials
        num_unused = sum((not u) for u in self.working_proof.used) - 1 # -1 for claim consequent
        steps_remaining = proof_size - step_depth
        min_essentials = max(0, num_unused - (steps_remaining - 1) * max_essentials)

        # Don't do more essentials than there are edges left in the target edge count (or less at last step)
        # Do enough essentials to still be able to reach target edge count

        # skip if impossible to use all steps
        if min_essentials > max_essentials: return

        # standardize working proof apart from rule index
        working_proof = self.working_proof.standardize(self.offset)

        # print(working_proof)
        # input('standardized ^^')

        # consequent-specific unifications at last step
        if step_depth + 1 == proof_size:
            for sub_working_proof in self.rule_index.consequent_specific_unifications(working_proof, step_depth, min_essentials):
                # print(working_proof)
                # input("consequent-specific generated this working_proof ^^")
                child = SearchNode(self.db, self.claim, self.rule_index, sub_working_proof, self.offset, self.edge_count)
                yield child

        # consequent-agnostic unifications at previous steps
        else:
            for sub_working_proof in self.rule_index.consequent_agnostic_unifications(working_proof, step_depth, min_essentials):
                # print(working_proof)
                # input("consequent-agnostic generated this working_proof ^^")
                child = SearchNode(self.db, self.claim, self.rule_index, sub_working_proof, self.offset, self.edge_count)
                yield from child.dfs(step_depth + 1)

        return

def ids(db, claim, entailment_rules, term_manager, max_proof_size, max_edge_count):
    """
    Assumes term manager has already encoded rule index
    """
    print(f"proving {claim}")
    print(f"old proof: {' '.join(claim.consequent.proof)}")

    # build rule index from rules
    rule_index = mu.RuleIndex(entailment_rules, term_manager)

    # termify claim
    consequent, essentials, mandatory = term_manager.termify(claim)

    # standardize claim variables apart from existing terms
    offset = len(term_manager.encoder) + 1
    standardizer = {v: offset+i for (i,v) in enumerate(mandatory)}
    consequent = mt.rename(consequent, standardizer)
    essentials = [(l, mt.rename(e, standardizer)) for (l,e) in essentials]
    sentinels = set(standardizer.keys())
    offset = offset + len(mandatory)

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
            for search_leaf in search_root.dfs():

                # completed_proof = search_leaf.working_proof.canonicalize(standardizer)
                # print(completed_proof)
                # input("Completed proof, canonicalized ^^")

                # check for proof
                # root_step = search_leaf.reconstruct_proof(standardizer)
                root_step = search_leaf.working_proof.finalize(standardizer, db.rules)

                if root_step is not None: return root_step

    return None

if __name__ == "__main__":

    from time import perf_counter
    import pickle as pk
    import src.metamathpy.setmm as ms
    import src.metamathpy.database as md

    max_node_depth = 3
    max_edge_count = 4 # make sure ->

        this is large enough to cover all proofs up to node depth
        you need to *enumerate in order of* increasing edge count **without** duplicating.  the max/min essentials for edge count is critical.
        could you possibly show ordered by edge count is less total num of search unifies on average than random ordering within last proof size depth

    do_run = True
    do_reload = False
    do_skip = True
    exclude_list = ms.new_usage_discouraged()
    start_from_goal_index = 0 # 783 (d3->2) #175 jad # 1374 syl332anc took 24223s before unify_with_filter
    stop_after = 100

    db = ms.load_pl()
    # goal_labels = ["id"]
    goal_labels = [label for (label, rule) in db.rules.items() if rule.consequent.tag == "$p" and label[-3:] not in ("ALT", "OLD") and label not in exclude_list]

    if do_run:

        if do_reload:
            with open("ufre.pkl","rb") as f: (goal_times, goal_proofs, novel, short) = pk.load(f)
        else:
            goal_times = {}
            goal_proofs = {}
            novel = set()
            short = set()

        new_attempt = new_proved = new_novel = new_short = 0

        for gl, goal_label in enumerate(goal_labels):
            if gl < start_from_goal_index: continue
            if goal_label in goal_proofs: continue
            if new_attempt == stop_after: break
            new_attempt += 1

            print(f"\n *** attempting {goal_label} ({gl} of {len(goal_labels)}). proved : novel : short (new) = {len(goal_proofs)} ({new_proved}) : {len(novel)} ({new_novel}) : {len(short)} ({new_short}) ***\n")
            start_time = perf_counter()

            claim = db.rules[goal_label]
            rules = db.rules_up_to(goal_label, exclude_list)
            if "|-" not in rules: rules["|-"] = []
            term_manager = mt.TermManager(rules["wff"])

            # print("Building rule index...")
            # rule_index = RuleIndex([r for r in rules["|-"] if r.consequent.label in ("ax-mp", "ax-1")], term_manager)

            print("ids searching...")
            max_proof_size = len(claim.essentials) + max_node_depth
            proof_root = ids(db, claim, rules["|-"], term_manager, max_proof_size, max_edge_count)

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
                    new_short += 1
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

            with open("ufre.pkl","wb") as f: pk.dump((goal_times, goal_proofs, novel, short), f)

    with open("ufre.pkl","rb") as f: (goal_times, goal_proofs, novel, short) = pk.load(f)

    # reload for original compressed proofs
    db = ms.load_pl()

    print(f"Grand total time = {sum(goal_times.values())}s, {len(goal_proofs)} of {len(goal_times)} proved, {len(novel)} novel, {len(short)} short")

    if len(short) > 0:
        print("short list:")
        for label in short:
            old_root, _ = mp.verify_compressed_proof(db, db.rules[label])
            old_normal_proof = old_root.normal_proof()
            print(f"label {label}:")
            print(f"new normal proof: {' '.join(goal_proofs[label])}")
            print(f"old normal proof: {' '.join(old_normal_proof)}")
