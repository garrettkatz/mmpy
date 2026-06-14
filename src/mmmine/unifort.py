import src.metamathpy.proof as mp
import src.metamathpy.terms as mt
from src.metamathpy.term_trie import TermTrieNode

try:
    profile
except NameError:
    profile = lambda x: x

class WorkingProof:
    def initialize(claim, proof_size, term_manager):
        return None, ()

i think searchnode logic can/should be absorbed into workingproof

class SearchNode:
    def __init__(self, db, claim, rule_index, working_proof, working_variables, term_manager):
        maybe variables should be an attribute of working proof?
        self.db = db
        self.claim = claim
        self.rule_index = rule_index
        self.working_proof = working_proof
        self.working_variables = working_variables
        self.term_manager = term_manager

    def reconstruct_proof(self):
        return None

    def dfs(self, step_depth=None):

        # default: start after last essential hypothesis
        if step_index is None:
            step_index = len(self.claim.essentials)

        proof_size = len(self.working_proof.assertions)
        if step_index == proof_size:
            yield self
            return

        # standardize here?
        self.working_proof.standardize_apart_from(rule index)

        # short-circuit working variable consequents
        if step_index + 1 == proof_size:
            # unify last proof step (claim consequent) against rule index consequent trie
            for essential_trie in rule_index.unifications_with_conclusion(self.working_proof, step_index, variables?, pruning?):
                # this is a consequent-specific essential_trie saved at index data of consequent trie
                # unify all subsets of proof_size.assertions with essentials trie
                # can these loops be collapsed? unifications_with_conclusion recurses in its per-consequent essential trees internally
                for u in essential_trie.unifications_with_dependencies(self.working_proof, step_index, variables?, pruning?):
                    # apply u to working proof (or generate the working proof itself?)
                    # dfs on substituted working proof, one step_index further
                    # or just stop recursing here, since you know the recursive call will hit base case in this if-branch?
        else: 
            # rule index has a separate trie root for all essentials of all rules, not consequent-specific
            for u in rule_index.unifications_with_dependencies(self.working_proof, .assertions[:step_index], variables?, pruning?):
                # apply u to working proof (or generate the working proof itself?)
                # dfs on substituted working proof, one step_index further

        yield from ()
        return

def ids(db, claim, rule_index, term_manager, max_proof_size):
    print(f"proving {claim}")

    # iteratively deepen expansions, starting from nodes in original claim
    for proof_size in range(len(claim.essentials)+1, max_proof_size+1):
        print(f"*** deepening to {proof_size=} ***")

        # try each proof up to current limit
        initial_proof, variables = WorkingProof.initialize(claim, proof_size, term_manager)
        search_root = SearchNode(db, claim, rule_index, initial_proof, variables, term_manager)
        for search_leaf in search_root.dfs():

            # check for proof
            root_step = search_leaf.reconstruct_proof()
            if root_step is not None: return root_step

    return None

if __name__ == "__main__":

    from time import perf_counter
    import pickle as pk
    import src.metamathpy.setmm as ms
    import src.metamathpy.database as md

    max_depth = 1

    do_run = True
    exclude_list = ms.new_usage_discouraged()
    start_from_goal_index = 0 #175 jad # 1374 syl332anc took 24223s before unify_with_filter
    stop_after = 10

    db = ms.load_pl()
    # goal_labels = ["notnotri"]
    # goal_labels = ["expt"]
    # goal_labels = ["peirceroll"]
    # goal_labels = ["mpisyl"]
    # goal_labels = ["ad4ant23"]
    # goal_labels = ["syl123anc"] # several mins
    # goal_labels = ["syl321anc"] # ~10min
    # goal_labels = ["syl332anc"]
    # goal_labels = ["olcs"] # 30sec
    goal_labels = [label for (label, rule) in db.rules.items() if rule.consequent.tag == "$p" and label[-3:] not in ("ALT", "OLD") and label not in exclude_list]

    if do_run:

        goal_times = {}
        goal_proofs = {}
        shortened = []
        for gl, goal_label in enumerate(goal_labels):
            if gl < start_from_goal_index: continue
            if len(goal_times) == stop_after: break
    
            print(f"\n *** attempting {goal_label} ({gl} of {len(goal_labels)})... ***\n")
            start_time = perf_counter()
    
            claim = db.rules[goal_label]
            rules = db.rules_up_to(goal_label, exclude_list)
            if "|-" not in rules: rules["|-"] = []
            term_manager = mt.TermManager(rules["wff"])


            # build an index for entailment rules
            # consequent_trie -> index data is (rules, subtrie)
            #    each rule in rules: a rule object with consequent corresponding to path and zero hypotheses
            #    subtrie: entrypoint to first hypothesis trie for all rules with 1+ hypotheses and consequent corresponding to path
            #    index also supports pruning mechanisms:
            #         prune if min(num_essentials, max_essentials) < min_essentials
            #         prune if num_unifies > unify_budget? inner ids on this budget
            rule_index = TermTrieNode()
            # work this out after fleshing out the usage beneath ids

            # print("indexing entailment rules...")
            # for rule in rules["|-"]:

            #     # term conversions
            #     consequent = term_manager.parse(rule.consequent.tokens[1:], set(rule.mandatory.keys()))
            #     essentials = [term_manager.parse(h.tokens[1:], set(rule.mandatory.keys())) for h in rule.essentials]
            #     mandatory = set([term_manager.encode(t) for t in rule.mandatory.keys()])

            #     node = rule_index.incorporate(consequent, result=None)
            #     if len(essentials) == 0:
            #         node.result = rule
            #     else:
            #         for essential in essentials:
            #             node.result = TermTrieNode

            print("searching...")
            proof_root = ids(db, claim, rule_index, term_manager, len(claim.essentials)+max_depth)
    
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
                mp.verify_normal_proof(db, claim) # raises assertion error if unverified
    
                print("Verified!")
                print(f"old proof ({old_size} steps): " + " ".join(old_normal_proof))
                # if new_size > old_size:
                #     print(old_root.tree_string())
                print(f"new proof ({new_size} steps): " + " ".join(new_normal_proof))
                # if new_size > old_size:
                #     print(proof_root.tree_string())
                print(f"total time: {total_time:.3f}s")
                if new_size < old_size:
                    shortened.append(goal_label)
                    print("You found one!!!")
                    # input('__')
    
                # # print(proof.to_string(term_manager))
                # print(proof.tree_string())
                # input('..')
    
                goal_proofs[goal_label] = new_normal_proof

                with open("ufrt.pkl","wb") as f: pk.dump((goal_proofs, goal_times, shortened), f)

    with open("ufrt.pkl","rb") as f: (goal_proofs, goal_times, shortened) = pk.load(f)

    print(f"Grand total time = {sum(goal_times.values())}s, {len(goal_proofs)} of {len(goal_times)} proved, {len(shortened)} shortened:")
    print(shortened)
    
    print("claim label, new normal proof:")
    for label in shortened:
        old_root, _ = mp.verify_compressed_proof(db, db.rules[label])
        old_normal_proof = old_root.normal_proof()
        print(f"label {label}:")
        print(f"new normal proof: {' '.join(goal_proofs[label])}")
        print(f"old normal proof: {' '.join(old_normal_proof)}")
        

