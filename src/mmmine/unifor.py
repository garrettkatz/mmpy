import src.metamathpy.proof as mp
import src.metamathpy.terms as mt

try:
    profile
except NameError:
    profile = lambda x: x

class PartialProof:
    def __init__(self, assertions, justifications, bindings):
        self.assertions = assertions
        self.justifications = justifications
        self.bindings = bindings

    def substitute(self, substitution):
        return PartialProof(
            [a.substitute(substitution) for a in self.assertions],
            list(self.justifications),
            [{v: t.substitute(substitution) for (v,t) in b.items()} for b in self.bindings])

    def unify_with(self, terms, index):
        """
        generates unifications of each term with multisubset of self's assertions up to index
        yields substituted versions of self that unified
        """

        # base case: no terms left
        if len(terms) == 0:
            yield self
            return

        # try unifying next term with each of self's assertions
        for i in range(index):
            success, substitution = mt.unify(terms[0], self.assertions[i])
            if not success: continue

            # recurse on remaining terms
            partial_proof = self.substitute(substitution)
            remaining_terms = [t.substitute(substitution) for t in terms[1:]]
            yield from partial_proof.unify_with(remaining_terms, index)

    def initialized_for(claim, proof_size):
        tail_size = proof_size - len(claim.essentials)
        return PartialProof(
            [h.tokens for h in claim.essentials] + [("|-", f"sv{d}") for d in range(tail_size-1)] + [claim.consequent.tokens],
            [h.label for h in claim.essentials] + ["" for d in range(tail_size)],
            [{} for _ in range(proof_size)])

class SearchNode:
    def __init__(self, db, claim, rules, partial_proof):
        self.db = db
        self.claim = claim
        self.rules = rules
        self.partial_proof = partial_proof

    def proof_check(self):
        return False, None

    def applications_of(self, rule, step_index):
        success, substitution = mt.unify(rule.consequent, self.partial_proof.assertions[step_index])
        if not success: return

        partial_proof = self.partial_proof.substitute(substitution)
        partial_proof.justifications[step_index] = rule.consequent.label

        yield from partial_proof.unify_with(rule.essentials, step_index)

    def dfs(self, step_index=None):
    
        if step_index is None:
            step_index = len(self.claim.essentials)
    
        if step_index == len(self.partial_proof.assertions):
            yield self

        here consider prioritizing rules with 1+ essentials and unifying with most recent assertions first, to avoid repeating the same reasoning multiple times    
        for rule in self.rules["|-"]:
            for partial_proof in self.applications_of(rule, step_index):
                child = SearchNode(self.db, self.claim, self.rules, partial_proof)
                yield from dfs(child, step_index+1)

@profile
def ids(db, claim, rules, max_proof_size):
    print(f"proving {claim}")

    # iteratively deepen expansions, starting from nodes in original claim
    for proof_size in range(len(claim.essentials)+1, max_proof_size+1):
        print(f"*** deepening to {proof_size=} ***")

        # try each proof up to current limit
        search_root = SearchNode(db, claim, rules, PartialProof.initialized_for(claim, proof_size))
        for search_leaf in search_root.dfs():

            # check for proof
            success, root_step = search_leaf.proof_check()
            if success: return root_step

    return None

if __name__ == "__main__":

    todo: implement term unification

    from time import perf_counter
    import pickle as pk
    import src.metamathpy.setmm as ms

    db = ms.load_pl()
    goal_labels = ["mp2b"]
    # goal_labels = ["peirceroll"]
    # goal_labels = ["mpisyl"]
    # goal_labels = [label for (label, rule) in db.rules.items() if rule.consequent.tag == "$p" and "ALT" not in rule.consequent.label]
    goal_times = []
    goal_proofs = []
    for gl, goal_label in enumerate(goal_labels):

        print(f"\n *** attempting {goal_label} ({gl} of {len(goal_labels)})... ***\n")
        start_time = perf_counter()

        claim = db.rules[goal_label]
        rules = db.rules_up_to(goal_label)

        proof = ids(db, claim, rules, len(claim.essentials)+1)
        if proof is None:
            print("Failure :(")

