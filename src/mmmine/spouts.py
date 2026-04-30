"""
spouts of and-or trees, some leafed on goal essentials and some rooted on goal consequents
"""
class SpoutNode:
    def __init__(self, tokens):
        self.tokens = tokens

class Spout:
    def __init__(self, claim, parse_rules):
        self.claim = claim
        self.parse_rules = parse_rules
        self.nodes = []

        # initialize nodes for each claim statement
        for statement in claim.essentials + [claim.consequent]:
            self.nodes.append(SpoutNode(statement.tokens))

    def contains_proof(self):
        return True

    def get_proof(self):
        return self

    def proof_size_lower_bound(self):
        return 0

    def attachments(self, rule):

        # find all unifications of each rule statement with spout nodes
        statement_attachments = []
        for statement in rule.essentials + [rule.consequent]:
            statement_nodes = []
            for node in self.nodes:
                unified = unify(statement.tokens, node.tokens, rule.mandatory | node.variables, self.parse_rules)
                if unified: statement_nodes.append(node)
            statement_attachments.append(statement_nodes)

        # yield each combination of one or more node attachments
        N = len(statement_attachments)
        for k in range(1,N+1):
            for combo in it.combinations(range(N), k):
                combo_nodes = [statement_attachments[c] for c in combo]
                for nodes in it.product(combo_nodes):
                    # yield the new spout with this attachment
                    pass

    def plot(self):
        pass
        

def spout_generator(rules, claim, proof_size_limit, spout=None):

    # initialize parent spout at top-level entry-point call
    if spout is None:
        parse_rules = rules["wff"] # todo: don't hardcode typecode
        spout = Spout(claim, parse_rules)

    # if smallest possible proof size in spout is greater than limit: return
    if spout.proof_size_lower_bound() >= proof_size_limit: return

    # for each rule:
    for rule in rules:
        # for every attachment (via unification) of one or more rule statements to some nodes in the spout so far
            # child spout = attachment of rule substitution to parent spout
            # yield from spout_generator(rules, claim, proof_size_limit, child spout)
        pass

    # yield Spout(claim)

def spout_prover(rules, claim, max_proof_size):
    print(f"proving {claim}")

    # a "search step" is adding a new node with either essential hypotheses or consequents that unify with one or more existing nodes
    # order all possible search steps so that smaller proofs are guaranteed identified before larger ones
    # bonus: "heuristic" which orders search steps so that proofs, if they exist, are identified sooner in the total search step order.
    # each proof is a satisfied and-or subtree of the spout graph

    # initialize spouts (goal essentials and consequents)

    for proof_size_limit in range(max_proof_size):
        # for each possible spout truncated by proof size:
        for spout in spout_generator(rules, claim, proof_size_limit):
            # if spout contains proof of claim, return success
            if spout.contains_proof(): return spout.get_proof()

    # towards heuristic:
    # "if the new node of the next search step does not have all essentials and conclusion unified against existing spouts appropriately, min proof size >= h"
    # how about unifying leaves of the consequent spout *with each other* as well as with the essential spouts (both their roots and non-anchor leaves!)? that should help bound dag size.
        # can you **draw** (plot) the spouts?

    return None

if __name__ == "__main__":

    goal_label = "mpd"

    import metamathpy.setmm as ms
    db = ms.load_pl()

    claim = db.rules[goal_label]
    rules = db.rules_up_to(goal_label)

    result = spout_prover(rules, claim, 0)
    print(result)

