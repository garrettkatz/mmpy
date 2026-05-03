"""
spouts of and-or trees, some leafed on goal essentials and some rooted on goal consequents
sparse matrix representation?
"""
import itertools as it
import src.metamathpy.database as md
import src.metamathpy.proof as mp
from src.metamathpy.parsing import unify

def multibind(X, Y, variables, sentinels, parse_rules, subst=None):
    """
    Generates unifications of all of X with subsets of Y
    variables, sentinels, parse_rules as in unify
    subst: initial substitution to apply
    yields (subst, ys)
        subst: unifying substitution
        ys: subset of Y unified with X
    """
    if subst is None: subst = {}

    # base case
    if len(X) == 0:
        yield subst, ()
        return

    # recursion
    x0 = mp.substitute(X[0], subst)
    for y in Y:
        y = mp.substitute(y, subst)
        success, s = unify(x0, y, variables, sentinels, parse_rules)
        if not success: continue
        for (new_subst, ys) in multibind(X[1:], Y, variables, sentinels, parse_rules, mp.compose(s, subst)):
            yield new_subst, (y,) + ys

class Spout:
    def __init__(self, claim, rules, nodes=None, order=None, variables=None, sentinels=None, steps=None):
        self.claim = claim
        self.rules = rules

        if nodes is None:
            # initialize nodes for each claim statement, with sentinels for claim variables (should not be substituted by a specialization)
            sentinels = {v: (f"mv{d}",) for (d,v) in enumerate(claim.mandatory.keys())}
            self.nodes = tuple(mp.substitute(statement.tokens, sentinels)[1:] for statement in (claim.consequent,) + claim.essentials)
            # initialize partial order (hypotheses before conclusion)
            self.order = {(n, self.nodes[0]) for n in self.nodes[1:]}
            # initialize variables and sentinels
            self.variables = set()
            self.sentinels = set(v[0] for v in sentinels.values())
            # initialize steps
            self.steps = {} # steps[conclusion] = OR([... step ...])

        else:
            self.nodes = nodes
            self.order = order
            self.variables = variables
            self.sentinels = sentinels
            self.steps = steps

    def __str__(self):
        # s = f"Spout(\n{claim}nodes:\n"
        s = f"Spout(\nnodes: [steps]:\n"
        for n in self.nodes:
            s += ' '.join(n) + ": " + str(self.steps.get(n, [])) + "\n"
        # s += "\n".join(" ".join(n) for n in self.nodes)
        # s += "\nsteps:\n" + "\n".join(' '.join(k) + ": " + str(v) for (k,v) in self.steps.items())
        s += "\nvars: " + str(self.variables) + ", sens: " + str(self.sentinels)
        return s

    def fullstr(self):
        # n conc:  [(<=rule, {h: n',...}), ...]
        s = f"Spout({self.claim.consequent.label} {' '.join(self.claim.consequent.tokens)}\n"
        for e in self.claim.essentials: s += f"     {e.label} {' '.join(e.tokens)}\n"
        for i, n in enumerate(self.nodes):
            s += f"{i: 3d} {' '.join(n)}"
            if i > len(self.claim.essentials):
                for step in self.steps.get(n, ()):
                    s += f" (<={step.rule.consequent.label} <"                    
            s += "\n"
            if i == len(self.claim.essentials): s += "-"*10 + "\n"
        return s

    def substitute(self, substitution):
        """
        Applies substitution to all nodes in-place
        """
        self.nodes = tuple(mp.substitute(n, substitution) for n in self.nodes)
        self.order = {(mp.substitute(a, substitution), mp.substitute(a, substitution)) for (a,b) in self.order}
        substeps = {}
        for conclusion, or_steps in self.steps.items():
            conclusion = mp.substitute(conclusion, substitution)
            substeps[conclusion] = []
            for step in or_steps:
                step = mp.ProofStep(
                    conclusion,
                    step.rule,
                    {h: mp.substitute(d, substitution) for (h,d) in step.dependencies.items()},
                    {v: substitution[v] for v in step.rule.mandatory},
                    disjoint=None) # todo: disjoints
                substeps[conclusion].append(step)
        self.steps = substeps

    def proof_check(self, node=None):
        """
        returns (success, proof) where
            success is True if self contains proof else False
            proof is a contained proof if success else None
        """

        # top-level call: set node to goal
        if node is None: node = self.nodes[0]
        print("proof check on " + " ".join(node))

        # base case: node is essential hypothesis
        H_c = len(self.claim.essentials)
        if node in self.nodes[1:1+H_c]:
            i = self.nodes[1:1+H_c].index(node)
            erule = md.Rule(consequent=self.claim.essentials[i], essentials=(), floatings=(), disjoint=(), variables=self.claim.mandatory) 
            return True, mp.ProofStep(node, erule)

        # or-branch on steps that conclude node
        for step in self.steps.get(node, ()):
            # and-branch on step's dependencies
            dependencies = {}
            for h, n_d in step.dependencies.items():
                result, dep_step = self.proof_check(n_d)
                if result:
                    dependencies[h] = dep_step
                else:
                    break
            if len(dependencies) == len(step.dependencies):
                proved_step = mp.ProofStep(step.conclusion, step.rule, dependencies, step.substitution, disjoint=None)
                return True, proved_step
                
        # if this line is reached, node is unjustified
        return False, None

    def unifications_with(self, rule, budget):
        """
        Generates partial unifications with rule respecting self's partial order
        budget is the maximum number of fresh nodes that can be attached
        yields (unifier, step, nodes) where
            unifier is the substitution
            step is the proof step for attachment, with token strings in place of dependencies
            nodes is the list of fresh nodes being attached
        """
        print("unify budget", budget)

        # hypothesis counts
        H_c = len(self.claim.essentials)
        H_r = len(rule.essentials)

        # variable symbols
        variables = set(rule.mandatory.keys()) | self.variables

        # unifiers including conclusion
        N_c = self.nodes[:1] + self.nodes[1+H_c:] # don't unify consequent with claim's essentials
        for n_c in N_c:
            success, s_c = unify(rule.consequent.tokens[1:], n_c, variables, self.sentinels, self.rules["wff"])
            if not success:
                # print(str(n_c) + ' unified with ' + str(rule.consequent.tokens[1:]) + f"[variables = {variables}] FAILED")
                continue
            # print(f"unified {' '.join(rule.consequent.tokens[1:])} with {' '.join(n_c)} by {s_c}")

            # filter dependency nodes satisfying partial order
            N_d = tuple(n for n in self.nodes[1:] if (n_c, n) not in self.order)
            # print("n_c: " + ' '.join(n_c))
            # print("N_d:\n" + '\n'.join(' '.join(n) for n in N_d))

            # all subsets of hypotheses: H_r - size <= budget, so H_r - budget <= size 
            # this way repeats a lot of work, optimize later
            for size in reversed(range(max(0, H_r-budget), H_r+1)):
                for idx in it.combinations(range(H_r), size):
                    X = tuple(rule.essentials[i].tokens[1:] for i in idx) # omit |- typecodes
                    # print(size, idx, "X:")
                    # print('\n'.join(' '.join(x) for x in X))
                    for substitution, N_X in multibind(X, N_d, variables, self.sentinels, self.rules["wff"], s_c):
                        # construct step and fresh nodes
                        dependencies = {}
                        fresh_nodes = []
                        for i, e in enumerate(rule.essentials):
                            if i in idx:
                                node = N_X[idx.index(i)]
                            else:
                                node = e.tokens[1:] # omit |- typecode
                                fresh_nodes.append(node)
                                # todo: occasionally fresh nodes are duplicates of self.nodes, filter or prevent these cases
                            dependencies[e.label] = node
                        step = mp.ProofStep(n_c, rule, dependencies, substitution) # todo: disjoint requirements
                        yield (substitution, step, tuple(fresh_nodes))

        # can't omit conclusion if there is no budget for new nodes
        if budget == 0: return

        # unify rule essentials with any nodes other than claim's conclusion
        n_c = rule.consequent.tokens[1:] # fresh node
        N_d = self.nodes[1:]

        # all subsets of hypotheses: H_r - size <= budget - 1, so H_r - budget + 1 <= size 
        for size in reversed(range(max(1, H_r - budget + 1), H_r+1)):
            for idx in it.combinations(range(H_r), size):
                X = tuple(rule.essentials[i].tokens[1:] for i in idx) # omit |- typecodes
                for substitution, N_X in multibind(X, N_d, variables, self.sentinels, self.rules["wff"]):
                    # construct step and fresh nodes
                    dependencies = {}
                    fresh_nodes = [n_c] # different from case above
                    for i, e in enumerate(rule.essentials):
                        if i in idx:
                            node = N_X[idx.index(i)]
                        else:
                            node = e.tokens[1:] # omit |- typecode
                            fresh_nodes.append(node)
                        dependencies[e.label] = node
                    step = mp.ProofStep(n_c, rule, dependencies, substitution) # todo: disjoint requirements
                    yield (substitution, step, tuple(fresh_nodes))

    def attach(self, unifier, step, nodes):
        """
        Attach a new step to the dag
        """

        # create work variables for any unbound mandatories in step.rule
        variables = set(self.variables)
        for v in step.rule.mandatory.keys():
            if v not in unifier:
                u = f"wv{len(variables)}"
                unifier[v] = (u,)
                variables.add(u)

        # update partial order with new step
        order = set(self.order)
        c = step.conclusion
        for d in step.dependencies.values():
            order.add((d, c))
            for n in self.nodes:
                if (n, d) in self.order: order.add((n, c))
                if (c, n) in self.order: order.add((c, n))

        # construct new spout with attachment
        nodes = self.nodes + nodes
        steps = dict(self.steps)
        if c not in steps: steps[c] = []
        steps[c].append(step)
        attachment = Spout(self.claim, self.rules, nodes, order, variables, self.sentinels, steps)
        attachment.substitute(unifier)
        return attachment

    def expansions(self, proof_size_cap):

        # base case: reached cap
        # budget = proof_size_cap - len(self.nodes)
        # if budget < 0: return # budget == 0 should still recurse for rules that introduce no fresh nodes
        budget = proof_size_cap - sum(map(len, self.steps.values()))
        print(f"{budget=}")
        if budget < 0: return

        # yield expansion up to cap
        yield self

        # if budget == 0: return
        # print(f"{budget=} didnt return")

        # recursive case: try attachments
        for rule in self.rules["|-"]:
            for (unifier, step, nodes) in self.unifications_with(rule, budget):
                # attach new step to spout
                attachment = self.attach(unifier, step, nodes)
                # yield from its expansions
                yield from attachment.expansions(proof_size_cap)

    def plot(self):
        pass

def spout_prover(claim, rules, max_proof_size):
    # a "search step" is adding a new node with either essential hypotheses or consequents that unify with one or more existing nodes
    # order all possible search steps so that smaller proofs are guaranteed identified before larger ones
    # bonus: "heuristic" which orders search steps so that proofs, if they exist, are identified sooner in the total search step order.
    # each proof is a satisfied and-or subtree of the spout graph
    print(f"proving {claim}")

    # initialize spout
    spout = Spout(claim, rules)

    # iteratively deepen expansions
    for proof_size_limit in range(max_proof_size+1):

        # for each possible spout truncated by proof size:
        for e, expansion in enumerate(spout.expansions(proof_size_limit)):
            print(f"\n *** expansion {e} *** \n")
            print(expansion.fullstr())
            input('.')

            # if spout contains proof of claim, return success
            success, proof = expansion.proof_check()
            if success: return proof

    # towards heuristic:
    # "if the new node of the next search step does not have all essentials and conclusion unified against existing spouts appropriately, min proof size >= h"
    # how about unifying leaves of the consequent spout *with each other* as well as with the essential spouts (both their roots and non-anchor leaves!)? that should help bound dag size.

    return None

if __name__ == "__main__":

    import metamathpy.setmm as ms
    db = ms.load_pl()
    parse_rules = [rule for rule in db.rules.values() if rule.consequent.tag == "$a" and rule.consequent.tokens[0] in ("wff", "class")]

    ## multibinder
    test_cases = [ # X, Y, variables
        (["ph"], ["ph"], ["ph"]),
        (["ph"], ["ps"], ["ph","ps"]),
        (["ph"], ["ps", "( ps -> ps )"], ["ph","ps"]),
        (["ph", "( ph -> ps )"], ["-. u0", "( -. u0 -> -. u1 )"], ["ph","ps","u0","u1"]),
    ]
    for (X, Y, V) in test_cases:
        X = [tuple(x.split()) for x in X]
        Y = [tuple(y.split()) for y in Y]
        print(X, Y, V)
        for s, ys in multibind(X, Y, V, (), parse_rules):
            print("", s, [" ".join(y) for y in ys])

    ## unifications_with
    claim = db.rules["ax-mp"]
    rules = db.rules_up_to("ax-1")

    spout = Spout(claim, rules)
    print(spout)
    print("\nunifications with ax-mp (sub, step, fresh):")
    for (s, step, fresh) in spout.unifications_with(db.rules["ax-mp"], budget=0):
        print({k: ' '.join(v) for k,v in s.items()})
        print(step)
        print(fresh)

    claim = md.Rule(
        consequent = md.Statement("tmp", "$p", "|- ( ph -> ps )".split(), ()),
        essentials = [
            md.Statement("tmp.1", "$e", "|- ( ta -> ( ph -> ps ) )".split(), ()),
            md.Statement("tmp.2", "$e", "|- ta".split(), ()),
        ],
        floatings = [
            md.Statement("wph", "$f", "wff ph".split(), ()),
            md.Statement("wps", "$f", "wff ps".split(), ()),
            md.Statement("wta", "$f", "wff ta".split(), ()),
        ],
        disjoint = (),
        variables = ("ph", "ps", "ta"),
    )
    claim.finalize()

    spout = Spout(claim, rules)
    print()
    print(spout)
    print("\nunifications with ax-mp (sub, step, fresh):")
    for (s, step, fresh) in spout.unifications_with(db.rules["ax-mp"], budget=0):
        print({k: ' '.join(v) for k,v in s.items()})
        print(step)
        print([' '.join(n) for n in fresh])

    claim = md.Rule(
        consequent = md.Statement("tmp", "$p", "|- ( ph -> ps )".split(), ()),
        essentials = [
            md.Statement("tmp.1", "$e", "|- ( ta -> ( ph -> ps ) )".split(), ()),
        ],
        floatings = [
            md.Statement("wph", "$f", "wff ph".split(), ()),
            md.Statement("wps", "$f", "wff ps".split(), ()),
            md.Statement("wta", "$f", "wff ta".split(), ()),
        ],
        disjoint = (),
        variables = ("ph", "ps", "ta"),
    )
    claim.finalize()

    spout = Spout(claim, rules)
    print()
    print(spout)
    print("\nunifications with ax-mp (sub, step, fresh):")
    for (s, step, fresh) in spout.unifications_with(db.rules["ax-mp"], budget=1):
        print({k: ' '.join(v) for k,v in s.items()})
        print(step)
        print([' '.join(n) for n in fresh])

    # ## expansions
    # claim = db.rules["mp2"]
    # rules = db.rules_up_to("mp2")
    # spout = Spout(claim, rules)
    # print(f"\n\n **** expanding {spout}")
    # print("\n **** expansions:")
    # for e, expansion in enumerate(spout.expansions(proof_size_cap=len(spout.nodes)+2)):
    #     print(f"\nexpansion {e}:\n")
    #     print(expansion)
    #     for or_steps in expansion.steps.values():
    #         for step in or_steps:
    #             print(f"{step} dependencies:")
    #             for h,d in step.dependencies.items(): print(h + ': ' + ' '.join(d))
    #     # input('..')

    # # result = spout_prover(rules, claim, 0)
    # # print(result)

    # # prover test: just a substitution of ax-1
    # claim = md.Rule(
    #     consequent = md.Statement("tmp", "$p", "|- ( ph -> ( ( ps -> ch ) -> ph ) )".split(), ()),
    #     essentials = [],
    #     floatings = [
    #         md.Statement("wph", "$f", "wff ph".split(), ()),
    #         md.Statement("wps", "$f", "wff ps".split(), ()),
    #         md.Statement("wch", "$f", "wff ch".split(), ()),
    #     ],
    #     disjoint = (),
    #     variables = ("ph", "ps", "ch"),
    # )
    # claim.finalize()
    # rules = db.rules_up_to("ax-2")

    # proof = spout_prover(claim, rules, max_proof_size=1)
    # assert proof is not None
    # print("Proof found:")
    # print(proof.tree_string())

    # # prover test: just a substitution of ax-mp
    # claim = md.Rule(
    #     consequent = md.Statement("tmp", "$p", "|- ( ph -> ps )".split(), ()),
    #     essentials = [
    #         md.Statement("tmp.1", "$e", "|- ( ta -> ( ph -> ps ) )".split(), ()),
    #         md.Statement("tmp.2", "$e", "|- ta".split(), ()),
    #     ],
    #     floatings = [
    #         md.Statement("wph", "$f", "wff ph".split(), ()),
    #         md.Statement("wps", "$f", "wff ps".split(), ()),
    #         md.Statement("wta", "$f", "wff ta".split(), ()),
    #     ],
    #     disjoint = (),
    #     variables = ("ph", "ps", "ta"),
    # )
    # claim.finalize()
    # rules = db.rules_up_to("ax-1")

    # proof = spout_prover(claim, rules, max_proof_size=1)
    # assert proof is not None
    # print("Proof found:")
    # print(proof.tree_string())

    # prover test: mp2
    claim = db.rules["mp2"]
    rules = db.rules_up_to("mp2")
    # here you need expansions to recurse but also need to change budget to steps, not nodes
    proof = spout_prover(claim, rules, max_proof_size=2)
    assert proof is not None
    print("Proof found:")
    print(proof.tree_string())
