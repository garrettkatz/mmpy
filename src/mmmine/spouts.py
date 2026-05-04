"""
spouts of and-or trees, some leafed on goal essentials and some rooted on goal consequents
sparse matrix representation?
"""
import itertools as it
import src.metamathpy.database as md
import src.metamathpy.proof as mp
from src.metamathpy.parsing import unify, parse_proof

try:
    profile
except NameError:
    profile = lambda x: x

@profile
def eager_bind(X, Y, floor, variables, sentinels, parse_rules, subst=None, idx=None):
    """
    Generates unifications of subsets of X with subsets of Y
    Only yields unifications of >= floor elements of X
    variables, sentinels, parse_rules as in unify
    subst: substitution built up during recursion
    uX: unifications with X build up during recursion
    yields (subst, uY, idx)
        subst: unifying substitution
        uY: unifier applied to each element of Y
        idx[i]: element of uY unified with X[i], if any, else None
    """
    if subst is None:
        subst = {}
        idx = ()

    # base case: impossible to reach floor
    if len(X) < floor: return

    # base case: all X processed
    if len(X) == 0:
        yield subst, Y, idx
        return

    # recursive case: unifying next element of X with each of Y
    for n,y in enumerate(Y):
        # try unifying X[0] with y
        success, s = unify(X[0], y, variables, sentinels, parse_rules)
        if not success: continue
        # apply substitution for remaining elements
        sX = [mp.substitute(x, s) for x in X[1:]]
        sY = [mp.substitute(y, s) for y in Y]
        # try unifying remaining elements
        yield from eager_bind(sX, sY, floor-1, variables, sentinels, parse_rules, mp.compose(s, subst), idx+(n,))

    # recursive case: leave X[0] unbound, floor does not change
    yield from eager_bind(X[1:], Y, floor, variables, sentinels, parse_rules, subst, idx+(None,))

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
    def __init__(self, claim, rules, nodes=None, order=None, variables=None, sentinels=None):
        """
        nodes[conclusion] = step justifying conclusion | None if not yet justified
        values of step.dependencies are other node conclusions rather than other proof steps
        variables: the work variables introduced by the search, which can be substituted
        sentinels: the metavariables in the original claim, which should not be substituted
        """
        self.claim = claim
        self.rules = rules

        if nodes is None:
            # substitute claim variables with sentinels (should not be specialized during the proof)
            sentinels = {v: (f"mv{d}",) for (d,v) in enumerate(claim.mandatory.keys())}
            tokens = tuple(mp.substitute(statement.tokens, sentinels) for statement in (claim.consequent,) + claim.essentials)
            self.claim = md.Rule(
                consequent=md.Statement(claim.consequent.label, claim.consequent.tag, tokens[0], ()),
                essentials=[md.Statement(e.label, e.tag, t, ()) for (e,t) in zip(claim.essentials, tokens[1:])],
                floatings=[md.Statement(f.label, f.tag, f.tokens[:1] + sentinels[f.tokens[1]], ()) for f in claim.floatings],
                disjoint=set((sentinels[u][0], sentinels[v][0]) for (u,v) in claim.disjoint),
                variables=set(v[0] for v in sentinels.values()))
            self.claim.finalize()
            # initialize nodes with substituted claim tokens
            self.nodes = {tokens[0]: None} # claim conclusion not justified yet
            for (stmt, toks) in zip(claim.essentials, tokens[1:]):
                rule = md.Rule(stmt, (), (), set(), set())
                rule.finalize()
                self.nodes[toks] = mp.ProofStep(toks, rule)
            # initialize partial order (hypotheses before conclusion)
            self.order = {(t, tokens[0]) for t in tokens[1:]}
            # initialize variables and sentinels
            self.variables = set()
            self.sentinels = set(v[0] for v in sentinels.values())

        else:
            self.nodes = nodes
            self.order = order
            self.variables = variables
            self.sentinels = sentinels

    def __str__(self):
        # s = f"Spout(\n{claim}nodes:\n"
        s = f"Spout(\nconclusion <= rule [h: n'...] (subst):\n"
        for n, (conclusion, step) in enumerate(self.nodes.items()):
            s += ' '.join(conclusion) + " <= "
            if step is None:
                s += "???\n"
            else:
                deps = []
                for (h, d) in step.dependencies.items():
                    deps.append(f"{h}: '{' '.join(d)}'")
                subst = ", ".join(f"{k}: {' '.join(v)}" for k,v in step.substitution.items())
                s += f"{step.rule.consequent.label} [{', '.join(deps)}] ({subst})\n"
        # s += "\n".join(" ".join(n) for n in self.nodes)
        # s += "\nsteps:\n" + "\n".join(' '.join(k) + ": " + str(v) for (k,v) in self.steps.items())
        s += "\nvars: " + str(self.variables) + ", sens: " + str(self.sentinels)
        return s

    def substitute(self, substitution):
        """
        Applies substitution to all nodes in-place
        """
        nodes = {}
        for conclusion, step in self.nodes.items():
            conclusion = mp.substitute(conclusion, substitution)
            if step is not None:
                step = mp.ProofStep(
                    conclusion,
                    step.rule,
                    {h: mp.substitute(d, substitution) for (h,d) in step.dependencies.items()},
                    {v: substitution[v] for v in step.rule.mandatory},
                    disjoint=None) # todo: disjoints
            nodes[conclusion] = step
        order = {(mp.substitute(a, substitution), mp.substitute(b, substitution)) for (a,b) in self.order}
        variables = set([substitution[v] for v in self.variables])
        return Spout(self.claim, self.rules, nodes, order, variables, self.sentinels)

    def proof_check(self, conclusion=None, steps=None):
        """
        conclusion is an intermediate token tuple to be proved (defaults to claim consequent)
        returns (success, proof) where
            success is True if self contains proof else False
            proof is a contained proof if success else None
        """

        # top-level call: set node to claim consequent and init steps (avoid in-place)
        if conclusion is None:
            conclusion = self.claim.consequent.tokens
            steps = {} # steps[conclusion] = step

        # base case: already proven
        if conclusion in steps: return True, steps[conclusion]

        # base case: unjustified
        spout_step = self.nodes[conclusion]
        if spout_step is None: return False, None

        # recursive case: check if all dependencies justified
        dependencies = {} # replace dependency tokens by proof steps
        for h, d in spout_step.dependencies.items():
            success, d_step = self.proof_check(d, steps)
            if not success: return False, None
            dependencies[h] = d_step

        # if this line reached, all dependencies satisfied
        step = mp.ProofStep(conclusion, spout_step.rule, dependencies, spout_step.substitution, spout_step.disjoint)
        steps[conclusion] = step
        return True, step

    def bindings_with(self, rule, variables, node_budget):
        """
        Generates all statement subset bindings of rule with self's nodes
        Handles consequent separately then calls eager_bind on hypotheses
        """

        X = [rule.consequent.tokens[1:]] + [e.tokens[1:] for e in rule.essentials]
        floor = len(X) - node_budget

        # abort if impossible to reach floor
        if len(X) < floor: return

        # first try all bindings including conclusion statement
        for i, (n_c, step) in enumerate(self.nodes.items()):

            # skip already-justified nodes
            if step is not None: continue

            # try unifying consequent
            success, s0 = unify(X[0], n_c[1:], variables, self.sentinels, self.rules["wff"])
            if not success: continue

            # set up order-respecting nodes for hypotheses eager bind
            N_d, reindex = [], {}
            for (j, n_d) in enumerate(self.nodes.keys()):
                if j == i: continue
                if (n_c, n_d) in self.order: continue
                N_d.append(n_d[1:])
                reindex[len(reindex)] = j

            # apply substitution for hypotheses eager bind
            sX = [mp.substitute(x, s0) for x in X[1:]]
            sN_d = [mp.substitute(n_d, s0) for n_d in N_d]
            
            # entry to hypotheses eager bind
            for (s, _, idx) in eager_bind(sX, sN_d, floor-1, variables, self.sentinels, self.rules["wff"], s0, ()):
                # remap idx to full node set and yield
                idx = (i,) + tuple(reindex.get(j, None) for j in idx)
                uN = [mp.substitute(n[1:], s) for n in self.nodes.keys()]
                yield s, uN, idx

        # only try omitting conclusion if floor allows it
        if len(X) == floor: return

        # try all nodes except claim consequent as dependencies
        N_d = [n[1:] for n in self.nodes.keys() if n != self.claim.consequent.tokens]
        # floor unchanged since X[0] unbound
        for (s, _, idx) in eager_bind(X[1:], N_d, floor, variables, self.sentinels, self.rules["wff"]):
            # remap idx to full node set and yield
            idx = (None,) + tuple((None if j is None else j+1) for j in idx) # +1 for omitted claim consequent node
            uN = [mp.substitute(n[1:], s) for n in self.nodes.keys()]
            yield s, uN, idx


    @profile
    def expansions_with(self, rule, node_budget):
        """
        Generates all expansions of self with a new step justified by rule
        node_budget: number of fresh nodes that can be generated
        """

        # standardize apart rule
        variables = set(self.variables)
        name_map = {}
        for v in rule.mandatory.keys():
            u = f"wv{len(variables)}"
            name_map[v] = u
            variables.add(u)
        rule = rule.rename(name_map)

        # unify rule statements with as many existing nodes as possible
        X = [rule.consequent.tokens[1:]] + [e.tokens[1:] for e in rule.essentials]
        N = [n[1:] for n in self.nodes.keys()]
        floor = len(X) - node_budget
        # for (subst, uN, idx) in eager_bind(X, N, floor, variables, self.sentinels, self.rules["wff"]):

        #     # filter out unifications with already-justified conclusions
        #     if idx[0] is not None and self.nodes[("|-",)+N[idx[0]]] is not None: continue
        for (subst, uN, idx) in self.bindings_with(rule, variables, node_budget):

            # apply substitutions
            sX = [mp.substitute(x, subst) for x in X]
            tsX = [("|-",)+sx for sx in sX] # prepend typecodes
            order = set([(mp.substitute(a,subst), mp.substitute(b,subst)) for (a,b) in self.order])

            # filter out redundancies after substitution
            if any(i is None and sx in uN for (i, sx) in zip(idx, sX)): continue

            # filter out self-circularity
            if tsX[0] in tsX[1:]: continue

            # filter out other circularity with order violations
            if any((tsX[0], n_d) in order for n_d in tsX[1:]): continue

            # substitute nodes
            nodes = {}
            for (conclusion, step) in self.nodes.items():
                conclusion = mp.substitute(conclusion, subst)
                if step is not None:
                    # print(subst)
                    # print(step.rule.mandatory)
                    step = mp.ProofStep(
                        conclusion,
                        step.rule,
                        {h: mp.substitute(d, subst) for (h,d) in step.dependencies.items()},
                        # {v: subst[v] for v in step.rule.mandatory},
                        substitution=mp.compose(subst, step.substitution),
                        disjoint=None) # todo: disjoints
                nodes[conclusion] = step

            # add any new nodes
            for (i, tsx) in zip(idx, tsX):
                if i is None: nodes[tsx] = None

            # build new step
            dependencies = {e.label: tsx for (e, tsx) in zip(rule.essentials, tsX[1:])}
            step = mp.ProofStep(tsX[0], rule, dependencies, subst) # todo: disjoint requirements
            nodes[tsX[0]] = step

            # transitive closure of ordering
            n_c = tsX[0]
            for n_d in tsX[1:]:
                order.add((n_d, n_c))
                for n in nodes.keys():
                    if (n_c, n) in order: order.add((n_d, n))
                    if (n, n_d) in order: order.add((n, n_c))

            # check for additional circularity introduced by modifications
            circ = False
            for n_c, step in nodes.items():
                if step is None: continue
                for n_d in step.dependencies.values():
                    if n_c == n_d or (n_c, n_d) in order:
                        circ = True
                        break
                if circ: break
            if circ: continue

            # yield expansion
            yield Spout(self.claim, self.rules, nodes, order, variables, self.sentinels)

    def expansions(self, node_budget):
        """
        Generates all expansions of self with a new step justified by any rule
        node_budget: number of fresh nodes that can be generated
        """
        for rule in self.rules["|-"]:
            yield from self.expansions_with(rule, node_budget)

    def dfs(self, step_cap):
        # base case: steps reached
        num_steps = len([n for (n,s) in self.nodes.items() if s is not None])
        if num_steps == step_cap: yield self
        if num_steps >= step_cap: return

        node_budget = step_cap - num_steps
        for expansion in self.expansions(node_budget):
            yield from expansion.dfs(step_cap)

    def plot(self):
        pass

    def complete_floating(self, step, steps=None):
        """
        Recursively complete sub-proofs of floating dependencies, assumes essentials are all satisfied
        step: root of proof to complete, done in-place
        """
        if steps is None: steps = {}
        # complete dependencies
        for h, d in step.dependencies.items(): self.complete_floating(d, steps)
        # complete step
        for f in step.rule.floatings:
            v = f.tokens[1]
            wff = step.substitution[v]
            proof, _ = parse_proof(self.rules["wff"], wff, self.variables, self.sentinels, steps)
            step.dependencies[f.label] = proof

    def revert_metavariables(self, claim, proof):
        """
        Reverts work variables in proof to canonical metavariable names matching original claim
        proof is root step of proof, assumes floatings were already completed
        proof steps are modified in-place
        todo: handle proof step substitutions correctly
        """
        substitution = {} # replaces working variables with original metavariables
        # rename sentinels
        for (a, b) in zip((claim.consequent,)+claim.essentials, (self.claim.consequent,)+self.claim.essentials):
            for (ta, tb) in zip(a.tokens, b.tokens):
                if tb in self.sentinels: substitution[tb] = (ta,)
        # collect available metavariables not used for sentinels
        metavariables = list(claim.variables - set([v[0] for v in substitution.values()]))
        # rename work variables that made it into proof step conclusions
        workvariables = set()
        for step in proof.all_steps():
            workvariables |= set(step.conclusion) & self.variables
        for v in workvariables:
            substitution[v] = (metavariables[0],)
            metavariables = metavariables[1:]
        # apply substitution to proof
        for step in proof.all_steps():
            step.conclusion = mp.substitute(step.conclusion, substitution)
            if step.rule.consequent.label[:3] == "wmv":
                v = step.rule.consequent.label[1:]
                mv = substitution[v][0]
                step.rule = md.Rule(md.Statement("w"+mv, "$a", ("wff", mv), ()), (), (), (), ())
                step.rule.finalize()
            step.substitution = {k: mp.substitute(v, substitution) for (k,v) in step.substitution.items()}
            step.disjoint = set([(substitution[u][0], substitution[v][0]) for (u,v) in step.disjoint]) # todo: is this right?
            # print(proof.tree_string())
            # input('.')


@profile
def spout_prover(claim, rules, max_proof_size):
    # a "search step" is adding a new node with either essential hypotheses or consequents that unify with one or more existing nodes
    # order all possible search steps so that smaller proofs are guaranteed identified before larger ones
    # bonus: "heuristic" which orders search steps so that proofs, if they exist, are identified sooner in the total search step order.
    # each proof is a satisfied and-or subtree of the spout graph
    print(f"proving {claim}")

    # initialize spout
    seed = Spout(claim, rules)

    # iteratively deepen expansions, starting from nodes in original claim
    for proof_size_limit in range(len(seed.nodes), max_proof_size+1):
        print(f"*** deepening to {proof_size_limit=} ***")

        # try each spout up to current limit
        num_spouts = 0
        for spout in seed.dfs(proof_size_limit):
            num_spouts += 1

            # print()
            # print(spout)

            # check for proof
            success, root_step = spout.proof_check()
            if success:
                print()
                print(spout)
                print()
                spout.complete_floating(root_step)
                spout.revert_metavariables(claim, root_step)
                print(f"at success {num_spouts=}")
                return root_step

        print(f"total {num_spouts=}")

    # towards heuristic:
    # "if the new node of the next search step does not have all essentials and conclusion unified against existing spouts appropriately, min proof size >= h"
    # how about unifying leaves of the consequent spout *with each other* as well as with the essential spouts (both their roots and non-anchor leaves!)? that should help bound dag size.

    return None

if __name__ == "__main__":

    import src.metamathpy.setmm as ms
    db = ms.load_pl()
    parse_rules = [rule for rule in db.rules.values() if rule.consequent.tag == "$a" and rule.consequent.tokens[0] in ("wff", "class")]

    ## multibinder
    test_cases = [ # X, Y, variables, num binders
        (["ph"], ["ph"], ["ph"], 1),
        (["ph"], ["ps"], ["ph","ps"], 1),
        (["ph"], ["ps", "( ps -> ps )"], ["ph","ps"], 2),
        (["ph", "( ph -> ps )"], ["-. u0", "( -. u0 -> -. u1 )"], ["ph","ps","u0","u1"], 1),
    ]
    for (X, Y, V, C) in test_cases:
        X = [tuple(x.split()) for x in X]
        Y = [tuple(y.split()) for y in Y]
        print(X, Y, V, C)
        count = 0
        for s, ys in multibind(X, Y, V, (), parse_rules):
            print("", s, [" ".join(y) for y in ys])
            count += 1
        assert count == C

    ## eagerbinder
    print("\n\n eager bind\n\n")
    for (X, Y, V, C) in test_cases:
        X = [tuple(x.split()) for x in X]
        Y = [tuple(y.split()) for y in Y]
        print(X, Y, V, C)
        count = 0
        floor = len(X) # bind all
        for s, uY, idx in eager_bind(X, Y, floor, V, (), parse_rules):
            print("", s, [" ".join(y) for y in Y])
            count += 1
            assert idx.count(None) == 0
            for x, i in zip(X, idx):
                if i is not None:
                    assert mp.substitute(x, s) == uY[i]
        assert count == C

    for (X, Y, V, C) in test_cases:
        X = [tuple(x.split()) for x in X]
        Y = [tuple(y.split()) for y in Y]
        print(X, Y, V, C)
        floor = len(X) - 1 # at most one unbound
        for s, uY, idx in eager_bind(X, Y, floor, V, (), parse_rules):
            unbound = idx.count(None)
            print(f"{unbound=}", s, [" ".join(mp.substitute(x, s)) for x in X], [None if i is None else " ".join(uY[i]) for i in idx])
            assert len(X) - unbound >= floor
            for x, i in zip(X, idx):
                if i is not None:
                    assert mp.substitute(x, s) == uY[i]

    # proof check
    claim = db.rules["ax-mp"]
    rules = db.rules_up_to("ax-1")
    spout = Spout(claim, rules)
    print(spout)
    result, _ = spout.proof_check()
    assert not result

    spout.nodes[spout.claim.consequent.tokens] = mp.ProofStep(
        conclusion=spout.claim.consequent.tokens,
        rule=claim,
        dependencies={"min": tuple("|- mv0".split()), "maj": tuple("|- ( mv0 -> mv1 )".split())},
        substitution={"ph": ("mv0",), "ps": ("mv1",)},
        disjoint=set())

    print(spout)
    result, proof = spout.proof_check()
    assert result
    print(proof.tree_string())

    ## expansions with
    claim = db.rules["ax-mp"]
    rules = db.rules_up_to("ax-1")
    spout = Spout(claim, rules)
    for e, expansion in enumerate(spout.expansions_with(db.rules['ax-mp'], node_budget=0)):
        print(f"\n\n expansion {e} \n\n")
        print(expansion)
    # input('.')

    claim = db.rules["mp2"]
    rules = db.rules_up_to("mp2")
    spout = Spout(claim, rules)
    print(f"\n\nexpansions of {spout}\n")
    for e, expansion in enumerate(spout.expansions_with(db.rules['ax-mp'], node_budget=1)):
        print(f"\n expansion {e} \n")
        print(expansion)
        # input('.')
        for e2, exp2 in enumerate(expansion.expansions_with(db.rules['ax-mp'], node_budget=1)):
            print(f"\n expansion {e},{e2} \n")
            print(exp2)
            # input('.')
            proved, proof_root = exp2.proof_check()
            if proved:
                print("\n Proof found!!\n")
                print(proof_root.tree_string())
                # input('!')

    proof_root = spout_prover(claim, rules, max_proof_size=5)
    assert proof_root is not None
    print("spout prover proof:")
    print(proof_root.tree_string())
    print(proof_root.normal_proof())
    gold, _ = mp.verify_compressed_proof(db, claim)
    print(gold.normal_proof())
    # input('..')

    ##########################

    # big test

    ##########################

    from time import perf_counter
    import pickle as pk

    goal_labels = ["peirceroll"]
    # goal_labels = [label for (label, rule) in db.rules.items() if rule.consequent.tag == "$p"]
    goal_times = []
    goal_proofs = []
    for gl, goal_label in enumerate(goal_labels):

        print(f"\n *** attempting {goal_label} ({gl} of {len(goal_labels)})... ***\n")
        start_time = perf_counter()

        claim = db.rules[goal_label]
        rules = db.rules_up_to(goal_label)
        proof_root = spout_prover(claim, rules, max_proof_size=10)

        total_time = perf_counter()-start_time

        # verify proof
        if proof_root is not None:
            # print(proof_root.tree_string())
            
            old_root, _ = mp.verify_compressed_proof(db, claim)
            old_normal_proof = old_root.normal_proof()
            new_normal_proof = proof_root.normal_proof()

            new_size = len([s for s in proof_root.all_steps() if s.conclusion[0] == "|-"])
            old_size = len([s for s in old_root.all_steps() if s.conclusion[0] == "|-"])
            # new_size = len(proof_root.all_steps())
            # old_size = len(old_root.all_steps())

            # old_root, _ = mp.verify_compressed_proof(db, claim)
            # old_normal_proof = old_root.normal_proof()
            claim.consequent = md.Statement(claim.consequent.label, claim.consequent.tag, claim.consequent.tokens, new_normal_proof)
            mp.verify_normal_proof(db, claim) # raises assertion error if unverified
            print("Verified!")
            print(f"old proof ({old_size} steps): " + " ".join(old_normal_proof))
            if new_size > old_size:
                print(old_root.tree_string())
            print(f"new proof ({new_size} steps): " + " ".join(new_normal_proof))
            if new_size > old_size:
                print(proof_root.tree_string())
            print(f"total time: {total_time:.3f}s")
            if new_size < old_size:
                print("You found one!!!")
                input('__')
            if new_size > old_size:
                print("Something wrong with iterative largening...")
                input('.')

            goal_times.append(total_time)
            goal_proofs.append(new_normal_proof)
            with open("spout_results.pkl", "wb") as f:
                pk.dump((goal_labels[:len(goal_times)], goal_times, goal_proofs), f)

        else:
            print("no proof found ...")
            break

    with open("spout_results.pkl", "rb") as f:
        results = pk.load(f)
        for (label, time, proof) in zip(*results):
            print(f"{label} proved in {time:.3f}s: {' '.join(proof)}")
