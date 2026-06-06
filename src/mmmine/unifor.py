import src.metamathpy.proof as mp
# import src.metamathpy.terms as mt
import src.metamathpy.cterms as mt

try:
    profile
except NameError:
    profile = lambda x: x

class PartialProof:
    def __init__(self, assertions, justifications, dependencies, used):
        """
        assertions[i]: term for the ith assertion
        justifications[i]: label of the rule justifying assertion i
        dependencies[i]: sequence of dependency step indices, same order as justifying rule's essentials
        used[i]: True if step i is a dependency of a later step, False otherwise
        """
        self.assertions = assertions
        self.justifications = justifications
        self.dependencies = dependencies
        self.used = used

    def to_string(self, term_manager):
        steps = []
        for i, (a,j,d) in enumerate(zip(self.assertions, self.justifications, self.dependencies)):
            steps.append(f"{i}: {j}{list(d)} |- " + " ".join(term_manager.serialize(a)))
        return "\n".join(steps)

    def copy(self):
        return PartialProof(
            [a.copy() for a in self.assertions],
            list(self.justifications), list(self.dependencies), list(self.used))

    @profile
    def substitute(self, substitution):
        return PartialProof(
            [mt.substitute(a, substitution) for a in self.assertions],
            list(self.justifications), list(self.dependencies), list(self.used))

    def standardize(self, variables, floor):
        """
        rename all variables in self so that they remain distinct and all are larger than floor
            variables: the tokens to be considered variables
            floor: variable int ids above floor are assumed available
        for example, floor is the highest int id occurring in rule index
        """

    @profile
    def unify_with(self, terms, index, variables, use_quota):
        """
        generates unifications of each term with multisubset of self's assertions up to index
        yields proof, substituted version of self that unified
        variables is set of variable integer ids passed to mt.unify
        use_quota is the minimum number of self's assertions that need to become used
        """

        # base case: impossible to meet quota
        if len(terms) < use_quota:
            return # unreachable code?

        # base case: all terms processed
        if len(terms) == 0:
            # only successful if quota is met
            if use_quota <= 0: yield self
            return

        # try unifying next term with each of self's assertions
        for i in range(index):

            # skip this assertion if already used so won't meet quota
            if self.used[i] and len(terms) == use_quota: continue

            # find unifying substitution (skip if none)
            substitution = mt.unify(terms[0], self.assertions[i], variables)
            if substitution is None: continue

            # update copy of proof substituted with this unification
            partial_proof = self.substitute(substitution)
            partial_proof.dependencies[index] = partial_proof.dependencies[index] + (i,)
            partial_proof.used[i] = True

            # recurse on remaining terms
            remaining_terms = [mt.substitute(t, substitution) for t in terms[1:]]
            new_usage = (not self.used[i])
            yield from partial_proof.unify_with(remaining_terms, index, variables, use_quota - new_usage)

    @profile
    def unify_with_filtered(self, terms, index, indices, variables, use_quota):
        """
        generates unifications of each term with multisubset of self's assertions in indices
        yields proof, substituted version of self that unified
        index is for the assertion being justified whose dependencies are updated
        indices[i] is the filtered set of assertion indices that terms[i] should be unified against
        variables is set of variable integer ids passed to mt.unify
        use_quota is the minimum number of self's assertions that need to become used
        """

        # base case: impossible to meet quota
        if len(terms) < use_quota:
            return # unreachable code?

        # base case: all terms processed
        if len(terms) == 0:
            # only successful if quota is met
            if use_quota <= 0: yield self
            return

        # try unifying next term with next filtered subset of self's assertions
        for i in indices[0]:

            # skip this assertion if already used so won't meet quota
            if self.used[i] and len(terms) == use_quota: continue

            # find unifying substitution (skip if none)
            substitution = mt.unify(terms[0], self.assertions[i], variables)
            if substitution is None: continue

            # update copy of proof substituted with this unification
            partial_proof = self.substitute(substitution)
            partial_proof.dependencies[index] = partial_proof.dependencies[index] + (i,)
            partial_proof.used[i] = True

            # recurse on remaining terms
            remaining_terms = [mt.substitute(t, substitution) for t in terms[1:]]
            new_usage = (not self.used[i])
            yield from partial_proof.unify_with_filtered(remaining_terms, index, indices[1:], variables, use_quota - new_usage)

    def initialized_for(claim, proof_size, term_manager):
        tail_size = proof_size - len(claim.essentials)
        assertions = []

        # parse assertion terms for essential hypotheses
        for h in claim.essentials:
            term = term_manager.parse(h.tokens[1:], set(claim.mandatory.keys()))
            assertions.append(term)

        # make assertion terms for intermediate steps, initialized to step variables
        variables = set()
        for d in range(tail_size-1):
            step_variable = f"step{d}"
            term = term_manager.token_term(step_variable)
            assertions.append(term)
            variables.add(term_manager.encode(step_variable))

        # parse assertion term for consequent
        term = term_manager.parse(claim.consequent.tokens[1:], set(claim.mandatory.keys()))
        assertions.append(term)

        # initialize justifications and bindings for each step
        justifications = [h.label for h in claim.essentials] + ["" for d in range(tail_size)]
        dependencies = [() for _ in range(proof_size)]
        used = [False for _ in range(proof_size)]

        return PartialProof(assertions, justifications, dependencies, used), variables

class SearchNode:
    def __init__(self, db, claim, rules, partial_proof, variables, term_manager):
        self.db = db
        self.claim = claim
        self.rules = rules # {len(essentials): [..., (mandatory variable ints, essential termss, consequent term), ...], ...}
        self.partial_proof = partial_proof
        self.variables = variables
        self.term_manager = term_manager

    def proof_string(self):
        return self.partial_proof.to_string(self.term_manager)

    def canonicalized_partial_proof(self):
        """
        Reverts work variables in self.partial_proof to canonical metavariable names
        assumes proof is complete and correct
        returns substituted partial proof
        """

        # identify claim metavariables (should not be replaced)
        claim_variables = set(map(self.term_manager.encode, self.claim.mandatory.keys()))

        # collect canonical metavariables
        canonical_variables = set(map(self.term_manager.encode, self.claim.variables))

        # filter those not used in claim
        available_variables = canonical_variables - claim_variables

        # collect work variables in proof
        work_variables = set()
        for a in self.partial_proof.assertions:
            # work_variables |= (set(a[:,0]) & self.variables)
            work_variables |= (set([u for (u,_) in a]) & self.variables)
        work_variables -= claim_variables # is this necessary? self.variables should really be self.work_variables?

        # substitute work variables with terms for canonical ones
        available_variables = [mt.singleton_term(v) for v in available_variables]
        substitution = dict(zip(list(work_variables), available_variables))
        return self.partial_proof.substitute(substitution)

    def reconstruct_proof(self):
        """
        Converts self.partial_proof to an mp.ProofStep DAG
        Assumes self.partial_proof is complete and correct
        Returns the root ProofStep
        """
        # TODO: disjoint variable requirements
        print(self.proof_string())

        steps = {}
        p = self.canonicalized_partial_proof()

        for n,(a,j,d) in enumerate(zip(p.assertions, p.justifications, p.dependencies)):

            # bind the consequent of the rule justifying current step
            rule = self.db.rules[j]
            # substitution = self.term_manager.bind(rule.consequent.tokens[1:], set(rule.mandatory.keys()), a)
            substitution = self.term_manager.instantiate(rule.consequent.tokens[1:], set(rule.mandatory.keys()), a)
            conclusion = ("|-",) + self.term_manager.serialize(a)
            assert conclusion not in steps # proof search should not produce redundant steps 

            # bind justification's essential hypotheses to previous proof steps
            dependencies = {}
            for i,h in zip(d, rule.essentials):
                dependency = steps[("|-",) + self.term_manager.serialize(p.assertions[i])]
                dependencies[h.label] = dependency
                # substitution |= self.term_manager.bind(h.tokens[1:], set(rule.mandatory.keys()), p.assertions[i])
                substitution |= self.term_manager.instantiate(h.tokens[1:], set(rule.mandatory.keys()), p.assertions[i])

            # insert the proofs of floating hypotheses
            for f in rule.floatings:
                dependencies[f.label] = self.term_manager.parse_proof(substitution[f.tokens[1]], steps)

            # save the step
            substitution = {v: self.term_manager.serialize(t) for (v,t) in substitution.items()}
            step = mp.ProofStep(conclusion, rule, dependencies, substitution)
            steps[conclusion] = step

        return step

    @profile
    def applications_of(self, label, essentials, consequent, step_index, variables, use_quota):

        # for all step indices before the last, consequent unifies trivially with step's work variable
        # (only true for pure forward search)
        if step_index + 1 < len(self.partial_proof.assertions):
            partial_proof = self.partial_proof.copy()
            partial_proof.assertions[step_index] = consequent

        # otherwise, see if rule consequent unifies with claim consequent
        else:
            substitution = mt.unify(consequent, self.partial_proof.assertions[step_index], variables)
            if substitution is None: return

            # apply viable substitution to essential hypotheses
            essentials = [mt.substitute(e, substitution) for e in essentials]
        
            # and to partial proof? is this a vacuous substitution?
            partial_proof = self.partial_proof.substitute(substitution)

        # record this rule as justification
        partial_proof.justifications[step_index] = label

        # # continue unifying substituted proof with substituted essentials
        # yield from partial_proof.unify_with(essentials, step_index, variables, use_quota)

        # filter unifiable indices for each substituted essential
        indices = []
        for e in essentials:
            indices.append([])
            for i in range(step_index):
                s = mt.unify(e, partial_proof.assertions[i], variables)
                if s is not None: indices[-1].append(i)

        # continue unifying substituted essentials with filtered substituted proof steps
        yield from partial_proof.unify_with_filtered(essentials, step_index, indices, variables, use_quota)

    @profile
    def dfs(self, step_index=None):

        if step_index is None:
            step_index = len(self.claim.essentials)

        proof_size = len(self.partial_proof.assertions)
        if step_index == proof_size:
            yield self
            return

        # Determine how many essentials are needed to use all steps
        max_essentials = max(self.rules.keys())
        num_unused = sum((not u) for u in self.partial_proof.used) - 1 # -1 for claim consequent
        steps_remaining = proof_size - step_index
        min_essentials = max(0, num_unused - (steps_remaining - 1) * max_essentials)

        # skip if impossible to use all steps
        if min_essentials > max_essentials: return

        # collect rules with enough essential hypotheses
        # TODO: consider prioritizing rules with 1+ essentials and unifying with most recent assertions first, to avoid repeating the same reasoning multiple times    
        rules = sum([self.rules[h] for h in self.rules if h >= min_essentials], [])
        for rule in rules:
            label, mandatory, essentials, consequent = rule

            # standardize apart rule statements
            offset = max(set(self.term_manager.encoder.values()) | self.variables) + 1 # starting integer for new variables
            s = {v: (offset + m) for (m, v) in enumerate(mandatory)}
            essentials = [mt.rename(e, s) for e in essentials]
            consequent = mt.rename(consequent, s)
            variables = self.variables | set(s.values())

            # recurse on all valid rule applications
            for partial_proof in self.applications_of(label, essentials, consequent, step_index, variables, min_essentials):
                child = SearchNode(self.db, self.claim, self.rules, partial_proof, variables, self.term_manager)
                yield from child.dfs(step_index + 1)


@profile
def ids(db, claim, entailment_rules, term_manager, max_proof_size):
    print(f"proving {claim}")

    # iteratively deepen expansions, starting from nodes in original claim
    for proof_size in range(len(claim.essentials)+1, max_proof_size+1):
        print(f"*** deepening to {proof_size=} ***")

        # try each proof up to current limit
        initial_proof, variables = PartialProof.initialized_for(claim, proof_size, term_manager)
        search_root = SearchNode(db, claim, entailment_rules, initial_proof, variables, term_manager)
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

    max_depth = 2

    do_run = True
    exclude_list = ms.new_usage_discouraged()
    start_from_goal_index = 0 #175 jad # 1374 syl332anc took 24223s before unify_with_filter
    stop_after = 100

    db = ms.load_pl()
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
    
            # convert entailment rules to terms, grouped by essential count
            print("termifying...")
            entailment_rules = {}
            for rule in rules["|-"]:
    
                # term conversions
                essentials = [term_manager.parse(h.tokens[1:], set(rule.mandatory.keys())) for h in rule.essentials]
                consequent = term_manager.parse(rule.consequent.tokens[1:], set(rule.mandatory.keys()))
                mandatory = set([term_manager.encode(t) for t in rule.mandatory.keys()])
    
                # group by essential count
                if len(essentials) not in entailment_rules: entailment_rules[len(essentials)] = []
                entailment_rules[len(essentials)].append((rule.consequent.label, mandatory, essentials, consequent))
    
            print("searching...")
            proof_root = ids(db, claim, entailment_rules, term_manager, len(claim.essentials)+max_depth)
    
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
                    input('__')
    
                # # print(proof.to_string(term_manager))
                # print(proof.tree_string())
                # input('..')
    
                goal_proofs[goal_label] = new_normal_proof

                with open("ufr.pkl","wb") as f: pk.dump((goal_proofs, goal_times, shortened), f)

    with open("ufr.pkl","rb") as f: (goal_proofs, goal_times, shortened) = pk.load(f)

    print(f"Grand total time = {sum(goal_times.values())}s, {len(goal_proofs)} of {len(goal_times)} proved, {len(shortened)} shortened:")
    print(shortened)

