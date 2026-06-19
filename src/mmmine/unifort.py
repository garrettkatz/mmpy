import src.metamathpy.proof as mp
import src.metamathpy.terms as mt
from src.metamathpy.term_trie import TermTrieNode

MAX_REM_PRUNE = True
NUM_HITS = 0
NUM_MISS = 0

try:
    profile
except NameError:
    profile = lambda x: x

def termify(term_manager, rule):
    """
    Converts statements in a rule to terms
    Returns (consequent, essentials, mandatory)
        consequent: term for rule's consequent
        essentials[i]: term for rule's ith essential hypothesis
        mandatory: set of int ids for mandatory variables in rule
    """
    consequent = term_manager.parse(rule.consequent.tokens[1:], set(rule.mandatory.keys()))
    essentials = [term_manager.parse(h.tokens[1:], set(rule.mandatory.keys())) for h in rule.essentials]
    mandatory = {term_manager.encode(t) for t in rule.mandatory.keys()}
    return (consequent, essentials, mandatory)

class WorkingProof:
    def __init__(self, assertions, justifications, dependencies, used, variables, term_manager):
        """
        assertions[i]: term for the ith assertion
        justifications[i]: label of the rule justifying assertion i
        dependencies[i]: sequence of dependency step indices, same order as justifying rule's essentials
        used[i]: True if step i is a dependency of a later step, False otherwise
        variables: set of working variables (can be substituted)
        offset: starting int id for fresh variables
        term_manager: used for printing
        """
        self.assertions = assertions
        self.justifications = justifications
        self.dependencies = dependencies
        self.used = used
        self.variables = variables
        self.term_manager = term_manager

    def __str__(self):
        lines = [f"vars={self.variables}:"]
        for i, (a,j,d) in enumerate(zip(self.assertions, self.justifications, self.dependencies)):
            lines.append(f"{i}: {j}{list(d)} |- " + " ".join(self.term_manager.serialize(a)))
        return "\n".join(lines)

    def initialize(consequent, essentials, offset, proof_size, term_manager):
        """
        Initialize working proof for claim
            consequent: term for claim consequent
            essentials[i] = (label, term) for ith essential statement
            offset: starting integer id for fresh variables
            proof_size: number of essential proof steps
            term_manager: for printing
        """

        # make assertion terms for intermediate steps, initialized to fresh step variables
        num_intermediate = proof_size - (len(essentials) + 1)
        assertions = []
        variables = set()
        for s in range(num_intermediate):
            assertions.append(mt.singleton_term(offset + s))
            variables.add(offset + s)

        # set up all step data
        if len(essentials) > 0:
            essential_labels, essential_terms = map(list, zip(*essentials))
        else:
            essential_labels, essential_terms = [], []
        assertions = essential_terms + assertions + [consequent]
        justifications = essential_labels + [""] * (proof_size - len(essentials))
        dependencies = [()] * proof_size
        used = [False] * proof_size

        return WorkingProof(assertions, justifications, dependencies, used, variables, term_manager)

    def standardize_apart(self, offset):
        standardizer = {v: offset + i for (i, v) in enumerate(self.variables)}
        assertions = [mt.rename(a, standardizer) for a in self.assertions]
        variables = set(standardizer.values())
        return WorkingProof(assertions, list(self.justifications), list(self.dependencies), list(self.used), variables, self.term_manager)

    @profile
    def substitute(self, substitution, replacement_variables):
        """
        replacement_variables: superset of variables occurring in substitution's replacement terms
        """

        # apply substitution to assertions
        assertions = [mt.substitute(a, substitution) for a in self.assertions]

        # remove variables that have been substituted out
        variables = self.variables - set(substitution.keys())

        # incorporate variables in replacements
        for replacement in substitution.values():
            variables |= {v for (v,_) in replacement if v in replacement_variables}

        # return new proof after substitution
        return WorkingProof(assertions, list(self.justifications), list(self.dependencies), list(self.used), variables, self.term_manager)

    def swap_assertion(self, step_index, new_assertion, variables):
        """
        Returns copy of self with new_assertion at step_index
        variables: must be superset of variables occurring in self or new_assertion
        """

        # insert assertion
        assertions = self.assertions[:step_index] + [new_assertion] + self.assertions[step_index+1:]

        # filter to variables occurring in new assertion list
        variables = {v for a in assertions for (v,_) in a if v in variables}

        return WorkingProof(assertions, list(self.justifications), list(self.dependencies), list(self.used), variables, self.term_manager)

def essential_unifications(essential_trie, working_proof, step_depth, variables, sub=None, dep_idx=(), use_quota=None):
    """
    Helper to unify nested essential tries with multisubset of working proof steps up to step_depth
    yields substituted working proof after unification
    variables: must be superset of variables occurring in essential_trie or working_proof
    use_quota: the minimum number of working proof's assertions that need to become used in yielded proof
    """

    # more complicated:
    # whereas unifor had fixed number of terms, different paths in essential_trie could have different numbers of remaining terms
    # can/should you maintain at each trie node the maximum number of remaining terms below it, to prune more here?

    # defaults
    if sub is None: sub = {}
    if use_quota is None: use_quota = 0 # dont need to use any unless specified

    # apply sub to working_proof
    # print("pre-sub:")
    # print(working_proof)
    working_proof = working_proof.substitute(sub, variables)
    # print("post-sub:")
    # print(working_proof)

    for i in range(step_depth):
        new_dep_idx = dep_idx + (i,)

        # count new usages
        new_usage = sum(int((not u) and (a in new_dep_idx)) for (a,u) in enumerate(working_proof.used))

        # print(f"trying unis with step {i}: {' '.join(working_proof.term_manager.serialize(working_proof.assertions[i]))}")
        for (new_sub, path_term, data) in essential_trie.unifications_with(working_proof.assertions[i], variables, sub):
            # print(f"essential trie unification: sub={new_sub}")
            # print(f"path term {' '.join(working_proof.term_manager.serialize(path_term))}")
            # print(f"with step {i}:")
            # print(' '.join(working_proof.term_manager.serialize(working_proof.assertions[i])))
            # print("finished labels:", [label for (label,_) in data[0]])

            complete_rules, incomplete_rule_trie, max_remaining_rule_terms = data

            # only yield at this point if new usage meets quota
            if new_usage >= use_quota:
                for (label, consequent) in complete_rules:
                    # replace step_depth assertion with consequent
                    sub_working_proof = working_proof.swap_assertion(step_depth, consequent, variables)
                    # apply substitution
                    sub_working_proof = sub_working_proof.substitute(new_sub, variables)
                    sub_working_proof.justifications[step_depth] = label
                    sub_working_proof.dependencies[step_depth] = new_dep_idx
                    for di in new_dep_idx: sub_working_proof.used[di] = True
                    yield sub_working_proof

            # only recurse if enough terms left to meet quota
            if MAX_REM_PRUNE:
                global NUM_HITS, NUM_MISS
                if new_usage + max_remaining_rule_terms < use_quota:
                    NUM_HITS += 1
                    continue
                NUM_MISS += 1

            # print("recursing on next trie:")
            # print(incomplete_rule_trie.tree_string(working_proof.term_manager))
            yield from essential_unifications(incomplete_rule_trie, working_proof, step_depth, variables, new_sub, new_dep_idx, use_quota)

class RuleIndex:
    def __init__(self, rules, term_manager):
        """
        rules: list of rule objects to be indexed
        term_manager: for encoding the rules

        has several chained tries for indexing operations

        trie node data has the form (rules, next_trie, max_remaining) where
            rules is a list of (label, consequent) for rules whose terms end at this node
            next trie is for the next term in rules that do not end at this node
            max_remaining is the maximum number of remaining terms in all rules below this node
        """
        self.term_manager = term_manager
        self.max_essentials = 0

        self.essential_less = [] # list of essential-less rules

        # keyed for rules with >= n essentials for each occurring n
        self.consequent_trie = {} # min essentials: trie
        self.essentials_trie = {} # min essentials: trie
        self.variables = {} # min essentials: variable set

        for rule in rules:
            consequent, essentials, mandatory = termify(term_manager, rule)
            self.max_essentials = max(self.max_essentials, len(essentials))

            # essential-less rules
            if len(essentials) == 0:
                self.essential_less.append((rule.consequent.label, consequent))

            for ne in range(len(essentials)+1):

                if ne not in self.variables: self.variables[ne] = set()
                self.variables[ne] |= mandatory
    
                # print(f"incorporating {rule}")
    
                ## consequent-specific trie
                if ne not in self.consequent_trie:
                    self.consequent_trie[ne] = TermTrieNode()
    
                # incorporate consequent
                node = self.consequent_trie[ne].incorporate(consequent)
                if node.data is None:
                    node.data = [[], TermTrieNode(), 0]
                node.data[2] = max(node.data[2], len(essentials))
    
                # incorporate any essentials
                for e, essential in enumerate(essentials):
                    node = node.data[1].incorporate(essential)
                    if node.data is None:
                        node.data = [[], TermTrieNode(), 0]
                    node.data[2] = max(node.data[2], len(essentials)-e-1)
    
                # store the rule label and consequent term
                node.data[0].append((rule.consequent.label, consequent))
    
                # for essential-less rules, skip consequent-agnostic indexing
                if len(essentials) == 0: continue
    
                ## essential-full consequent-agnostic trie
                if ne not in self.essentials_trie:
                    self.essentials_trie[ne] = TermTrieNode()
    
                # incorporate first essential
                node = self.essentials_trie[ne].incorporate(essentials[0])
                if node.data is None:
                    node.data = [[], TermTrieNode(), 0]
                node.data[2] = max(node.data[2], len(essentials)-1)
    
                # incorporate any remaining essentials
                for e, essential in enumerate(essentials[1:]):
                    node = node.data[1].incorporate(essential)
                    if node.data is None:
                        node.data = [[], TermTrieNode(), 0]
                    node.data[2] = max(node.data[2], len(essentials)-2)
    
                # store the rule label and consequent term
                node.data[0].append((rule.consequent.label, consequent))

    def tree_string(self, node, prefix=""):
        if node.data is None:
            s = [""]
        else:
            s = [str([label for (label,_) in node.data[0]]) + "\n" + self.tree_string(node.data[1], prefix+" ")]
        for (t,n), child in node.branches.items():
            cs = self.tree_string(child, prefix+" ")
            s.append(f"{prefix}{self.term_manager.decode(t)} [{t},:{n}] {cs}")
        return "\n".join(s)

    def consequent_specific_unifications(self, working_proof, step_depth, min_essentials):
        """
        Yields substituted working proofs after unifying with rule index
        Only yields results with at least min_essentials new usages
        Unifies rule consequents with working_proof.assertions[step_depth] and hypotheses with working_proof.assertions[:step_depth]
        """
        conclusion = working_proof.assertions[step_depth]
        variables = self.variables[min_essentials] | working_proof.variables
        for (sub, path_term, data) in self.consequent_trie[min_essentials].unifications_with(conclusion, variables):
            # applicable rules without essentials
            for (label, _) in data[0]:
                sub_working_proof = working_proof.substitute(sub, variables)
                sub_working_proof.justifications[step_depth] = label
                yield sub_working_proof
            # applicable rules with essentials
            # print(f"consequent-specific unified {' '.join(working_proof.term_manager.serialize(path_term))} with step {step_depth}")
            yield from essential_unifications(data[1], working_proof, step_depth, variables, sub, use_quota=min_essentials)

    def consequent_agnostic_unifications(self, working_proof, step_depth, min_essentials):
        variables = self.variables[min_essentials] | working_proof.variables
        # essential-less rules, unless min_essentials is > 0
        if min_essentials == 0:
            for (label, consequent) in self.essential_less:
                # replace step_depth assertion with consequent
                sub_working_proof = working_proof.swap_assertion(step_depth, consequent, variables)
                sub_working_proof.justifications[step_depth] = label
                yield sub_working_proof
        # essential-full rules
        yield from essential_unifications(self.essentials_trie[min_essentials], working_proof, step_depth, variables, use_quota=min_essentials)

class SearchNode:
    def __init__(self, db, claim, rule_index, working_proof, offset):
        """
        offset: offset for fresh variable ids, beyond ids in rule index and termified claim
        """
        self.db = db
        self.claim = claim
        self.rule_index = rule_index
        self.working_proof = working_proof
        self.offset = offset

    def canonicalize_working_proof(self, standardizer):
        """
        Reverts variables in self.working_proof to canonical metavariable names in set.mm
        assumes proof is complete and correct
        returns substituted working proof
        standardizer: the rename map originally used to standardize claim apart
        """

        proof = self.working_proof

        # revert claim metavariable names
        substitution = {u:v for (v,u) in standardizer.items()}
        claim_variables = set(standardizer.keys())

        # collect canonical metavariables
        canonical_variables = set(map(proof.term_manager.encode, self.claim.variables))

        # filter those not used in claim
        available_variables = canonical_variables - claim_variables

        # rename any remaining variables in proof
        assert len(available_variables) >= len(proof.variables)
        for (u,v) in zip(proof.variables, available_variables):
            substitution[u] = v

        # perform renaming
        assertions = [mt.rename(a, substitution) for a in proof.assertions]
        proof_variables = set(substitution.values())
        return WorkingProof(assertions, list(proof.justifications), list(proof.dependencies), list(proof.used), proof_variables, proof.term_manager)

    def reconstruct_proof(self, standardizer):
        """
        Converts self.partial_proof to an mp.ProofStep DAG
        Assumes self.partial_proof is complete and correct
        Returns the root ProofStep
        standardizer: the rename map originally used to standardize claim apart
        """
        # TODO: disjoint variable requirements

        steps = {}
        p = self.canonicalize_working_proof(standardizer)

        for n,(a,j,d) in enumerate(zip(p.assertions, p.justifications, p.dependencies)):

            # instantiate the consequent of the rule justifying current step
            rule = self.db.rules[j]
            substitution = p.term_manager.instantiate(rule.consequent.tokens[1:], set(rule.mandatory.keys()), a)
            conclusion = ("|-",) + p.term_manager.serialize(a)
            assert conclusion not in steps # proof search should not produce redundant steps 

            # instantiate justification's essential hypotheses on previous proof steps
            dependencies = {}
            for i,h in zip(d, rule.essentials):
                dependency = steps[("|-",) + p.term_manager.serialize(p.assertions[i])]
                dependencies[h.label] = dependency
                substitution |= p.term_manager.instantiate(h.tokens[1:], set(rule.mandatory.keys()), p.assertions[i])

            # insert the proofs of floating hypotheses
            for f in rule.floatings:
                dependencies[f.label] = p.term_manager.parse_proof(substitution[f.tokens[1]], steps)

            # save the step
            substitution = {v: p.term_manager.serialize(t) for (v,t) in substitution.items()}
            step = mp.ProofStep(conclusion, rule, dependencies, substitution)
            steps[conclusion] = step

        return step

    def dfs(self, step_depth=None):

        # print("current working proof:")
        # print(self.working_proof)
        # input('.')

        # default: start after last essential hypothesis
        if step_depth is None:
            step_depth = len(self.claim.essentials)

        proof_size = len(self.working_proof.assertions)
        if step_depth == proof_size:
            yield self
            return

        # Determine how many essentials are needed to use all steps
        max_essentials = self.rule_index.max_essentials
        num_unused = sum((not u) for u in self.working_proof.used) - 1 # -1 for claim consequent
        steps_remaining = proof_size - step_depth
        min_essentials = max(0, num_unused - (steps_remaining - 1) * max_essentials)

        # skip if impossible to use all steps
        if min_essentials > max_essentials: return

        # standardize working proof apart from rule index
        working_proof = self.working_proof.standardize_apart(self.offset)

        # print(working_proof)
        # input('standardized ^^')

        # consequent-specific unifications at last step
        if step_depth + 1 == proof_size:
            for sub_working_proof in self.rule_index.consequent_specific_unifications(working_proof, step_depth, min_essentials):
                # print(working_proof)
                # input("consequent-specific generated this working_proof ^^")
                child = SearchNode(self.db, self.claim, self.rule_index, sub_working_proof, self.offset)
                yield child

        # consequent-agnostic unifications at previous steps
        else:
            for sub_working_proof in self.rule_index.consequent_agnostic_unifications(working_proof, step_depth, min_essentials):
                # print(working_proof)
                # input("consequent-agnostic generated this working_proof ^^")
                child = SearchNode(self.db, self.claim, self.rule_index, sub_working_proof, self.offset)
                yield from child.dfs(step_depth + 1)

        return

def ids(db, claim, rule_index, term_manager, max_proof_size):
    """
    Assumes term manager has already encoded rule index
    """
    print(f"proving {claim}")
    print(f"old proof: {' '.join(claim.consequent.proof)}")

    # termify claim
    consequent, essentials, mandatory = termify(term_manager, claim)

    # standardize claim variables apart from existing terms
    offset = len(term_manager.encoder) + 1
    standardizer = {v: offset+i for (i,v) in enumerate(mandatory)}
    consequent = mt.rename(consequent, standardizer)
    essentials = [(h.label, mt.rename(e, standardizer)) for (h,e) in zip(claim.essentials, essentials)]
    sentinels = set(standardizer.keys())
    offset = offset + len(mandatory)

    # iteratively deepen expansions, starting from nodes in original claim
    for proof_size in range(len(essentials)+1, max_proof_size+1):
        print(f"*** deepening to {proof_size=} ***")

        # try each proof up to current limit
        initial_proof = WorkingProof.initialize(consequent, essentials, offset, proof_size, term_manager)
        search_root = SearchNode(db, claim, rule_index, initial_proof, offset)
        for search_leaf in search_root.dfs():

            # completed_proof = search_leaf.canonicalize_working_proof(standardizer)
            # print(completed_proof)
            # input("Completed proof, canonicalized ^^")

            # check for proof
            root_step = search_leaf.reconstruct_proof(standardizer)
            if root_step is not None: return root_step

    return None

if __name__ == "__main__":

    from time import perf_counter
    import pickle as pk
    import src.metamathpy.setmm as ms
    import src.metamathpy.database as md

    max_depth = 2

    do_run = True
    do_reload = True
    do_skip = True
    exclude_list = ms.new_usage_discouraged()
    start_from_goal_index = 1443 # 783 (d3->2) #175 jad # 1374 syl332anc took 24223s before unify_with_filter
    stop_after = -1

    db = ms.load_pl()
    # goal_labels = ["id"]
    goal_labels = [label for (label, rule) in db.rules.items() if rule.consequent.tag == "$p" and label[-3:] not in ("ALT", "OLD") and label not in exclude_list]

    if do_run:

        if do_reload:
            with open("ufrt.pkl","rb") as f: (goal_times, goal_proofs, novel, short) = pk.load(f)
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


            # build rule indexan index for entailment rules
            # consequent_trie -> index data is (rules, subtrie)
            #    each rule in rules: a rule object with consequent corresponding to path and zero hypotheses
            #    subtrie: entrypoint to first hypothesis trie for all rules with 1+ hypotheses and consequent corresponding to path
            #    index also supports pruning mechanisms:
            #         prune if min(num_essentials, max_essentials) < min_essentials
            #         prune if num_unifies > unify_budget? inner ids on this budget
            print("Building rule index...")
            # rule_index = RuleIndex([r for r in rules["|-"] if r.consequent.label in ("ax-mp", "ax-1")], term_manager)
            rule_index = RuleIndex(rules["|-"], term_manager)
            
            # print("\n **** rule consequent-specific trie ****\n")
            # print(rule_index.tree_string(rule_index.consequent_trie[0]))
            # print("\n **** rule consequent-agnostic trie ****\n")
            # print(rule_index.tree_string(rule_index.essentials_trie[0]))
            # print("\n **** rule essential-less list ****\n")
            # for (label, consequent) in rule_index.essential_less:
            #     print(label, ' '.join(term_manager.serialize(consequent)), consequent)
            # input('.%%')

            print("searching...")
            max_proof_size = len(claim.essentials)+max_depth
            proof_root = ids(db, claim, rule_index, term_manager, max_proof_size)
    
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

            with open("ufrt.pkl","wb") as f: pk.dump((goal_times, goal_proofs, novel, short), f)

    with open("ufrt.pkl","rb") as f: (goal_times, goal_proofs, novel, short) = pk.load(f)

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
        
    print(f"{NUM_HITS=}")
    print(f"{NUM_MISS=}")

