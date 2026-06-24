import src.metamathpy.proof as mp
import src.metamathpy.terms as mt
from src.metamathpy.term_trie import TermTrieNode

try:
    profile
except NameError:
    profile = lambda x: x

class WorkingProof:
    def __init__(self, claim, assertions, justifications, dependencies, used, variables, term_manager):
        """
        claim: Rule object being proved
        assertions[i]: term for the ith assertion
        justifications[i]: label of the rule justifying assertion i
        dependencies[i]: sequence of dependency step indices, same order as justifying rule's essentials
        used[i]: True if step i is a dependency of a later step, False otherwise
        variables: set of working variables (can be substituted)
        offset: starting int id for fresh variables
        term_manager: used for printing
        """
        self.claim = claim
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

    def copy(self):
        return WorkingProof(
            self.claim, self.assertions, list(self.justifications), list(self.dependencies), list(self.used), set(self.variables), self.term_manager)

    def initialize(claim, consequent, essentials, offset, proof_size, term_manager):
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

        return WorkingProof(claim, assertions, justifications, dependencies, used, variables, term_manager)

    @profile
    def standardize(self, offset):
        """
        Renumber all variables in proof to be >= offset
        """
        standardizer = {v: offset + i for (i, v) in enumerate(self.variables)}
        assertions = [mt.rename(a, standardizer) for a in self.assertions]
        variables = set(standardizer.values())
        return WorkingProof(self.claim, assertions, list(self.justifications), list(self.dependencies), list(self.used), variables, self.term_manager)

    def canonicalize(self, standardizer):
        """
        Reverts variables in self to canonical metavariable names in set.mm
        assumes proof is complete and correct
        returns substituted working proof
        standardizer: the rename map originally used to standardize self's claim apart
        """

        # revert claim metavariable names
        substitution = {u:v for (v,u) in standardizer.items()}
        claim_variables = set(standardizer.keys())

        # collect canonical metavariables
        canonical_variables = set(map(self.term_manager.encode, self.claim.variables))

        # filter those not used in claim
        available_variables = canonical_variables - claim_variables

        # rename any remaining variables in proof
        assert len(available_variables) >= len(self.variables)
        for (u,v) in zip(self.variables, available_variables):
            substitution[u] = v

        # perform renaming
        assertions = [mt.rename(a, substitution) for a in self.assertions]
        proof_variables = set(substitution.values())
        return WorkingProof(self.claim, assertions, list(self.justifications), list(self.dependencies), list(self.used), proof_variables, self.term_manager)

    def finalize(self, standardizer, rules):
        """
        Converts self to an mp.ProofStep DAG
        Assumes self is complete and correct
        Returns the root ProofStep
        standardizer: the rename map originally used to standardize claim apart
        rules: label-keyed dictionary of available entailment rules
        """
        # TODO: disjoint variable requirements

        steps = {} # avoid repeated subproofs
        p = self.canonicalize(standardizer)

        for n,(a,j,d) in enumerate(zip(p.assertions, p.justifications, p.dependencies)):

            # instantiate the consequent of the rule justifying current step
            rule = rules[j]
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

    @profile
    def substitute(self, substitution, replacement_variables):
        """
        return copy of self with substitution applied
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
        return WorkingProof(self.claim, assertions, list(self.justifications), list(self.dependencies), list(self.used), variables, self.term_manager)

    @profile
    def replace_assertion(self, step_index, new_assertion, variables):
        """
        Returns copy of self with new_assertion at step_index
        variables: must be superset of variables occurring in self and/or new_assertion
        """

        # insert assertion
        assertions = self.assertions[:step_index] + [new_assertion] + self.assertions[step_index+1:]

        # filter to variables occurring in new assertion list
        variables = {v for a in assertions for (v,_) in a if v in variables}

        return WorkingProof(self.claim, assertions, list(self.justifications), list(self.dependencies), list(self.used), variables, self.term_manager)

    @profile
    def essential_unifications(self, nested_essential_trie, step_depth, variables, sub=None, dep_idx=(), use_quota=None):
        """
        Helper to unify nested essential tries with multisubset of self's steps up to step_depth
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
        subd_proof = self.substitute(sub, variables)
        # print("post-sub:")
        # print(subd_proof)

        for i in range(step_depth):
            new_dep_idx = dep_idx + (i,)

            # count new usages
            new_usage = sum(int((not u) and (a in new_dep_idx)) for (a,u) in enumerate(subd_proof.used))

            # print(f"trying unis with step {i}: {' '.join(subd_proof.term_manager.serialize(subd_proof.assertions[i]))}")
            for (new_sub, path_term, data) in nested_essential_trie.unifications_with(subd_proof.assertions[i], variables, sub):
                # print(f"essential trie unification: sub={new_sub}")
                # print(f"path term {' '.join(subd_proof.term_manager.serialize(path_term))}")
                # print(f"with step {i}:")
                # print(' '.join(subd_proof.term_manager.serialize(subd_proof.assertions[i])))
                # print("finished labels:", [label for (label,_) in data[0]])

                complete_rules, next_trie, max_remaining_rule_terms = data

                # only yield at this point if new usage meets quota
                if new_usage >= use_quota:
                    for (label, consequent) in complete_rules:
                        # replace step_depth assertion with consequent
                        repd_proof = subd_proof.replace_assertion(step_depth, consequent, variables)
                        # apply substitution
                        repd_proof = repd_proof.substitute(new_sub, variables)
                        repd_proof.justifications[step_depth] = label
                        repd_proof.dependencies[step_depth] = new_dep_idx
                        for di in new_dep_idx: repd_proof.used[di] = True
                        yield repd_proof

                # only recurse if enough terms left to meet quota
                if new_usage + max_remaining_rule_terms < use_quota: continue

                # print("recursing on next trie:")
                # print(next_trie.tree_string(subd_proof.term_manager))
                yield from subd_proof.essential_unifications(next_trie, step_depth, variables, new_sub, new_dep_idx, use_quota)

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
        self.max_essentials = max([len(r.essentials) for r in rules])

        self.essentialless_rules = [] # list of essential-less rules
        self.essentialless_variables = set() # and their variables

        # keyed for rules with >= n essentials for each occurring n
        self.consequent_trie = {} # (min, max) essentials: trie
        self.essentials_trie = {} # (min, max) essentials: trie
        self.consequent_variables = {} # (min, max) essentials: variable set
        self.essentials_variables = {} # (min, max) essentials: variable set

        for rule in rules:
            consequent, essentials, mandatory = term_manager.termify(rule)

            # essential-less rules
            if len(essentials) == 0:
                self.essentialless_rules.append((rule.consequent.label, consequent))
                self.essentialless_variables |= mandatory

            for mxe in range(len(essentials), self.max_essentials+1):
                for mne in range(len(essentials)+1):

                    if (mne,mxe) not in self.consequent_variables: self.consequent_variables[(mne,mxe)] = set()
                    self.consequent_variables[(mne,mxe)] |= mandatory

                    # print(f"incorporating {rule}")

                    ## consequent-specific trie
                    if (mne,mxe) not in self.consequent_trie:
                        self.consequent_trie[(mne,mxe)] = TermTrieNode()

                    # incorporate consequent
                    node = self.consequent_trie[(mne,mxe)].incorporate(consequent)
                    if node.data is None:
                        node.data = [[], TermTrieNode(), 0]
                    node.data[2] = max(node.data[2], len(essentials))

                    # incorporate any essentials
                    for e, (_, essential) in enumerate(essentials):
                        node = node.data[1].incorporate(essential)
                        if node.data is None:
                            node.data = [[], TermTrieNode(), 0]
                        node.data[2] = max(node.data[2], len(essentials)-e-1)

                    # store the rule label and consequent term
                    node.data[0].append((rule.consequent.label, consequent))

                    # for essential-less rules, skip consequent-agnostic indexing
                    if len(essentials) == 0: continue

                    if (mne,mxe) not in self.essentials_variables: self.essentials_variables[(mne,mxe)] = set()
                    self.essentials_variables[(mne,mxe)] |= mandatory

                    ## essential-full consequent-agnostic trie
                    if (mne,mxe) not in self.essentials_trie:
                        self.essentials_trie[(mne,mxe)] = TermTrieNode()

                    # incorporate first essential
                    lab, essential = essentials[0]
                    node = self.essentials_trie[(mne,mxe)].incorporate(essential)
                    if node.data is None:
                        node.data = [[], TermTrieNode(), 0]
                    node.data[2] = max(node.data[2], len(essentials)-1)

                    # incorporate any remaining essentials
                    for e, (_, essential) in enumerate(essentials[1:]):
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

    def full_string(self):
        print("keys")
        print(self.consequent_trie.keys())
        print(self.essentials_trie.keys())
        s = [
            "\n **** rule consequent-specific trie ****\n",
            self.tree_string(self.consequent_trie[0,self.max_essentials]),
            "\n **** rule consequent-agnostic trie ****\n",
            self.tree_string(self.essentials_trie[0,self.max_essentials]),
            "\n **** rule essential-less list ****\n",
        ]
        for (label, consequent) in self.essentialless_rules:
            s.append(label + ' '.join(self.term_manager.serialize(consequent)))# + consequent)
        return "\n".join(s)

    @profile
    def consequent_specific_unifications(self, working_proof, step_depth, min_new_usages, min_essentials, max_essentials):
        """
        Yields substituted working proofs after unifying with rule index
        Only yields results with at least min_new_usages new usages
        Only yields results using rules with between (min,max) essentials
        Unifies rule consequents with working_proof.assertions[step_depth] and hypotheses with working_proof.assertions[:step_depth]
        """

        # you need at least min_new_usages essentials to hit usage quota
        low_essentials = max(min_essentials, min_new_usages)

        # dont yield if no rules exist in this range
        if (low_essentials, max_essentials) not in self.consequent_variables: return
        variables = self.consequent_variables[(low_essentials, max_essentials)] | working_proof.variables

        conclusion = working_proof.assertions[step_depth]
        for (sub, path_term, data) in self.consequent_trie[(low_essentials, max_essentials)].unifications_with(conclusion, variables):
            # applicable rules without essentials
            for (label, _) in data[0]:
                sub_working_proof = working_proof.substitute(sub, variables)
                sub_working_proof.justifications[step_depth] = label
                yield sub_working_proof
            # applicable rules with essentials
            # print(f"consequent-specific unified {' '.join(working_proof.term_manager.serialize(path_term))} with step {step_depth}")
            yield from working_proof.essential_unifications(data[1], step_depth, variables, sub, use_quota=min_new_usages)

    @profile
    def consequent_agnostic_unifications(self, working_proof, step_depth, min_new_usages, min_essentials, max_essentials):

        # you need at least min_new_usages essentials to hit usage quota
        low_essentials = max(min_essentials, min_new_usages)

        # essential-less rules, unless low_essentials is > 0
        if low_essentials == 0:
            variables = self.essentialless_variables | working_proof.variables
            for (label, consequent) in self.essentialless_rules:
                # replace step_depth assertion with consequent
                sub_working_proof = working_proof.replace_assertion(step_depth, consequent, variables)
                sub_working_proof.justifications[step_depth] = label
                yield sub_working_proof

        # essential-full rules
        low_essentials = max(low_essentials, 1) # don't duplicate essential-less yields from trie

        # dont yield if no rules exist in this range
        if (low_essentials, max_essentials) not in self.essentials_variables: return
        variables = self.essentials_variables[(low_essentials, max_essentials)] | working_proof.variables

        yield from working_proof.essential_unifications(self.essentials_trie[(low_essentials, max_essentials)], step_depth, variables, use_quota=min_new_usages)

    @profile
    def consequent_specific_unifications_defer(self, working_proof, step_depth, min_new_usages, min_essentials, max_essentials):
        """
        Yields substituted working proofs after unifying with rule index
        Only yields results with at least min_new_usages new usages
        Only yields results using rules with between (min,max) essentials
        Unifies rule consequents with working_proof.assertions[step_depth] and hypotheses with working_proof.assertions[:step_depth]
        """

        # you need at least min_new_usages essentials to hit usage quota
        low_essentials = max(min_essentials, min_new_usages)

        if low_essentials == 0:
            # defer to completion after top-level yield
            sub_working_proof = working_proof.copy() # necessary?
            yield sub_working_proof # leave justification as "" for completion later while step_depth increases

        low_essentials = max(low_essentials, 1) # don't duplicate essential-less yields from trie

        # dont yield if no rules exist in this range
        if (low_essentials, max_essentials) not in self.consequent_variables: return
        variables = self.consequent_variables[(low_essentials, max_essentials)] | working_proof.variables

        conclusion = working_proof.assertions[step_depth]
        for (sub, path_term, data) in self.consequent_trie[(low_essentials, max_essentials)].unifications_with(conclusion, variables):
            # applicable rules without essentials
            for (label, _) in data[0]:
                sub_working_proof = working_proof.substitute(sub, variables)
                sub_working_proof.justifications[step_depth] = label
                yield sub_working_proof
            # applicable rules with essentials
            # print(f"consequent-specific unified {' '.join(working_proof.term_manager.serialize(path_term))} with step {step_depth}")
            yield from working_proof.essential_unifications(data[1], step_depth, variables, sub, use_quota=min_new_usages)

    @profile
    def consequent_agnostic_unifications_defer(self, working_proof, step_depth, min_new_usages, min_essentials, max_essentials):

        # you need at least min_new_usages essentials to hit usage quota
        low_essentials = max(min_essentials, min_new_usages)

        # essential-less rules, unless low_essentials is > 0
        if low_essentials == 0:
            # defer to completion after top-level yield
            sub_working_proof = working_proof.copy() # necessary?
            yield sub_working_proof # leave justification as "" for completion later while step_depth increases

        # essential-full rules
        low_essentials = max(low_essentials, 1) # don't duplicate essential-less yields from trie

        # dont yield if no rules exist in this range
        if (low_essentials, max_essentials) not in self.essentials_variables: return
        variables = self.essentials_variables[(low_essentials, max_essentials)] | working_proof.variables

        yield from working_proof.essential_unifications(self.essentials_trie[(low_essentials, max_essentials)], step_depth, variables, use_quota=min_new_usages)

if __name__ == "__main__":

    import src.metamathpy.setmm as ms
    db = ms.load_pl()
    exclude_list = ms.new_usage_discouraged()

    goal_label = "mp2"
    claim = db.rules[goal_label]
    rules = db.rules_up_to(goal_label, exclude_list)
    term_manager = mt.TermManager(rules["wff"])

    consequent, essentials, mandatory = term_manager.termify(claim)
    offset = 1000
    proof_size = 5
    wp = WorkingProof.initialize(claim, consequent, essentials, offset, proof_size, term_manager)
    print(wp)
    print(wp.standardize(100))
    input('.')

    rule_index = RuleIndex(rules["|-"], term_manager)

    print("\n **** rule consequent-specific trie ****\n")
    print(rule_index.tree_string(rule_index.consequent_trie[0]))
    print("\n **** rule consequent-agnostic trie ****\n")
    print(rule_index.tree_string(rule_index.essentials_trie[0]))
    print("\n **** rule essential-less list ****\n")
    for (label, consequent) in rule_index.essentialless_rules:
        print(label, ' '.join(term_manager.serialize(consequent)), consequent)
