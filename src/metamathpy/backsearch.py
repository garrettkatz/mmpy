import metamathpy.proof as mp
from metamathpy.substitution import substitute, Scheme

class AndNode:
    """
    Represents one viable proof strategy for a parent OrNodes's goal
    Parameters as in ProofStep, except dependencies are OrNodes instead of ProofSteps
    Proof requires all dependencies to be proved (hence "and" node)
    """
    def __init__(self, rule, substitution=None, dependencies=None):
        self.rule = rule
        self.substitution = substitution
        self.dependencies = dependencies

class OrNode:
    """
    Represents a goal claim and all its viable proof strategies (list of AndNodes)
    Proof requires one strategy to succeed (hence "or" node)
    """
    def __init__(self, tokens, variables, disjoint=None):
        """
        tokens: token sequence (tuple) of goal claim
        variables: list of tokens that are metavariables in claim
        disjoint: disjoint variable requirements of claim, if any
        """
        self.tokens = tokens
        self.variables = variables
        self.disjoint = disjoint
        self.and_nodes = []
        self.node_count = 1

    def expand(self, rules, max_depth):
        """
        recursively expands and-or tree for self
        inputs:
            rules: list of rule objects to use as justifications
            max_depth: recursively expand at most this many or-levels            
        """

        # base case
        if max_depth == 0: return

        # or-loop (only one rule needs to justify)
        for rule in rules:
    
            # a hypothesis-less "rule" (ie, hypothesis of whats being currently proved) has to match without substitutions
            if len(rule.hypotheses) == 0:
                if tuple(rule.consequent.tokens) == self.tokens: # todo: in finalize, change token list to tuple?
                    self.and_nodes.append(AndNode(rule))
                    self.node_count += 1
    
            # else try all possible substitutions
            else:
    
                for substitution in rule.scheme.matches(self.tokens):
        
                    # skip if disjoint requirements not satisfied or too many inherited
                    inherited, message = mp.disjoint_variable_check(rule, substitution)
                    if inherited is None: continue
                    if self.disjoint is not None and inherited > self.disjoint: continue
    
                    # and-loop: all dependencies must be proved (base case: all([]) is True)
                    dependencies = {}
                    for hyp in rule.hypotheses:
        
                        # recursively expand or-node dependency
                        or_node = OrNode(substitute(hyp.tokens, substitution), self.variables, self.disjoint)
                        or_node.expand(rules, max_depth-1)
                        if max_depth-1 > 0 and len(or_node.and_nodes) == 0: break # no way to prove this dependency
                        
                        # proof of this dependency not yet ruled out
                        dependencies[hyp.label] = or_node
        
                    # if some hypotheses have no viable proof strategies, this substitution and rule does not work
                    if len(dependencies) < len(rule.hypotheses): continue

                    # otherwise, construct and append and-node
                    and_node = AndNode(rule, substitution, dependencies)
                    self.and_nodes.append(and_node)
                    self.node_count += 1 + sum(or_node.node_count for or_node in dependencies.values())

    def tree_string(self, prefix=""):
        s = f"{prefix}{' '.join(self.tokens)}"
        if len(self.and_nodes) > 0:
            s += f" -| or<{self.node_count}>["
            for and_node in self.and_nodes:
                psub = {}
                if and_node.substitution is not None:
                    psub = {k: ' '.join(v) for k,v in and_node.substitution.items()}
                s += f"\n{prefix+' '}{and_node.rule.consequent.label}/{psub}"
                if and_node.dependencies is not None:
                    s += " -| and["
                    for or_node in and_node.dependencies.values():
                        s += "\n" + or_node.tree_string(prefix+'  ')
        return s

    def first_viable_proof(self):
        # recursively find first viable proof, if any, in self's current expansion
        for and_node in self.and_nodes:
            if and_node.dependencies is None:
                return True, mp.ProofStep(self.tokens, and_node.rule)
            else:
                dependencies = {}
                for label, or_node in and_node.dependencies.items():
                    success, step = or_node.first_viable_proof()
                    if not success: break
                    dependencies[label] = step
                if len(dependencies) < len(and_node.dependencies): continue
                return True, mp.ProofStep(self.tokens, and_node.rule, dependencies, and_node.substitution, self.disjoint)

        return False, None

def work_variable_bindings(schemes, pile):
    # helper generator for backsearch with work variables
    # yield every substitution s such that all(scheme.sub(s) in pile.keys for scheme in schemes)
    # also yields the corresponding steps in the pile

    # try matching first scheme against each token sequence in the pile
    for tokens, step in pile.items():
        for bindings in schemes[0].matches(tokens):

            # base case: this is the last scheme, so done
            if len(schemes) == 1:
                yield bindings, (step,)
                continue

            # recursive case: check if these bindings also work for remaining schemes
            sub_schemes = []
            for scheme in schemes[1:]:
                sub_schemes.append(Scheme(
                    scheme.substitute(bindings),
                    set(scheme.variables) - set(bindings.keys())
                ))

            for sub_bindings, steps in work_variable_bindings(sub_schemes, pile):
                yield (bindings | sub_bindings), ((step,) + steps)


def backsearch(goal, rules, disjoint=None, pile=None, max_depth=-1, verbose=False):
    """
    parameters:
      goal: token sequence for claim to prove
      rules: list of rule objects to use as justifications
      disjoint: disjoint variable requirements of claim, if any
      pile: dictionary of proof steps available for satisfying leaves, if any (pile[step.conclusion] = step)
      max_depth: if >= 0, dont search past this depth
      verbose: if True, print debug messages
    returns (success, rootstep)
      success: true or false
      rootstep: root of partial proof step tree (wraps goal, rule, dependencies, substitution), or None if not successful
    todo: test disjoint variable code branches
    """

    # initialize arguments if not provided
    if pile is None: pile = {}

    # check if current goal already proved in pile
    if goal in pile: return True, pile[goal]

    # depth limit reached
    if verbose: print(" "*max_depth + f">>> {' '.join(goal)}")
    if max_depth == 0: return False, None

    # or-loop (only one rule needs to justify)
    for rule in rules:

        # a hypothesis-less "rule" (ie, hypothesis of whats being currently proved) has to match without substitutions
        if len(rule.hypotheses) == 0:
            if tuple(rule.consequent.tokens) == goal: # todo: in finalize, change token list to tuple?
                if verbose: print(" "*max_depth + f">>> {' '.join(goal)} <={rule.consequent.label}_/(0)")
                return True, mp.ProofStep(goal, rule)

        # else try all possible substitutions
        else:

            # determine whether this rule introduces work variables
            mandatory = set([f.tokens[1] for f in rule.floatings])
            work_variables = tuple(mandatory - set(rule.consequent.tokens))
            needs_work = (len(work_variables) > 0)

            # if so, standardize apart
            if needs_work:
                standardizer = {wv: (f"wv{d}",) for (d, wv) in enumerate(work_variables)}
                work_variables = tuple(f"wv{d}" for (d, wv) in enumerate(work_variables))

            for substitution in rule.scheme.matches(goal):

                psub = {k:' '.join(v) for k,v in substitution.items()}
                if verbose: print(" "*max_depth + f">>> {' '.join(goal)} <={rule.consequent.label}{psub}")

                # skip if disjoint requirements not satisfied or too many inherited
                inherited, message = mp.disjoint_variable_check(rule, substitution)
                if inherited is None: continue
                if disjoint is not None and inherited > disjoint: continue

                # and-loop: all dependencies must be proved (base case: all([]) is True)
                if needs_work:

                    # set up work variable schemes for each hypothesis
                    schemes = []
                    for hyp in rule.hypotheses:
                        hyp_tokens = substitute(hyp.tokens, standardizer)
                        hyp_tokens = substitute(hyp_tokens, substitution)
                        scheme = Scheme(hyp_tokens, work_variables)
                        schemes.append(scheme)

                    if verbose:
                        print(" "*max_depth + "work vars needed, schemes:")
                        for scheme in schemes: print(" "*max_depth + str(scheme))

                    # use first (if any) work variable binding satisfied by pile
                    for bindings, steps in work_variable_bindings(schemes, pile):
                        dependencies = {hyp.label: step for hyp, step in zip(rule.hypotheses, steps)}

                        if verbose: print(" "*max_depth + f">>> {' '.join(goal)} <={rule.consequent.label}{psub}_/({len(dependencies)})[wv:{bindings}]")

                        return True, mp.ProofStep(goal, rule, dependencies, substitution | bindings, inherited)

                else:
                    # no work variables, try backsearching each hypothesis
                    dependencies = {}
                    for hyp in rule.hypotheses:

                        # try satisfying
                        subgoal = substitute(hyp.tokens, substitution)
                        success, step = backsearch(subgoal, rules, disjoint, pile, max_depth-1, verbose)
                        if not success: break
                        if verbose: print(" "*max_depth + f">>> {' '.join(goal)} <={rule.consequent.label}{psub}_/{hyp.label}")

                        # satisfied, can use step as dependency
                        dependencies[hyp.label] = step

                    # if some hypotheses not satisfied, this substitution and rule does not work
                    if len(dependencies) < len(rule.hypotheses):
                        if verbose: print(" "*max_depth + f">>> {' '.join(goal)} <={rule.consequent.label}{psub}X({len(dependencies)}|{len(rule.hypotheses)})")
                        continue
    
                    if verbose: print(" "*max_depth + f">>> {' '.join(goal)} <={rule.consequent.label}{psub}_/({len(dependencies)})")

                    # otherwise, it worked, construct and return root step
                    return True, mp.ProofStep(goal, rule, dependencies, substitution, inherited)

    # no rules worked
    return False, None

if __name__ == "__main__":

    import numpy as np
    import metamathpy.setmm as ms
    import metamathpy.database as md

    # # test disjoint variable code branches
    # rules = [md.Rule(
    #     Statement('test', '$p', "|- ( ph -> ps )".split(), ()),
    #     essentials=[],
    #     floatings=[
    #         Statement('wph', '$a', "wff ph".split(), ()),
    #         Statement('wps', '$a', "wff ps".split(), ())
    #     ],
    #     disjoint = {("ph", "ps")},
    #     variables = {"ph", "ps"})
    # )]
    # backsearch(tokens, rules, disjoint=None, max_depth=-1, verbose=False)
    

    db = ms.load_pl()
    # db = ms.load_all()

    # try parsing a wff with schemes for each rule
    # wff_rules = [db.rules[k] for k in ("wph", "wps", "wch", "wi", "wn")]
    # wff_rules = [db.rules[k] for k in db.rules if k[0] == "w"]
    wff_rules = list(db.rules.values())

    # filter out rules with essentials and hypothesis "rules"
    wff_rules = [rule for rule in wff_rules if len(rule.essentials)==0 and rule.consequent.tag != "$e"]

    tests = [
        ("wff ph", True),
        ("wff ps", True),
        ("wff ch", True),
        ("wff ( ph -> ph )", True),
        ("wff ( ph -> ps )", True),
        ("wff ( ps -> ch )", True),
        ("wff ps -> ch", False),
        ("wff ( ps ->", False),
        ("wff ps ch", False),
        ("wff -. ps", True),
        ("wff -.", False),
        ("|- ( ph -> ph )", True),
        ("|- ( ( ph -> ph ) -> ( ph -> ph ) )", True),
    ]
    for s, r in tests:
        goal = tuple(s.split())
        success, rootstep = backsearch(goal, wff_rules)#, max_depth=3) # may need max depth if rules with essentials included
        assert success == r, s
        if success:
            print(f"^^ token string: {s}")
            print("Final proof:")
            print(rootstep.tree_string())
        else:
            print(f"-- false token string {s}")
    input('no assertions failed...')

    ## test proof pile on last step of a1i proof
    a1i_rules = wff_rules + [db.rules[lab] for lab in ("ax-mp","a1i.1")]
    steps = [
        # # goal already in the pile
        # mp.ProofStep(tuple("|- ( ps -> ph )".split()), db.rules["ax-mp"], {}, {}),
        # dependencies in the pile
        mp.ProofStep(tuple("wff ph".split()), db.rules["wph"], {}, {}),
        mp.ProofStep(tuple("wff ( ps -> ph )".split()), db.rules["wi"], {}, {}),
        mp.ProofStep(tuple("|- ph".split()), db.rules["a1i.1"], {}, {}),
        mp.ProofStep(tuple("|- ( ph -> ( ps -> ph ) )".split()), db.rules["ax-1"], {}, {}),
    ]
    pile = {step.conclusion: step for step in steps}
    goal = tuple("|- ( ps -> ph )".split())
    success, rootstep = backsearch(goal, a1i_rules, pile=pile, max_depth=2, verbose=True)
    assert success
    print("a1i proof:")
    print(rootstep.tree_string())
    input("..")

    ## similar test again, but requiring work variable substitution
    # instance of a1i with compound expression ( ch -> ph ) for ph
    a1i_rules = wff_rules + [db.rules[lab] for lab in ("ax-mp","a1i.1")]
    steps = [
        # dependencies in the pile
        mp.ProofStep(tuple("wff ( ch -> ph )".split()), db.rules["wi"], {}, {}),
        mp.ProofStep(tuple("wff ( ps -> ( ch -> ph ) )".split()), db.rules["wi"], {}, {}),
        mp.ProofStep(tuple("|- ( ch -> ph )".split()), db.rules["a1i.1"], {}, {}),
        mp.ProofStep(tuple("|- ( ( ch -> ph ) -> ( ps -> ( ch -> ph ) ) )".split()), db.rules["ax-1"], {}, {}),
    ]
    pile = {step.conclusion: step for step in steps}

    # check work_variable_bindings
    schemes = [
        Scheme("wff wv".split(), ("wv",)),
        Scheme("wff ( ps -> ( ch -> ph ) )".split(), ("wv",)),
        Scheme("|- wv".split(), ("wv",)),
        Scheme("|- ( wv -> ( ps -> ( ch -> ph ) ) )".split(), ("wv",)),
    ]
    for b, (bindings, steps) in enumerate(work_variable_bindings(schemes, pile)):
        print(b, bindings, steps)
    input("all wv bindings^^")

    goal = tuple("|- ( ps -> ( ch -> ph ) )".split())
    success, rootstep = backsearch(goal, a1i_rules, pile=pile, max_depth=2, verbose=True)
    assert success
    print("a1i[ch -> ph] proof:")
    print(rootstep.tree_string())
    input("..")


    # ## and-or tree tests
    # for s, _ in tests:
    #     tokens = tuple(s.split())
    #     print(f"token string: {s}")
    #     or_node = OrNode(tokens, wff_vars)
    #     or_node.expand(wff_rules, max_depth=4)
    #     print(or_node.tree_string())
    #     success, rootstep = or_node.first_viable_proof()
    #     print('or-and tree^^')
    #     if success:
    #         print("Final proof:")
    #         print(rootstep.tree_string())
    #     else:
    #         print("Failure...")
    #     input('..')

    # ## checking how far you can get without work variables (not very):
    # # get rules that do not introduce work variables
    # workless_rules = []
    # for rule in db.rules.values():
    #     # extract mandatory variables in essential hypotheses and consequent
    #     con_vars = rule.variables & set(rule.consequent.tokens)
    #     ess_vars = rule.variables & set(sum((h.tokens for h in rule.essentials), []))
    #     # no work variables if all mandatory variables are in the consequent
    #     if ess_vars <= con_vars: workless_rules.append(rule)
    # # for rule in [r for r in workless_rules if r.consequent.tag in ("$a","$p")][:20]:
    # #     print(rule)
    # # input("first workless rules ^^...")

    # # get rules whose proofs only rely on workless rules
    # workless_provable = []
    # for rule in db.rules.values():
    #     if rule.consequent.tag != "$p": continue
    #     split = rule.consequent.proof.index(")")
    #     step_labels = rule.consequent.proof[1:split]
    #     if set(step_labels) <= set(workless_rules): workless_provable.append(rule)

    # for rule in workless_provable[:5]:
    #     print(rule)
    #     rootstep, _ = mp.verify_compressed_proof(db, rule)
    #     print(rootstep.tree_string())
    # input(f"first workless provables ({len(workless_provable)} total, {len(workless_rules)} workless rules) ^^...")
