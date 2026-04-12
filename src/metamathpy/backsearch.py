import metamathpy.proof as mp
from metamathpy.substitution import substitute

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


def backsearch(rules, variables, tokens, disjoint=None, max_depth=-1, verbose=False):
    """
    parameters:
      rules: list of rule objects to use as justifications
      variables: list of tokens that are metavariables
      tokens: token sequence claim to prove
      disjoint: disjoint variable requirements of claim, if any
      max_depth: if >= 0, dont search past this depth
      verbose: if True, print debug messages
    returns (success, rootstep)
      success: true or false
      rootstep: root of partial proof step tree (wraps tokens, rule, dependencies, substitution), or None if not successful
    todo: test disjoint variable code branches
    """

    # depth limit reached
    if verbose: print(" "*max_depth + f">>> {' '.join(tokens)}")
    if max_depth == 0: return False, None

    # or-loop (only one rule needs to justify)
    for rule in rules:

        # a hypothesis-less "rule" (ie, hypothesis of whats being currently proved) has to match without substitutions
        if len(rule.hypotheses) == 0:
            if tuple(rule.consequent.tokens) == tokens: # todo: in finalize, change token list to tuple?
                if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}_/(0)")
                return True, mp.ProofStep(tokens, rule)

        # else try all possible substitutions
        else:

            for substitution in rule.scheme.matches(tokens):

                psub = {k:' '.join(v) for k,v in substitution.items()}
                if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}")

                # skip if disjoint requirements not satisfied or too many inherited
                inherited, message = mp.disjoint_variable_check(rule, substitution)
                if inherited is None: continue
                if disjoint is not None and inherited > disjoint: continue

                # and-loop: all dependencies must be proved (base case: all([]) is True)
                dependencies = {}
                for hyp in rule.hypotheses:
    
                    # try satisfying
                    success, step = backsearch(rules, variables, substitute(hyp.tokens, substitution), disjoint, max_depth-1, verbose)
                    if not success: break
                    if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}_/{hyp.label}")
                    
                    # satisfied, can use step as dependency 
                    dependencies[hyp.label] = step
    
                # if some hypotheses not satisfied, this substitution and rule does not work
                if len(dependencies) < len(rule.hypotheses):
                    if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}X({len(dependencies)}|{len(rule.hypotheses)})")
                    continue
    
                if verbose: print(" "*max_depth + f">>> {' '.join(tokens)} <={rule.consequent.label}{psub}_/({len(dependencies)})")
    
                # otherwise, it worked, construct and return root step
                return True, mp.ProofStep(tokens, rule, dependencies, substitution, inherited)

    # no rules worked
    return False, None

if __name__ == "__main__":

    import numpy as np
    import metamathpy.setmm as ms
    import metamathpy.database as md

    # # test disjoint variable code branches
    # rules = [md.Rule(
    #     Statement('test', '$p', "|- ( ph -> ps )".split(" "), ()),
    #     essentials=[],
    #     floatings=[
    #         Statement('wph', '$a', "wff ph".split(" "), ()),
    #         Statement('wps', '$a', "wff ps".split(" "), ())
    #     ],
    #     disjoint = {("ph", "ps")},
    #     variables = {"ph", "ps"})
    # )]
    # backsearch(rules, variables, tokens, disjoint=None, max_depth=-1, verbose=False)
    

    db = ms.load_pl()
    # db = ms.load_all()

    # try parsing a wff with schemes for each rule
    wff_vars = {"ph", "ps", "ch"}
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
        tokens = tuple(s.split(" "))
        success, rootstep = backsearch(wff_rules, wff_vars, tokens)#, max_depth=3) # may need max depth if rules with essentials included
        assert success == r, tokens
        if success:
            print(f"^^ token string: {s}")
            print("Final proof:")
            print(rootstep.tree_string())
        else:
            print(f"-- false token string {s}")
    input('no assertions failed...')

    for s, _ in tests:
        tokens = tuple(s.split(" "))
        print(f"token string: {s}")
        or_node = OrNode(tokens, wff_vars)
        or_node.expand(wff_rules, max_depth=4)
        print(or_node.tree_string())
        success, rootstep = or_node.first_viable_proof()
        print('or-and tree^^')
        if success:
            print("Final proof:")
            print(rootstep.tree_string())
        else:
            print("Failure...")
        input('..')

    # get rules that do not introduce work variables
    workless_rules = []
    for rule in db.rules.values():
        # extract mandatory variables in essential hypotheses and consequent
        con_vars = rule.variables & set(rule.consequent.tokens)
        ess_vars = rule.variables & set(sum((h.tokens for h in rule.essentials), []))
        # no work variables if all mandatory variables are in the consequent
        if ess_vars <= con_vars: workless_rules.append(rule)
    # for rule in [r for r in workless_rules if r.consequent.tag in ("$a","$p")][:20]:
    #     print(rule)
    # input("first workless rules ^^...")

    # get rules whose proofs only rely on workless rules
    workless_provable = []
    for rule in db.rules.values():
        if rule.consequent.tag != "$p": continue
        split = rule.consequent.proof.index(")")
        step_labels = rule.consequent.proof[1:split]
        if set(step_labels) <= set(workless_rules): workless_provable.append(rule)

    for rule in workless_provable[:5]:
        print(rule)
        rootstep, _ = mp.verify_compressed_proof(db, rule)
        print(rootstep.tree_string())
    input(f"first workless provables ({len(workless_provable)} total, {len(workless_rules)} workless rules) ^^...")
