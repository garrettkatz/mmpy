import metamathpy.proof as mp
from metamathpy.substitution import substitute

def backsearch(rules, variables, tokens, max_depth=-1, verbose=False):
    """
    parameters:
      rules: list of rule objects to use as justifications
      variables: list of tokens that are metavariables
      tokens: token sequence to prove
      max_depth: if >= 0, dont search past this depth
      verbose: if True, print debug messages
    returns (success, rootstep)
      success: true or false
      rootstep: root of partial proof step tree (wraps tokens, rule, dependencies, substitution), or None if not successful
    TODO: disjoint variable requirements
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
    
                # and-loop: all dependencies must be proved (base case: all([]) is True)
                dependencies = {}
                for hyp in rule.hypotheses:
    
                    # try satisfying
                    success, step = backsearch(rules, variables, substitute(hyp.tokens, substitution), max_depth-1)
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
                return True, mp.ProofStep(tokens, rule, dependencies, substitution) # todo: disjoint

    # no rules worked
    return False, None

if __name__ == "__main__":

    import numpy as np
    import metamathpy.setmm as ms
    import metamathpy.database as md

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
