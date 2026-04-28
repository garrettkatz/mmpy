
if __name__ == "__main__":

    import metamathpy.setmm as ms

    db = ms.load_pl()

    essentialess_rules = []
    for rule in db.rules.values():
        if rule.consequent.tag != "$p": continue
        if len(rule.essentials) == 0: essentialess_rules.append(rule)
    print(f"{len(essentialess_rules)} propositions without essentials")
    print(essentialess_rules[0])

    concwork_rules = []
    for rule in db.rules.values():
        if rule.consequent.tag != "$p": continue
        if len(rule.essentials) > 0:
            # see if there are any mandatory variables not in essentials
            if len(rule.mandatory - set(sum([e.tokens for e in rule.essentials],[]))) > 0:
                concwork_rules.append(rule)
    print(f"{len(concwork_rules)} propositions with mandatories not contained in >0 essentials")
    for rule in concwork_rules[:3]:
        print(rule)

    ## checking how far you can get without work variables (not very):
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
    print(f"{len(workless_rules)} rules that do not introduce work variables")

    # get rules whose proofs only rely on workless rules
    workless_provable = []
    for rule in db.rules.values():
        if rule.consequent.tag != "$p": continue
        split = rule.consequent.proof.index(")")
        step_labels = rule.consequent.proof[1:split]
        if set(step_labels) <= set(workless_rules): workless_provable.append(rule)

    # for rule in workless_provable[:5]:
    #     print(rule)
    #     rootstep, _ = mp.verify_compressed_proof(db, rule)
    #     print(rootstep.tree_string())
    # input(f"first workless provables ({len(workless_provable)} total, {len(workless_rules)} workless rules) ^^...")
    print(f"{len(workless_provable)} rules whose proofs only rely on workless rules")



    # are all rules about typecodes are essential-less or at least work-less?
    # check if all floating typecodes (all except |-) have only essentialess or work-less inference rules
    # the answer is YES. only other typecodes are wff and class.  In both cases, all of their grammar rules are essentialless and workless.

    print("loading all...")
    db = ms.load_all()
    print("counting...")
    num_rules = {}
    num_essless = {}
    num_workless = {}
    for rule in db.rules.values():
        if rule.consequent.tag in ("$a", "$p"):
            typecode = rule.consequent.tokens[0]
            essentialless = (len(rule.essentials) == 0)
            workless = (rule.mandatory <= set(rule.consequent.tokens))
            num_rules[typecode] = num_rules.get(typecode, 0) + 1
            num_essless[typecode] = num_essless.get(typecode, 0) + int(essentialless)
            num_workless[typecode] = num_workless.get(typecode, 0) + int(workless)

    for typecode in num_rules:
        print(f"typecode {typecode}: {num_rules[typecode]} total, {num_essless[typecode]} essential-less, {num_workless[typecode]} workless")

