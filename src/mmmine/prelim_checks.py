from time import perf_counter
import mmmine.bidao as bd

if __name__ == "__main__":

    import metamathpy.setmm as ms

    # individual targets

    # # target = "bijust" # justification theorems
    # target = "meredith" # axiom equivalence
    # num_sweeps = 2

    # db = ms.load_to(target)

    # goal_tokens = tuple(db.rules[target].consequent.tokens)

    # # just keep metavariables in floating hypotheses for now
    # metavars = tuple(hyp.tokens[1] for hyp in db.rules[target].floatings)

    # # filter rules
    # rules = bd.filter_rules(db, metavars, ax_only=False, dependent_floor=2, exclude_labels=(target,))
    # # for rule in rules[:20]: print(rule)
    # print(f"{len(db.rules)} to {len(rules)} filtered rules")

    # # run sweeps
    # root_step = bd.run_sweeps(num_sweeps, rules, goal_tokens, dbg=True)

    # lots of targets
    num_sweeps = 3
    max_time = 5

    db = ms.load_pl()

    prop_labels = []
    for rule in db.rules.values():
        if rule.consequent.tag == "$p" and len(rule.essentials)==0: prop_labels.append(rule.consequent.label)

    num_success = 0
    for t, target in enumerate(prop_labels):

        goal_tokens = tuple(db.rules[target].consequent.tokens)
        print(f"Target {t} of {len(prop_labels)}, {num_success} success so far: {' '.join(goal_tokens)}")

        # just keep metavariables in floating hypotheses for now
        metavars = tuple(hyp.tokens[1] for hyp in db.rules[target].floatings)
    
        # filter rules
        rules = bd.filter_rules(db, metavars, ax_only=False, dependent_floor=1, exclude_labels=prop_labels[t:])
        # for rule in rules[:20]: print(rule)
        print(f"{len(db.rules)} to {len(rules)} filtered rules")
    
        # run sweeps
        timeout = perf_counter() + max_time
        root_step = bd.run_sweeps(num_sweeps, rules, goal_tokens, timeout, dbg=False)
        if root_step is not None: num_success += 1
    
