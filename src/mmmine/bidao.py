from time import perf_counter
import itertools as it
import numpy as np
import metamathpy.proof as mp
import metamathpy.database as md
from metamathpy.unification import substitute

# place-holder rule for wff parses
WFF_RULE = md.Rule(md.Statement("WFF", None, None, None), [], [], set(), set())

class GoalNode:
    def __init__(self, conclusion):
        # conclusion: token string to be proved
        self.conclusion = conclusion

        # each child represents an inference that would prove this goal if essential dependencies are satisfied
        # each essential dependency of a child has a respective sub-goal node
        # assumes floating dependencies already proven
        # successful proof requires logical-or over the children, logical-and of their essential depency token strings
        self.children = {} # tuple of essential dependency token strings -> rule, substitution, floating dependencies, sub-goals

    def update(self, rule, substitution, floating_steps, essential_tokens):
        # save a new route to prove self (no-op if route already included in children)
        # floating_steps[n] is proof step satisfying nth floating dependency
        # essential_tokens[n] are tokens for the nth essential dependency sub-goal
        # each essential dependency gets a sub-goal node
        # returns sub-goals for this update (does not check for duplicates or cycles in the DAG)

        # don't update a node with an existing route
        if essential_tokens in self.children: return ()

        # otherwise construct requisite sub-goals
        sub_goals = tuple(map(GoalNode, essential_tokens))

        # update with new route and return
        self.children[essential_tokens] = (rule, substitution, floating_steps, sub_goals)
        return sub_goals

    def satisfy_from(self, proof_steps):
        # proof_steps[conclusion tokens] = first proof step encountered with that conclusion (type |- only), as in rule sweep
        # try to satisfy goal from proof steps, returning None if failed or the final proof step if successful

        # base case
        if self.conclusion in proof_steps:
            return proof_steps[self.conclusion]

        # recursive case: logical-or over children
        for essential_tokens in self.children:

            (rule, substitution, floating_steps, sub_goals) = self.children[essential_tokens]

            # logical-and over child sub-goals: any None sub_proofs indicate not satisfied
            sub_proofs = tuple(sub_goal.satisfy_from(proof_steps) for sub_goal in sub_goals)
            if None in sub_proofs: continue

            # if this line is reached, all sub-goals were proved
            proof_step, status = mp.perform(rule, floating_steps + sub_proofs)
            assert status == "" # make sure inference is valid
            return proof_step

        # if this line reached, logical-or failed
        return None

    def deficit(self, proof_steps):
        # proof_steps[conclusion tokens] = first proof step encountered with that conclusion (type |- only), as in rule sweep
        # count the minimal number of open descendent goals needed to satisfy self
        # (todo: avoid double-counting duplicates)
        
        # base case: self already satisfied directly
        if self.conclusion in proof_steps: return 0

        # base case: no children, so self must be satisfied directly
        if len(self.children) == 0: return 1

        # recursive case: logical-or (minimum) over children
        child_min = np.inf
        for essential_tokens in self.children:
        
            # logical-and (sum) over current child's sub-goals
            (rule, substitution, floating_steps, sub_goals) = self.children[essential_tokens]
            child_sum = sum(sub_goal.deficit(proof_steps) for sub_goal in sub_goals)
            child_min = min(child_min, child_sum)

        return child_min

    def tree_string(self, prefix=""):
        s = prefix + " ".join(self.conclusion) + " [OR:\n"
        for essential_tokens in self.children:
            (rule, substitution, floating_steps, sub_goals) = self.children[essential_tokens]
            s += prefix + f" {rule.consequent.label}[AND:\n"
            for sub_goal in sub_goals:
                s += sub_goal.tree_string(prefix + "  ")
            s += prefix + " :DNA]\n"
        s += prefix + ":RO]\n"
        return s


def rule_sweep(rules, proof_steps, goals, timeout):
    # rules[n] = nth inference rule to try
    # proof_steps[typecode][conclusion tokens] = first proof step encountered with that type code and conclusion
    # goals[conclusion tokens][k] = kth encountered goal node for that conclusion (todo: dag but with cycle-checks)
    # timeout: once perf_counter exceeds this, ends early
    new_steps = {"wff": {}, "|-": {}} # other typecodes needed beyond PL
    new_goals = {}
    for rule in rules:

        # early termination
        if perf_counter() > timeout: break

        # apply rule to all wff combinations for metavariables
        for wffs in it.product(proof_steps["wff"].values(), repeat=len(rule.floatings)):

            # early termination
            if perf_counter() > timeout: break

            # setup substitution from floating hypotheses
            substitution = {hyp.tokens[1]: dep.conclusion[1:] for (hyp, dep) in zip(rule.floatings, wffs)}

            # apply substitution to essential hypotheses and consequent
            essential_tokens = tuple(substitute(hyp.tokens, substitution) for hyp in rule.essentials)
            conclusion_tokens = substitute(rule.consequent.tokens, substitution)

            # forward chaining: only apply rule if hypotheses are satisfied
            if all(tokens in proof_steps["|-"] for tokens in essential_tokens):

                # set up all dependencies
                deps = wffs + tuple(proof_steps["|-"][tokens] for tokens in essential_tokens)
    
                # perform the rule
                step, status = mp.perform(rule, deps)
    
                # should be sound for PL (no distinct variable requirements)
                assert status == ""
    
                # save new results
                tokens = step.conclusion
                typecode = tokens[0]
                if tokens not in proof_steps[typecode] and tokens not in new_steps[typecode]:
                    new_steps[typecode][tokens] = step
    
                # also assume any conclusion is well-formed
                if typecode == "|-":
                    tokens = ("wff",) + tokens[1:] 
                    if tokens not in proof_steps["wff"] and tokens not in new_steps["wff"]:
                        new_steps["wff"][tokens] = mp.ProofStep(tokens, rule=WFF_RULE) # skip the actual parse

            # backward chaining: update and-or tree if goal is matched
            if conclusion_tokens in goals:
                for goal in goals[conclusion_tokens]:
                    sub_goals = goal.update(rule, substitution, wffs, essential_tokens)
                    for sub_goal in sub_goals:
                        if sub_goal.conclusion not in new_goals:
                            new_goals[sub_goal.conclusion] = []
                        new_goals[sub_goal.conclusion].append(sub_goal)

            # print(substitution)
            # input('.')

    return new_steps, new_goals

def run_sweeps(num_sweeps, rules, goal_tokens, timeout, dbg=False):
    # todo: multiple top-level goals
    # returns root proof step if successful else None

    # set up goals
    root_goal = GoalNode(goal_tokens)
    goals = {goal_tokens: [root_goal]}

    proof_steps = {"wff": {}, "|-": {}}
    for sweep in range(num_sweeps):

        # do the next sweep
        start = perf_counter()
        new_steps, new_goals = rule_sweep(rules, proof_steps, goals, timeout)
        duration = perf_counter() - start
    
        if dbg:
            print(f"sweep {sweep}:")
            for typecode in ("wff", "|-"):
                print(f"new {typecode}s ({len(new_steps[typecode])} total):")
                for t, tokens in enumerate(new_steps[typecode]):
                    print(f" {' '.join(tokens)}")
                    if t == 10:
                        print(" ...")
                        break

            print(f"new goals ({len(new_goals)} total):")
            for t, tokens in enumerate(new_goals):
                print(f" {' '.join(tokens)}")
                if t == 10:
                    print(" ...")
                    break

        # integrate new proof steps, without replacing earliest encounters
        for typecode in ("wff", "|-"):
            proof_steps[typecode] = new_steps[typecode] | proof_steps[typecode]

        # integrate new goals (todo: deduplicate)
        for conclusion in new_goals:
            if conclusion not in goals: goals[conclusion] = []
            goals[conclusion].extend(new_goals[conclusion])                

        if dbg:
            print("goal tree:")
            print(root_goal.tree_string())
            print(f"deficit = {root_goal.deficit(proof_steps['|-'])}")
    
            print(f"Took {duration:.3f}s ({duration/60:.3f}m)")

        # check satisfaction
        root_step = root_goal.satisfy_from(proof_steps["|-"])
        if root_step is not None:
            print("Root is satisfied!")
            print(root_step.tree_string())
            return root_step

        if dbg: input("..")

def filter_rules(db, metavars, ax_only, dependent_floor, exclude_labels):
    # filter db rules by given criteria
    # only include given metavars
    # omit essential hypotheses
    # omit $p rules if ax_only = True
    # omit rules with less than dependent_floor direct dependents
    # omit excluded labels

    # calculate num direct dependents of each rule, assuming compressed proofs
    num_dependents = {label: 0 for label in db.rules}

    for rule in db.rules.values():
        # only propositions have proofs
        if rule.consequent.tag != "$p": continue

        # get proof labels (assumes proof in compressed format)
        split = rule.consequent.proof.index(")")
        step_labels = rule.consequent.proof[1:split]

        for label in step_labels:
            num_dependents[label] += 1

    rules = []
    for (label, rule) in db.rules.items():

        # for now, omit "rules" for essential hypotheses
        if rule.consequent.tag == "$e": continue

        # if requested, omit any non-axiom propositions
        if ax_only and rule.consequent.tag == "$p": continue

        # limit metavariables
        if rule.consequent.tag == "$f" and rule.consequent.tokens[1] not in metavars: continue

        # omit propositions with few direct dependents
        if rule.consequent.tag == "$p" and num_dependents[label] < dependent_floor: continue

        # omit excluded labels
        if label in exclude_labels: continue

        # otherwise keep the rule
        rules.append(rule)

    return rules

if __name__ == "__main__":

    import metamathpy.setmm as ms

    num_sweeps = 3
    max_time = 10

    # ax_only = True
    # loader = ms.load_pl
    # goal_tokens = tuple("|- ( ph -> ( ps -> ph ) )".split(" "))
    # metavars = ("ph", "ps")

    ax_only = False
    loader = lambda : ms.load_to("mpd")
    goal_tokens = tuple("|- ( ph -> ph )".split(" "))
    metavars = ("ph",)

    db = loader()

    # filter rules
    rules = filter_rules(db, metavars, ax_only, dependent_floor=0, exclude_labels=())

    # run sweeps
    timeout = perf_counter() + max_time
    root_step = run_sweeps(num_sweeps, rules, goal_tokens, timeout, dbg=True)

    # # set up goals
    # root_goal = GoalNode(goal_tokens)
    # goals = {goal_tokens: [root_goal]}

    # proof_steps = {"wff": {}, "|-": {}}
    # for sweep in range(num_sweeps):

    #     # do the next sweep
    #     start = perf_counter()
    #     new_steps, new_goals = rule_sweep(rules, proof_steps, goals)
    #     duration = perf_counter() - start
    
    #     print(f"sweep {sweep}:")
    #     for typecode in ("wff", "|-"):
    #         print(f"new {typecode}s ({len(new_steps[typecode])} total):")
    #         for t, tokens in enumerate(new_steps[typecode]):
    #             print(f" {' '.join(tokens)}")
    #             if t == 10:
    #                 print(" ...")
    #                 break

    #     print(f"new goals ({len(new_goals)} total):")
    #     for t, tokens in enumerate(new_goals):
    #         print(f" {' '.join(tokens)}")
    #         if t == 10:
    #             print(" ...")
    #             break

    #     # integrate new proof steps, without replacing earliest encounters
    #     for typecode in ("wff", "|-"):
    #         proof_steps[typecode] = new_steps[typecode] | proof_steps[typecode]

    #     # integrate new goals (todo: deduplicate)
    #     for conclusion in new_goals:
    #         if conclusion not in goals: goals[conclusion] = []
    #         goals[conclusion].extend(new_goals[conclusion])                

    #     print("goal tree:")
    #     print(root_goal.tree_string())
    #     print(f"deficit = {root_goal.deficit(proof_steps['|-'])}")

    #     print(f"Took {duration:.3f}s ({duration/60:.3f}m)")

    #     root_step = root_goal.satisfy_from(proof_steps["|-"])
    #     if root_step is not None:
    #         print("Root is satisfied!")
    #         print(root_step.tree_string())
    #         break

    #     input("..")


