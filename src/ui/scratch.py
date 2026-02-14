"""
pip install blessed
"""
import itertools as it

from blessed import Terminal
from blessed.keyboard import Keystroke

from metamathpy.unification import substitute
import metamathpy.setmm as ms
import metamathpy.proof as mp

class SearchNode:

    def __init__(self, goal_tokens, rules):
        # goal_tokens: conclusion token tuple that self is trying to prove
        # rules: label-keyed dict of rules to be used in self's proof search
        self.goal_tokens = goal_tokens
        self.rules = rules

        # initialize proof steps by type, keyed by conclusion
        self.steps = {"wff": {}, "|-": {}}
        self.trace = []

    def setup(db, goal_label, rule_labels, ax_only=False):
        # factory helper that filters rules

        goal = db.rules[goal_label]
        rules = {}

        # process in reversed order for proximity prioritization
        for rule_label in reversed(rule_labels):
            rule = db.rules[rule_label]

            # for now, omit "rules" for essential hypotheses
            if rule.consequent.tag == "$e": continue

            # if requested, omit any non-axiom propositions
            if ax_only and rule.consequent.tag == "$p": continue

            # otherwise keep the rule
            rules[rule_label] = rule

        # add hypotheses of goal to rules
        for hyp in goal.hypotheses: rules[hyp.label] = db.rules[hyp.label]

        # print(goal_label, ":", list(rules.keys()))
        # input('.')

        return SearchNode(tuple(goal.consequent.tokens), rules)

    def is_solution(self):
        if len(self.trace) == 0: return False
        if self.trace[-1].conclusion == self.goal_tokens: return True
        return False

    def children(self):
        """
        Use with care; yields in-place modifications of self as each child
        """
        # try applying each rule
        for rule_label, rule in self.rules.items():

            # apply rule to all wff combinations for metavariables
            wffs = list(self.steps["wff"].values())
            for deps in it.product(wffs, repeat=len(rule.floatings)):

                # set up substitution
                substitution = {}
                for (hyp, dep) in zip(rule.floatings, deps):
                    # assert matching types (only works for PL)
                    assert hyp.tokens[0] == dep.conclusion[0] == "wff"
            
                    # update substitution
                    variable = hyp.tokens[1]
                    substitution[variable] = dep.conclusion[1:]

                # apply substitution and check if essentials are satisfied
                satisfied = True
                for hyp in rule.essentials:
                    substituted = substitute(hyp.tokens, substitution)
                    if substituted not in self.steps["|-"]:
                        satisfied = False
                        break
                    deps = deps + (self.steps["|-"][substituted],)

                # if not, move on to next combo
                if not satisfied: continue

                # otherwise, get conclusion and make sure inference checks out
                step, status = mp.perform(rule, deps)
                assert status == ""

                # append resulting proof step while yielding this child
                tokens = step.conclusion
                typecode = tokens[0] # wff or |-
                if tokens not in self.steps[typecode]:
                    self.steps[typecode][tokens] = step
                    self.trace.append(step)

                    yield self
    
                    # *** undo changes for next child, careful with this
                    self.steps[typecode].pop(tokens)
                    self.trace.pop()

        return

def dfs(node, depth_limit=0):

    # yield the current node before recursing
    yield node

    # check if max depth reached
    if depth_limit <= 0: return

    # if not, recurse search from each child
    for child in node.children():
        yield from dfs(child, depth_limit = depth_limit-1)

def ids(root, max_depth):
    for depth_limit in range(max_depth+1):
        yield from dfs(root, depth_limit)

if __name__ == "__main__":

    max_depth = 12

    term = Terminal()
    db = ms.load_pl()

    rule_labels = [label
        for label in db.rules.keys()
            if db.rules[label].consequent.tag in ("$p", "$a")]
    rule_index = 0

    # set up proof searches for each rule
    searches = {} # stores the generator
    solved, failed = set(), set() # sets of labels with success/failed proofs
    for r, label in enumerate(rule_labels):
        consequent = db.rules[label].consequent
        if consequent.tag == "$p":
            consequent.proof.clear()
            root = SearchNode.setup(db, label, rule_labels[:r], ax_only=False)
            # searches[label] = ids(root, max_depth)
            searches[label] = dfs(root, max_depth)
            if len(searches) == 10: break

    # # sanity check: try running a search "offline"
    # # label = "a1ii"
    # # label = "idi"
    # label = "mp2b"
    # worked = False
    # for n, node in enumerate(searches[label]):

    #     # stop if search ended successfully
    #     if node.is_solution():
    #         worked = True
    #         break

    # print(f"{n=}: {worked=}")
    # input('.')        

    # mm_code = db.rules[rule_labels[rule_index]].mm()
    # mm_code.replace("\n", "\n" + term.clear_eol)
    # print(mm_code)
    # input('.')

    # should check and branch on mouse support
    # https://blessed.readthedocs.io/en/latest/api/terminal.html#blessed.terminal.Terminal.does_mouse

    with term.fullscreen(), term.no_line_wrap(), term.mouse_enabled(), term.cbreak(), term.hidden_cursor():
    
        while True:

            # step all the proof searches multiple times per loop
            for search_step in range(100):
                for label in list(searches.keys()):
                    generator = searches[label]
                    try:
                        # get next node in the search
                        node = next(generator)
    
                        # update proof tokens
                        if len(node.trace) > 0:
                            proof_tokens = node.trace[-1].normal_proof()
                            db.rules[label].consequent.proof.clear()
                            db.rules[label].consequent.proof.extend(proof_tokens)
    
                        # if search ended successfully, remove it
                        if node.is_solution():
                            searches.pop(label)
                            solved.add(label)
    
                    except StopIteration:
                        # StopIteration means this search ended in failure, remove it
                        searches.pop(label)
                        failed.add(label)
                    

            H, W = term.height, term.width

            # eventually don't print everywhere, only the changes
            mm_lines = []
            rule_offset = 0
            while len(mm_lines) < H:
                mm_rule = db.rules[rule_labels[rule_index + rule_offset]].mm()
                mm_lines = mm_lines + mm_rule.split("\n")
                rule_offset += 1
            mm_lines = mm_lines[:H]
            # mm_code.replace("\n", term.clear_eol + "\n")

            # make cursor in center, not top
            mm_lines[0] = term.black_on_white(mm_lines[0] + term.clear_eol)
            mm_lines[1:] = [line + term.clear_eol for line in mm_lines[1:]]

            # print(term.move_xy(0,0) + mm_code + term.clear_eol, end='', flush=True)
            # print((term.clear_eol+"\n")*4, end='', flush=True)

            for offset in range(H):
                if offset < len(mm_lines):
                    # print(term.move_xy(0,offset) + mm_lines[offset] + term.clear_eol, end='', flush=True)
                    print(term.move_xy(0,offset) + mm_lines[offset], end='', flush=True)
                else:
                    print(term.move_xy(0,offset) + term.clear_eol, end='', flush=True)

            # https://blessed.readthedocs.io/en/latest/measuring.html#
            # print(term.move_xy(0,H-1) + f"[{rule_index} of {len(db.rules)}, {H//2} of {H}, 0 of {W}, {len(searches)} active searches]" + term.clear_eol, end='', flush=True)
            status_string = f"{len(searches)} active searches, {len(solved)} solved, {len(failed)} failed]"
            print(term.move_xy(0,H-1) + status_string + term.clear_eol, end='', flush=True)

            # # the clear_eol (end of line) could be useful when backtracking the iterative deepening proof search.
            # print(term.move_xy(10, 5) + f"here" + term.move_xy(12,3) + "also here" + term.clear_eol, end='', flush=True)

            # all key names:
            # https://blessed.readthedocs.io/en/latest/keyboard.html#all-names

            inp = term.inkey(timeout=0.01)

            if inp.is_sequence:
                # print(f"Special key: {inp.name} ({inp!r})")

                if inp.is_up(): rule_index = max(rule_index - 1, 0)
                if inp.is_down(): rule_index = (rule_index + 1) % len(db.rules)

            elif hasattr(inp, "name") and inp.name is not None and inp.name.startswith("MOUSE_"):
                print(repr(inp.name))
                print(inp.mouse_yx)

            elif inp == "q":
                break

        
