import os
from parse import *

def substitute(symbols, substitution):
    result = []
    for symbol in symbols:
        result.extend(substitution.get(symbol, [symbol]))
    return result

# one inference step in a proof
class Inference:
    def __init__(self, rule, dependencies, substitution):
        self.rule = rule # justification for the step
        self.dependencies = dependencies # previous steps it relies on
        self.substitution = substitution # substitution that matches them
        self.conclusion = substitute(rule.symbols, substitution)
    def __repr__(self):
        return f"{self.rule.label} {' '.join(self.conclusion)}"
    def print(self, label="", prefix=""):
        subst = {key: " ".join(val) for key, val in substitution.items()}
        # print(f"{prefix}[{label} <= {self.rule.label}] {' '.join(self.conclusion)} <= {' '.join(self.rule.symbols)}")
        print(f"{prefix}[{label} <= {self.rule.label}] {' '.join(self.conclusion)}")
        for lab, dep in self.dependencies.items():
            dep.print(lab, prefix + " ")

if __name__ == "__main__":

    # fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    fpath = "p2.mm"
    db = parse(fpath)
    db.print()
    thm = db.get_statement('mpd')
    print(thm.label, thm.tag, thm.symbols)

    # get scope
    scope = thm.block.get_scope()
    print(scope)

    print("\n" + "*"*8 + "\n")

    # build uncompressed proof
    stack = []
    for s,label in enumerate(thm.proof):
        rule = db.get_statement(label)
        print(f"\n{s}")
        print(stack)
        print(rule)

        if type(rule) == Hypothesis:
            inf = Inference(rule, {}, {})
            stack.append(inf)

        if type(rule) in (Axiom, Proposition):

            scope = rule.block.get_scope(rule)

            # remove floating hypotheses for irrelevant variables
            variables = set(rule.symbols)
            for e in scope.e: variables.update(e.symbols)
            variables.intersection_update(scope.v)
            floats = [f for f in scope.f if f.symbols[1] in variables]

            # pop dependencies from stack
            hypotheses = floats + scope.e
            split = len(stack) - len(hypotheses)
            stack, dependencies = stack[:split], stack[split:]
            substitution = {}

            for dep, hyp in zip(dependencies, hypotheses):

                if hyp.tag == "$f":
                    r_type, r_sym = hyp.symbols[0], hyp.symbols[1:]
                    s_type, s_sym = dep.conclusion[0], dep.conclusion[1:]
                    assert len(r_sym) == 1, \
                           f"step {s} {label}: non-variable floating dependency {r_sym}"
                    assert r_type == s_type, \
                           f"step {s} {label}: mismatched types {r_type} vs {s_type}"
                    substitution[r_sym[0]] = s_sym

                if hyp.tag == "$e":
                    assert dep.conclusion == substitute(hyp.symbols, substitution), \
                           f"step {s} {label}: {s_hyp.symbols} != subst({hyp.symbols}, {substitution})"

            dependencies = {hyp.label: dep for (hyp, dep) in zip(hypotheses, dependencies)}
            inf = Inference(rule, dependencies, substitution)
            stack.append(inf)

    print(f"\nend:")
    print(stack)

    assert len(stack) == 1, f"non-singleton stack {stack} after proof"
    assert stack[0].conclusion == thm.symbols, f"proved statement {stack[0].conclusion} does not match theorem {thm.symbols}"

    root_inf = stack[0]
    root_inf.print(thm.label)


