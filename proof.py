"""
symbols[n]: nth token in symbol string
substitution[v]: symbol string to put in place of symbol v
returns result[n]: nth token after substitutions applied
"""
def substitute(symbols, substitution):
    result = []
    for symbol in symbols:
        result.extend(substitution.get(symbol, [symbol]))
    return tuple(result)

"""
Inference: represents one step in a proof
rule: the rule object used to justify the step
conclusion: the symbol string that is concluded by applying the rule
dependencies[h]: another inference object, whose conclusion met the rule hypothesis with label h
substitution: the substitution that transforms the rule's consequent and hypotheses into the conclusion and dependencies
"""
class Inference:
    def __init__(self, rule, conclusion, dependencies, substitution):
        self.rule = rule # justification for the step
        self.conclusion = conclusion # conclusion of the step
        self.dependencies = dependencies # previous steps it relies on
        self.substitution = substitution # substitution that matches them

    def __repr__(self):
        return f"{self.rule.consequent} {' '.join(self.conclusion)}"

    def print(self, label="", prefix=""):
        subst = {key: " ".join(val) for key, val in self.substitution.items()}
        print(f"{prefix}[{label} <= {self.rule.consequent}] {' '.join(self.conclusion)} {subst}")
        for lab, dep in self.dependencies.items():
            dep.print(lab, prefix + " ")

"""
claim: a statement object whose proof will be verified
"""
def verify_proof(database, claim):

    # initialize stack of proof steps
    stack = []

    # initialize set of inferences, indexed by conclusion (tupled for hashability)
    inferences = {}

    # process each label in proof
    for step, step_label in enumerate(claim.proof):

        print(f"\n{step}")
        print(stack)

        # get corresponding statement in database
        statement = database.statements[step_label]

        # if step is a hypothesis of claim, push onto stack
        if statement.tag in ("$f", "$e"):

            # create placeholder inference for hypothesis if not already done
            conclusion = tuple(statement.tokens)
            if conclusion not in inferences:
                rule = Rule(database, step_label, [], [])
                inferences[conclusion] = Inference(rule, conclusion, {}, {})

            # push onto stack
            stack.append(inferences[conclusion])

        # if step is a rule, apply to top of stack
        if statement.tag in ("$a", "$p"):

            # look up rule, its consequent, and hypothesis labels
            rule = db.rules[step_label]
            consequent = statement.tokens
            hypothesis_labels = rule.floatings + rule.essentials

            # pop dependencies, one per hypothesis
            split = len(stack) - len(hypothesis_labels)
            stack, dependencies = stack[:split], stack[split:]

            # form substitution that unifies hypotheses with dependencies
            substitution = {}
            for h, label in enumerate(hypothesis_labels):

                # get current hypothesis and dependency to be unified
                hypothesis = database.statements[label]
                dependency = dependencies[h].conclusion

                # update substitution for floating hypotheses
                if hypothesis.tag == "$f":

                    # check matching types
                    h_type, d_type = hypothesis.tokens[0], dependency[0]
                    assert h_type == d_type, \
                           f"step {step} {label}: mismatched types {h_type} vs {d_type}"

                    # save replacement tokens
                    v = hypothesis.tokens[1]
                    substitution[v] = dependency[1:]

                # check that substitution unifies dependencies with essential hypotheses
                if hypothesis.tag == "$e":
                    assert dependency == substitute(hypothesis.tokens, substitution), \
                           f"step {step} {label}: {dependency} != subst({hypothesis.tokens}, {substitution})"

            # infer conclusion from the rule
            conclusion = substitute(consequent, substitution)

            # only construct new inference if not already done
            if conclusion not in inferences:

                # wrap dependencies in dictionary by hypothesis label
                dependencies = {h: dep for (h, dep) in zip(hypothesis_labels, dependencies)}

                # construct and save inference
                inferences[conclusion] = Inference(rule, conclusion, dependencies, substitution)

            # push inference onto stack
            stack.append(inferences[conclusion])

    # check that original claim has been proved
    assert len(stack) == 1, f"non-singleton stack {stack} after proof"
    assert stack[0].conclusion == tuple(claim.tokens), \
           f"proved statement {' '.join(stack[0].conclusion)} does not match theorem {' '.join(claim.tokens)}"

    print(f"\nend:")
    print(stack)

    # return root of proof graph and dictionary of nodes
    return stack[0], inferences

def verify_compressed_proof(database, claim):

    # extract labels and integer indices of compressed proof
    split = claim.proof.index(")")
    step_labels = claim.proof[1:split]
    ordinals = tuple(map(ord, claim.proof[split+1]))
    A, U, Z = ord('A'), ord('U'), ord('Z')
    step_indices = [0]
    for ordinal in ordinals:
        if A <= ordinal < U:
            step_indices[-1] = 20 * step_indices[-1] + (ordinal - A)
            step_indices.append(0)
        elif U <= ordinal < Z:
            step_indices[-1] = 5 * step_indices[-1] + (ordinal - U)
        else:
            pass

def verify_all(database):
    for c, claim in enumerate(database.statements.values()):
        if claim.tag != "$p": continue
        print(c)
        verify_proof(database, claim)

if __name__ == "__main__":

    import os
    from database import *

    fpath = "p2.mm"
    db = parse(fpath)

    db.print()
    thm = db.rules['mpd']
    thm.print()

    claim = db.statements[thm.consequent]
    proof_root, proof_nodes = verify_proof(db, claim)
    proof_root.print(claim.label)

    print("\nall nodes:\n")
    keys = list(proof_nodes.keys())
    for k, conclusion in enumerate(keys):
        inf = proof_nodes[conclusion]
        edges = [keys.index(dep.conclusion) for dep in inf.dependencies.values()]
        print(k, " ".join(conclusion), inf.rule.consequent, edges)

    # fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    # db = parse(fpath)
    # verify_all(db)

