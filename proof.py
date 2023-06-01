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
                           f"step {step} {label}: {' '.join(dependency)} != subst({' '.join(hypothesis.tokens)}, {substitution})"

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

    # extract labels and mixed-radix indices of compressed proof
    split = claim.proof.index(")")
    step_labels = claim.proof[1:split]
    proof_string = ''.join(claim.proof[split+1:])
    ordinals = tuple(map(ord, proof_string))

    # convert to integer pointers and save tagged steps
    A, U, Z = ord('A'), ord('U'), ord('Z')
    tagged_steps = {}
    step_pointers = []
    step_index = 0
    for ordinal in ordinals:
        if ordinal < U:
            step_index = 20 * step_index + (ordinal - A)
            step_pointers.append(step_index)
            step_index = 0
        elif ordinal < Z:
            step_index = 5 * step_index + (ordinal - U) + 1
        else:
            tagged_steps[len(step_pointers) - 1] = step_pointers[-1]
    tagged_keys = tuple(tagged_steps.keys())

    # print(step_pointers)
    # print(tagged_steps)

    # setup offsets into hypotheses, labels, and tagged steps
    claimed_rule = database.rules[claim.label]
    claim_hypothesis_labels = claimed_rule.floatings + claimed_rule.essentials
    m = len(claim_hypothesis_labels)
    n = len(step_labels)

    # print(f"proving {claim.label} with m={m} hypotheses {claim_hypothesis_labels}")
    # print(f"and n={n} step labels {step_labels}")
    # print(f"and proof string {proof_string}")
    # print("converted to ints", {i+1: pointer+1 for (i,pointer) in enumerate(step_pointers)})
    # print(f"with tagged steps {tagged_steps}")

    chunks = [chr(ordinals[0])]
    for i in range(1, len(ordinals)):
        if ordinals[i-1] == Z: chunks.append("")
        elif ordinals[i-1] < U and ordinals[i] != Z: chunks.append("")
        chunks[-1] += chr(ordinals[i])
    # for c,chunk in enumerate(chunks): print(c+1, chunk, step_pointers[c]+1)

    # initialize stack of proof steps
    stack = []

    # initialize set of inferences, indexed by conclusion (tupled for hashability)
    inferences = {}

    # initialize list of proved conclusions
    tagged_inferences = []

    # process each step in proof
    for step, pointer in enumerate(step_pointers):

        # print(f"\nstep {step+1}, pointer {pointer+1} stack:")
        # for i,inf in enumerate(stack): print(i, inf.rule.consequent, ' '.join(inf.conclusion)[:80], '...' if len(' '.join(inf.conclusion)) > 80 else '')
        # print("and tagged inferences:")
        # for i,inf in enumerate(tagged_inferences): print(i, tagged_keys[i]+1, inf.rule.consequent, ' '.join(inf.conclusion)[:80], '...' if len(' '.join(inf.conclusion)) > 80 else '')

        # if step is a hypothesis of claim, push onto stack
        if pointer < m:

            # get corresponding statement
            step_label = claim_hypothesis_labels[pointer]
            statement = database.statements[step_label]
            # print(f"using hypothesis {step_label}:", ' '.join(statement.tokens))

            # create placeholder inference for hypothesis
            conclusion = tuple(statement.tokens)
            rule = Rule(database, step_label, [], [])
            inferences[conclusion] = Inference(rule, conclusion, {}, {})

            # push onto stack
            stack.append(inferences[conclusion])

            # save tagged steps
            if step in tagged_steps:
                tagged_inferences.append(inferences[conclusion])

        # if step is a rule, apply to top of stack
        elif pointer < m + n:

            # get corresponding statement
            step_label = step_labels[pointer - m]
            statement = database.statements[step_label]

            # look up rule, its consequent, and hypothesis labels
            rule = db.rules[step_label]
            consequent = statement.tokens
            hypothesis_labels = rule.floatings + rule.essentials
            # print(f"using rule {step_label}:", ' '.join(consequent))
            # print("with hypotheses:", hypothesis_labels)

            # pop dependencies, one per hypothesis
            split = len(stack) - len(hypothesis_labels)
            stack, dependencies = stack[:split], stack[split:]
            # print(step, dependencies)

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
                    if h_type != d_type:
                        print(' '.join(hypothesis.tokens))
                        print(' '.join(dependency))
                    assert h_type == d_type, \
                           f"step {step} {label}: mismatched types {h_type} vs {d_type}"

                    # save replacement tokens
                    v = hypothesis.tokens[1]
                    substitution[v] = dependency[1:]

                # check that substitution unifies dependencies with essential hypotheses
                if hypothesis.tag == "$e":
                    if dependency != substitute(hypothesis.tokens, substitution):
                        print(' '.join(dependency))
                        print(' '.join(hypothesis.tokens))
                        print(' '.join(substitute(hypothesis.tokens, substitution)))
                        print({k: ' '.join(v) for k,v in substitution.items()})
                    assert dependency == substitute(hypothesis.tokens, substitution), \
                           f"step {step} {label}: {' '.join(dependency)} != subst({' '.join(hypothesis.tokens)}, {substitution})"

            # infer conclusion from the rule
            conclusion = substitute(consequent, substitution)

            # wrap dependencies in dictionary by hypothesis label
            dependencies = {h: dep for (h, dep) in zip(hypothesis_labels, dependencies)}

            # construct and save inference
            inferences[conclusion] = Inference(rule, conclusion, dependencies, substitution)

            # push inference onto stack
            stack.append(inferences[conclusion])

            # save tagged steps
            if step in tagged_steps:
                tagged_inferences.append(inferences[conclusion])

        # if step was already proved, push corresponding tagged inference back onto the stack again
        else:

            # get previously proved inference
            inference = tagged_inferences[pointer - (m + n)]

            # print(f"reusing ({pointer-(m+n)})th tagged previous step {tagged_keys[pointer - (m + n)]+1}: ", ' '.join(inference.conclusion))

            # push back onto stack
            stack.append(inference)

        # print("concluded", ' '.join(stack[-1].conclusion)[:80], '...' if len(' '.join(stack[-1].conclusion)) > 80 else '')


    # check that original claim has been proved
    assert stack[0].conclusion == tuple(claim.tokens), \
           f"proved statement {' '.join(stack[0].conclusion)} does not match theorem {' '.join(claim.tokens)}"
    assert len(stack) == 1, f"non-singleton stack {stack} after proof"

    # print(f"\nend:")
    # print(stack)

    # return root of proof graph and dictionary of nodes
    return stack[0], inferences

def verify_all(database):
    # verify all claims in the database
    for c, claim in enumerate(database.statements.values()):

        # only verify proposition statements
        if claim.tag != "$p": continue
        # print(c, claim.label)

        # compressed proofs start with "(" token
        if claim.proof[0] == "(":
            verify_compressed_proof(database, claim)
        else:
            verify_proof(database, claim)

if __name__ == "__main__":

    from database import *

    # fpath = "p2.mm"
    # db = parse(fpath)

    # db.print()
    # thm = db.rules['mpd']
    # thm.print()

    # claim = db.statements[thm.consequent]
    # proof_root, proof_nodes = verify_proof(db, claim)
    # proof_root.print(claim.label)

    # print("\nall nodes:\n")
    # keys = list(proof_nodes.keys())
    # for k, conclusion in enumerate(keys):
    #     inf = proof_nodes[conclusion]
    #     edges = [keys.index(dep.conclusion) for dep in inf.dependencies.values()]
    #     print(k, " ".join(conclusion), inf.rule.consequent, edges)

    import os
    fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = parse(fpath)
    verify_all(db)

