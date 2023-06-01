import itertools as it

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
Proof step: represents one step of a proof
conclusion: the symbol string that is concluded by applying an inference rule
rule: the rule object that was applied
dependencies[h]: another inference object, whose conclusion met the rule hypothesis with label h
substitution: the substitution that transforms the rule's consequent and hypotheses into the conclusion and dependencies
"""
class ProofStep:
    def __init__(self, conclusion, rule, dependencies, substitution):
        self.conclusion = conclusion # conclusion of the step
        self.rule = rule # justification for the step
        self.dependencies = dependencies # previous steps it relies on
        self.substitution = substitution # substitution that matches them

    def __repr__(self):
        return f"{self.rule.consequent.label} {' '.join(self.conclusion)}"

    def print(self, label="", prefix=""):
        subst = {key: " ".join(val) for key, val in self.substitution.items()}
        print(f"{prefix}[{label} <= {self.rule.consequent.label}] {' '.join(self.conclusion)} {subst}")
        for lab, dep in self.dependencies.items():
            dep.print(lab, prefix + " ")

"""
Apply a rule to a sequence of dependencies, each a previous proof step 
The conclusions of each dependency should match the hypotheses of the rule
returns the conclusion, matching substitution, and inherited disjoint variable requirements
"""
def perform(rule, dependencies):

    # form substitution that unifies hypotheses with dependencies
    substitution = {}
    for (hypothesis, dependency) in zip(rule.floatings + rule.essentials, dependencies):

        # update substitution for floating hypotheses
        if hypothesis.tag == "$f":

            # check matching types
            h_type, d_type = hypothesis.tokens[0], dependency.conclusion[0]
            assert h_type == d_type, \
                   f"{hypothesis.label}: mismatched types {h_type} vs {d_type}"

            # update substitution
            variable = hypothesis.tokens[1]
            substitution[variable] = dependency.conclusion[1:]

        # check that substitution unifies dependencies with essential hypotheses
        if hypothesis.tag == "$e":
            substituted = substitute(hypothesis.tokens, substitution)
            assert dependency.conclusion == substituted, \
                   f"{hypothesis.label}: {' '.join(dependency.conclusion)} != subst({' '.join(hypothesis.tokens)}, {substitution})"

    # get all variables in substituted expressions and pairs of variables being substituted
    subvars = {v: rule.variables.intersection(tokens) for (v, tokens) in substitution.items()}
    variable_pairs = {(min(u,v), max(u,v)) for (u,v) in it.product(substitution.keys(), repeat=2)}

    # disjoint variable checks
    inherited_disjoint = set()
    for (u, v) in variable_pairs & rule.disjoint:
        # check that disjoint variable substitutions remain disjoint
        assert len(subvars[u] & subvars[v]) == 0, f"{rule.consequent.label}: $d {u} {v} violated by {substitution}"
        # inherit disjoint requirements on the substituted variables
        for (x, y) in it.product(subvars[u], subvars[v]):
            inherited_disjoint.add((min(x, y), max(x, y)))

    # infer conclusion from the rule
    conclusion = substitute(rule.consequent.tokens, substitution)

    # return results
    return conclusion, substitution, inherited_disjoint

"""
claim: a rule object whose proof will be verified
"""
def verify_proof(database, claim):

    # initialize stack of proof steps
    stack = []

    # initialize set of proof steps, indexed by conclusion (tupled for hashability)
    proof_steps = {}

    # process each label in proof
    for step, step_label in enumerate(claim.consequent.proof):

        print(f"\n{step}")
        print(stack)

        # get corresponding statement in database
        statement = database.statements[step_label]

        # if step is a hypothesis of claim, push onto stack
        if statement.tag in ("$f", "$e"):

            # create placeholder inference for hypothesis if not already done
            conclusion = tuple(statement.tokens)
            if conclusion not in proof_steps:
                rule = Rule(statement, [], [], set(), set())
                proof_steps[conclusion] = ProofStep(conclusion, rule, {}, {})

            # push onto stack
            stack.append(proof_steps[conclusion])

        # if step is a rule, apply to top of stack
        if statement.tag in ("$a", "$p"):

            # look up rule, its consequent, and hypothesis labels
            rule = db.rules[step_label]
            consequent = statement.tokens
            hypotheses = rule.floatings + rule.essentials

            # pop dependencies, one per hypothesis
            split = len(stack) - len(hypotheses)
            stack, dependencies = stack[:split], stack[split:]

            # apply rule
            conclusion, substitution, disjoint = perform(rule, dependencies)

            # check against missing disjoint requirements
            assert disjoint <= claim.disjoint, \
                f"missing $d requirements: {disjoint} - {claim.disjoint} = {disjoint - claim.disjoint}"

            # only construct new proof step if not already done
            if conclusion not in proof_steps:

                # wrap dependencies in dictionary by hypothesis label
                dependencies = {hyp.label: dep for (hyp, dep) in zip(hypotheses, dependencies)}

                # construct and save proof step
                proof_steps[conclusion] = ProofStep(conclusion, rule, dependencies, substitution)

            # push step onto stack
            stack.append(proof_steps[conclusion])

    # check that original claim has been proved
    assert len(stack) == 1, f"non-singleton stack {stack} after proof"
    assert stack[0].conclusion == tuple(claim.consequent.tokens), \
           f"proved statement {' '.join(stack[0].conclusion)} does not match theorem {' '.join(claim.consequent.tokens)}"

    print(f"\nend:")
    print(stack)

    # return root of proof graph and dictionary of nodes
    return stack[0], proof_steps

def verify_compressed_proof(database, claim):

    # extract labels and mixed-radix indices of compressed proof
    split = claim.consequent.proof.index(")")
    step_labels = claim.consequent.proof[1:split]
    proof_string = ''.join(claim.consequent.proof[split+1:])
    ordinals = tuple(map(ord, proof_string))

    # convert to integer pointers and save tagged steps
    A, U, Z = ord('A'), ord('U'), ord('Z')
    tagged_steps = {}
    step_pointers = []
    pointer = 0
    for ordinal in ordinals:
        if ordinal < U:
            pointer = 20 * pointer + (ordinal - A)
            step_pointers.append(pointer)
            pointer = 0
        elif ordinal < Z:
            pointer = 5 * pointer + (ordinal - U) + 1
        else:
            tagged_steps[len(step_pointers) - 1] = step_pointers[-1]
    tagged_keys = tuple(tagged_steps.keys())

    # print(step_pointers)
    # print(tagged_steps)

    # setup offsets into hypotheses, labels, and tagged steps
    claim_hypotheses = claim.floatings + claim.essentials
    m = len(claim_hypotheses)
    n = len(step_labels)

    # print(f"proving {claim.consequent.label} with m={m} hypotheses {[hyp.label for hyp in claim_hypotheses]}")
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

    # initialize set of proof steps, indexed by conclusion (tupled for hashability)
    proof_steps = {}

    # initialize list of proved conclusions
    tagged_proof_steps = []

    # process each step in proof
    for step, pointer in enumerate(step_pointers):

        # print(f"\nstep {step+1}, pointer {pointer+1} stack:")
        # for i,inf in enumerate(stack): print(i, inf.rule.consequent.label, ' '.join(inf.conclusion)[:80], '...' if len(' '.join(inf.conclusion)) > 80 else '')
        # print("and tagged proof_steps:")
        # for i,inf in enumerate(tagged_proof_steps): print(i, tagged_keys[i]+1, inf.rule.consequent.label, ' '.join(inf.conclusion)[:80], '...' if len(' '.join(inf.conclusion)) > 80 else '')

        # if step is a hypothesis of claim, push onto stack
        if pointer < m:

            # get corresponding statement
            step_label = claim_hypotheses[pointer].label
            statement = database.statements[step_label]
            # print(f"using hypothesis {step_label}:", ' '.join(statement.tokens))

            # create placeholder inference for hypothesis
            conclusion = tuple(statement.tokens)
            rule = Rule(statement, [], [], set(), set())
            proof_steps[conclusion] = ProofStep(conclusion, rule, {}, {})

            # push onto stack
            stack.append(proof_steps[conclusion])

            # save tagged steps
            if step in tagged_steps:
                tagged_proof_steps.append(proof_steps[conclusion])

        # if step is a rule, apply to top of stack
        elif pointer < m + n:

            # get corresponding statement
            step_label = step_labels[pointer - m]
            statement = database.statements[step_label]

            # look up rule, its consequent, and hypothesis labels
            rule = db.rules[step_label]
            hypotheses = rule.floatings + rule.essentials
            # print(f"using rule {step_label}:", ' '.join(statement.tokens))
            # print("with hypotheses:", [hyp.label for hyp in hypotheses])

            # pop dependencies, one per hypothesis
            split = len(stack) - len(hypotheses)
            stack, dependencies = stack[:split], stack[split:]

            # apply rule
            conclusion, substitution, disjoint = perform(rule, dependencies)

            # check against missing disjoint requirements
            assert disjoint <= claim.disjoint, \
                f"missing $d requirements: {disjoint - claim.disjoint}"

            # wrap dependencies in dictionary by hypothesis label
            dependencies = {hyp.label: dep for (hyp, dep) in zip(hypotheses, dependencies)}

            # construct and save inference
            proof_steps[conclusion] = ProofStep(conclusion, rule, dependencies, substitution)

            # push inference onto stack
            stack.append(proof_steps[conclusion])

            # save tagged steps
            if step in tagged_steps:
                tagged_proof_steps.append(proof_steps[conclusion])

        # if step was already proved, push corresponding tagged inference back onto the stack again
        else:

            # get previously proved inference
            inference = tagged_proof_steps[pointer - (m + n)]

            # print(f"reusing ({pointer-(m+n)})th tagged previous step {tagged_keys[pointer - (m + n)]+1}: ", ' '.join(inference.conclusion))

            # push back onto stack
            stack.append(inference)

        # print("concluded", ' '.join(stack[-1].conclusion)[:80], '...' if len(' '.join(stack[-1].conclusion)) > 80 else '')


    # check that original claim has been proved
    assert stack[0].conclusion == tuple(claim.consequent.tokens), \
           f"proved statement {' '.join(stack[0].conclusion)} does not match theorem {' '.join(claim.consequent.tokens)}"
    assert len(stack) == 1, f"non-singleton stack {stack} after proof"

    # print(f"\nend:")
    # print(stack)

    # return root of proof graph and dictionary of nodes
    return stack[0], proof_steps

def verify_all(database):
    # verify all claims in the database
    for c, claim in enumerate(database.rules.values()):

        # skip non-$p rules (axioms)
        if claim.consequent.tag != "$p": continue
        print(c, claim.consequent.label)

        # compressed proofs start with "(" token
        if claim.consequent.proof[0] == "(":
            verify_compressed_proof(database, claim)
        else:
            verify_proof(database, claim)

if __name__ == "__main__":

    from database import *

    # fpath = "p2.mm"
    # db = parse(fpath)

    # db.print()
    # claim = db.rules['mpd']
    # claim.print()

    # proof_root, proof_steps = verify_proof(db, claim)
    # proof_root.print(claim.consequent.label)

    # print("\nall nodes:\n")
    # keys = list(proof_steps.keys())
    # for k, conclusion in enumerate(keys):
    #     step = proof_steps[conclusion]
    #     edges = [keys.index(dep.conclusion) for dep in step.dependencies.values()]
    #     print(k, " ".join(conclusion), step.rule.consequent.label, edges)

    import os
    fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = parse(fpath)

    verify_all(db)
    # verify_compressed_proof(db, db.rules['ax5d'])

