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
    inherited = set()
    for (u, v) in variable_pairs & rule.disjoint:
        # check that disjoint variable substitutions remain disjoint
        assert len(subvars[u] & subvars[v]) == 0, f"{rule.consequent.label}: $d {u} {v} violated by {substitution}"
        # inherit disjoint requirements on the substituted variables
        for (x, y) in it.product(subvars[u], subvars[v]):
            inherited.add((min(x, y), max(x, y)))

    # infer conclusion from the rule
    conclusion = substitute(rule.consequent.tokens, substitution)

    # return results
    return conclusion, substitution, inherited

"""
Conduct one step of a proof of claim
Applies given rule to top of stack; modifies stack in place
Returns the resulting proof step object
"""
def conduct(rule, stack, claim):

    # get rule hypotheses
    hypotheses = rule.floatings + rule.essentials

    # short-circuit hypothesis-less rules
    if len(hypotheses) == 0:
        return ProofStep(tuple(rule.consequent.tokens), rule, {}, {})

    # pop top of stack
    split = len(stack) - len(hypotheses)
    dependencies = stack[split:]
    del stack[split:]

    # get conclusion by applying rule to top of stack
    conclusion, substitution, disjoint = perform(rule, dependencies)

    # check against missing disjoint requirements
    assert disjoint <= claim.disjoint, \
        f"missing $d requirements: {disjoint} - {claim.disjoint} = {disjoint - claim.disjoint}"

    # wrap dependencies in dictionary by hypothesis label
    dependencies = {hyp.label: dep for (hyp, dep) in zip(hypotheses, dependencies)}

    # return results of step
    return ProofStep(conclusion, rule, dependencies, substitution)

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

        # conduct next proof step
        rule = db.rules[step_label]
        proof_step = conduct(rule, stack, claim)
        conclusion = proof_step.conclusion

        # save new proof steps
        if proof_step.conclusion not in proof_steps:
            proof_steps[proof_step.conclusion] = proof_step

        # push proof step onto stack
        stack.append(proof_step)

    # check that original claim has been proved
    assert len(stack) == 1, f"non-singleton stack {stack} after proof"
    assert stack[0].conclusion == tuple(claim.consequent.tokens), \
           f"proved statement {' '.join(stack[0].conclusion)} does not match theorem {' '.join(claim.consequent.tokens)}"

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
            step_pointers.append(-1) # indicates last step should be tagged

    # initialize proof stack
    stack = []

    # initialize buffer dereferenced by step pointers
    proof_steps = []
    # steps for claim hypotheses
    for hypothesis in claim.floatings + claim.essentials:
        conclusion, rule = tuple(hypothesis.tokens), database.rules[hypothesis.label]
        proof_steps.append(ProofStep(conclusion, rule, {}, {}))
    # step labels
    proof_steps += step_labels

    # process each step in proof
    for step, pointer in enumerate(step_pointers):

        # tag previous step if requested
        if pointer < 0:
            proof_steps.append(stack[-1])

        # otherwise handle current proof step
        else:

            # retrieve current step
            proof_step = proof_steps[pointer]

            # replace labels by associated step
            if type(proof_step) is str:
                proof_step = conduct(db.rules[proof_step], stack, claim)

            # push current proof step onto stack
            stack.append(proof_step)

    # check that original claim has been proved
    assert stack[0].conclusion == tuple(claim.consequent.tokens), \
           f"proved statement {' '.join(stack[0].conclusion)} does not match theorem {' '.join(claim.consequent.tokens)}"
    assert len(stack) == 1, f"non-singleton stack {stack} after proof"

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

