"""
Run from parent directory with
$ python -m src.proof
"""
import itertools as it

try:
    profile
except NameError:
    profile = lambda x: x

"""
symbols[n]: nth token in symbol string
substitution[v]: symbol string to put in place of symbol v
returns result[n]: nth token after substitutions applied
"""
# @profile
def substitute(symbols, substitution):
    result = ()
    for symbol in symbols:
        if symbol in substitution: result += substitution[symbol]
        else: result += (symbol,)
    return result
# from substitute import substitute # cython version

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

    # recursively collect all proof steps along the way to this one
    def all_steps(self, explored = None):

        # skip duplicated steps
        if explored == None: explored = set()
        if self.conclusion in explored: return []
        explored.add(self.conclusion)

        steps = [self]
        for dep in self.dependencies.values():
            steps.extend(dep.all_steps(explored))
        return steps

"""
Apply a rule to a sequence of dependencies, each a previous proof step 
The conclusions of each dependency should match the hypotheses of the rule
returns the conclusion, matching substitution, and inherited disjoint variable requirements
"""
@profile
def perform(rule, dependencies):

    # form substitution that unifies hypotheses with dependencies
    substitution = {}
    for (hypothesis, dependency) in zip(rule.hypotheses, dependencies):

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
        else: #if hypothesis.tag == "$e":
            substituted = substitute(hypothesis.tokens, substitution)
            # substituted = hypothesis.after(substitution) # 29
            assert dependency.conclusion == substituted, \
                   f"{hypothesis.label}: {' '.join(dependency.conclusion)} != subst({' '.join(hypothesis.tokens)}, {substitution})"

    # get all variables in substituted expressions and pairs of variables being substituted
    subvars = {v: rule.variables.intersection(tokens) for (v, tokens) in substitution.items()}
    variable_pairs = set(it.combinations(sorted(substitution.keys()), 2))

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
    # conclusion = rule.consequent.after(substitution) # 46

    # return results
    return conclusion, substitution, inherited

"""
Conduct one step of a proof of claim
Applies given rule to top of stack; modifies stack in place
Returns the resulting proof step object
"""
@profile
def conduct(rule, stack, claim):

    # short-circuit hypothesis-less rules
    if len(rule.hypotheses) == 0:
        return ProofStep(tuple(rule.consequent.tokens), rule, {}, {})

    # pop top of stack
    split = len(stack) - len(rule.hypotheses)
    dependencies = stack[split:]
    del stack[split:]

    # get conclusion by applying rule to top of stack
    conclusion, substitution, disjoint = perform(rule, dependencies)

    # check against missing disjoint requirements
    assert disjoint <= claim.disjoint, \
        f"missing $d requirements: {disjoint} - {claim.disjoint} = {disjoint - claim.disjoint}"

    # wrap dependencies in dictionary by hypothesis label
    dependencies = {hyp.label: dep for (hyp, dep) in zip(rule.hypotheses, dependencies)}

    # return results of step
    return ProofStep(conclusion, rule, dependencies, substitution)

"""
claim: a rule object whose proof will be verified
"""
@profile
def verify_normal_proof(database, claim):

    # initialize stack of proof steps
    stack = []

    # initialize set of proof steps, indexed by conclusion (tupled for hashability)
    proof_steps = {}

    # process each label in proof
    for step, step_label in enumerate(claim.consequent.proof):

        # print(f"\n{step}")
        # print(stack)

        # conduct next proof step
        rule = database.rules[step_label]
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

@profile
def verify_compressed_proof(database, claim):

    # extract labels and mixed-radix pointer encodings
    split = claim.consequent.proof.index(")")
    step_labels = claim.consequent.proof[1:split]
    proof_string = ''.join(claim.consequent.proof[split+1:])

    # convert to integer pointers and save tagged steps
    A, U, Z = ord('A'), ord('U'), ord('Z')
    step_pointers = []
    pointer = 0
    for ordinal in map(ord, proof_string):
        if ordinal < U:
            pointer = 20 * pointer + (ordinal - A)
            step_pointers.append(pointer)
            pointer = 0
        elif ordinal < Z:
            pointer = 5 * pointer + (ordinal - U) + 1
        else:
            step_pointers.append(-1) # indicates previous step should be tagged

    # initialize proof stack
    stack = []

    # initialize buffer that gets dereferenced by step pointers
    proof_steps = []
    # steps for claim hypotheses
    for hypothesis in claim.hypotheses:
        conclusion, rule = tuple(hypothesis.tokens), database.rules[hypothesis.label]
        proof_steps.append(ProofStep(conclusion, rule, {}, {}))
    # step labels
    proof_steps += step_labels

    # process each step in proof
    proof_step_dict = {}
    for step, pointer in enumerate(step_pointers):

        # tag previous step if requested
        if pointer < 0: proof_steps.append(stack[-1])

        # otherwise handle current proof step
        else:

            # retrieve current step
            proof_step = proof_steps[pointer]

            # replace labels by associated step
            if type(proof_step) is str:
                proof_step = conduct(database.rules[proof_step], stack, claim)
                proof_step_dict[proof_step.conclusion] = proof_step

            # push current proof step onto stack
            stack.append(proof_step)

    # check that original claim has been proved
    assert stack[0].conclusion == tuple(claim.consequent.tokens), \
           f"proved statement {' '.join(stack[0].conclusion)} does not match theorem {' '.join(claim.consequent.tokens)}"
    assert len(stack) == 1, f"non-singleton stack {stack} after proof"

    # return root of proof graph and dictionary of nodes
    return stack[0], proof_step_dict

def verify_proof(database, claim):
    # compressed proofs start with "(" token
    if claim.consequent.proof[0] == "(":
        return verify_compressed_proof(database, claim)
    else:
        return verify_normal_proof(database, claim)

@profile
def verify_all(database, start=0, stop=-1):
    # verify all claims in the database
    for c, claim in enumerate(database.rules.values()):

        # only in specified slice
        if c < start: continue
        if c == stop: break

        # skip non-$p rules (axioms)
        if claim.consequent.tag != "$p": continue
        # print(c, claim.consequent.label)

        verify_proof(database, claim)


if __name__ == "__main__":

    from src.database import *

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
    print("parsed.")

    # verify_all(db)
    verify_all(db, stop=20000)
    # verify_compressed_proof(db, db.rules['ax5d'])

