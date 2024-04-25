"""
Run from top-level directory with
$ python -m src.metamathpy.environment
"""
from .proof import conduct

"""
Environment steps through normal proof verification process
Resets with a new claim to be proved and empty stack
State is current (claim, proof, stack)
Action is rule label
Step returns state, error message ("" means valid)
Done when top of stack matches claim

Attributes:
env.claim is current claim being proved
env.stack is the stack
env.proof is the list of labels in the uncompressed proof
"""
class Environment:
    def __init__(self, database):
        self.db = database
        self.claim = None
        self.proof = []
        self.stack = []

    def copy(self):
        env = Environment(self.db)
        env.claim = self.claim
        env.proof = list(self.proof)
        env.stack = list(self.stack)
        return env

    def reset(self, claim=None):
        self.claim = claim
        self.proof = []
        self.stack = []
        return (self.claim, list(self.proof), list(self.stack))

    # action is label of rule to apply
    def step(self, action):

        # enforce disjoint variables if proving a specific claim
        disjoint = set() if self.claim is None else self.claim.disjoint

        # conduct next proof step
        rule = self.db.rules[action]
        proof_step, msg = conduct(rule, self.stack, disjoint)

        # push proof step onto stack
        self.stack.append(proof_step)

        # save actions so far in proof
        self.proof.append(action)

        # return state and message
        state = (self.claim, list(self.proof), list(self.stack))
        return state, msg

if __name__ == "__main__":

    from .database import *
    import os
    fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = parse(fpath)
    print("parsed.")

    env = Environment(db)

    print("mpd proof:")
    claim = db.rules["mpd"]
    proof = ['wph', 'wph', 'wph', 'wi', 'wph', 'wph', 'wph', 'ax-1', 'wph', 'wph', 'wph', 'wi', 'ax-1', 'mpd']
    env.reset(claim)

    for a, action in enumerate(proof):
        (claim, _, stack), msg = env.step(action)
        assert msg == ""
        print(f"{a}: action = {action}")
        print('top of stack', stack[-1])

    print("\ninvalid step proof:")
    proof = ["wph", "wi"]
    env.reset()
    for a, action in enumerate(proof):
        (claim, _, stack), msg = env.step(action)
        print(f"{a}: action = {action}")
        print('top of stack:', stack[-1])
    assert msg != ""
    print(f"error message: {msg}")

    print("\nopen-ended:")
    proof = ["wph", "wps", "ax-1", "wph"]
    env.reset()
    for a, action in enumerate(proof):
        (claim, _, stack), msg = env.step(action)
        print(f"{a}: action = {action}, stack:")
        print(stack)

    env = Environment(db)
    print(env.reset())
    
    print(env.step("wph"))
    env2 = env.copy()

    print(env.step("wi"))
    print(env2.step("wps"))




