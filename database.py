from collections import namedtuple
import itertools as it

try:
    profile
except NameError:
    profile = lambda x: x

"""
Statement
    label: the label of the statement (str)
    tag: the type of statement ("$p", "$a", etc., str)
    tokens[n]: the nth token in the statement math symbol string (str)
    proof[n]: the nth token in the proof (str)
Rule:
    consequent: the rule's conclusion statement
    essentials[n]: the nth essential hypothesis statement
    floatings[n]: the nth floating hypothesis statement
Frame:
    frame[tag][n]: the nth
        constant or variable symbol if tag in "cv"
        list of disjoint variables if tag is "d"
        hypothesis if tag in "ef"
"""
class Statement:
    def __init__(self, label, tag, tokens, proof):
        self.label = label
        self.tag = tag
        self.tokens = tokens
        self.proof = proof
    def finalize(self):
        unique_tokens = {}
        self.token_pointers = []
        for token in enumerate(self.tokens):
            if token not in unique_tokens:
                unique_tokens[token] = len(unique_tokens)
            self.token_pointers.append(unique_tokens[token])
        self.unique_tokens = list(unique_tokens.keys())
    """
    substitution[v]: symbol string to put in place of symbol v
    returns substituted[n]: nth token after substitutions applied
    """
    @profile
    def after(self, substitution):
        substituted = {}
        for t, token in self.unique_tokens:
            if token in substitution:
                substituted[t] = substitution[token]
            else:
                substituted[t] = (token,)
        result = ()
        for p in self.token_pointers: result += substituted[p]
        return result

class Rule:
    def __init__(self, consequent, essentials, floatings, disjoint, variables):
        self.consequent = consequent
        self.essentials = essentials
        self.floatings = floatings
        self.disjoint = disjoint
        self.variables = variables
    def finalize(self):
        self.hypotheses = self.floatings + self.essentials
    def print(self):
        print(f"{self.consequent.label} {self.consequent.tag} {' '.join(self.consequent.tokens)} $.")
        print(f"disjoint variable sets: {self.disjoint}")
        for hypothesis in self.hypotheses:
            print(f"  {hypothesis.label} {hypothesis.tag} {' '.join(hypothesis.tokens)} $.")

def new_frame(): return {tag: [] for tag in "cvdfe"}

class Database:
    def __init__(self):
        self.statements = {} # looks up statements by label
        self.rules = {} # looks up rules by consequent's label

    def print(self, start=0):
        if start < 0: start = len(self.rules) + start
        for r, rule in enumerate(self.rules.values()):
            if r < start: continue
            rule.print()

def parse(fpath):

    db = Database()

    # parser state
    in_comment = False # whether currently in comment
    current_tag = None # most recent tag (excluding comments)
    label = None # most recent label
    statement = None # most recent statement
    frames = [new_frame()] # stack of frames in current scope

    # dbg = False

    with open(fpath, "r") as f:
        for n, line in enumerate(f):

            for token in line.strip().split():

                # if label == "df-alsc": dbg = True
                # if dbg:
                #     db.print(start=-2)
                #     print(f"token='{token}', label='{label}', tag='{current_tag}'")
                #     print(statement)
                #     input('..')    

                # skip comments
                if token == "$(": in_comment = True
                if token == "$)": in_comment = False
                if in_comment: continue

                # update scope
                if token == "${": frames.append(new_frame())
                if token == "$}": frames.pop()

                # initialize declarations
                if token in ("$c", "$v", "$d"):
                    statement = Statement(label, token, [], [])

                # initialize labeled statements
                if token in ("$f", "$e", "$a", "$p"):
                    assert label != None, \
                           f"line {n+1}: {token} not preceded by label"

                    statement = Statement(label, token, [], [])
                    db.statements[label] = statement

                # handle non-tag tokens
                if token[0] != "$":

                    # update label
                    label = token

                    # update statements
                    if current_tag is not None:
                        if current_tag in "cvdfeap":
                            statement.tokens.append(token)
                        elif current_tag == "=":
                            statement.proof.append(token)

                # handle completed statements and rules
                if token == "$.":

                    # update frame
                    if current_tag in "cv":
                        frames[-1][current_tag].extend(statement.tokens)
                    if current_tag == "d":
                        frames[-1][current_tag].append(sorted(statement.tokens))
                    if current_tag in "fe":
                        frames[-1][current_tag].append(statement)

                    # include placeholder "rules" for hypotheses
                    if current_tag in "fea=":
                        rule = Rule(statement, [], [], set(), set())

                    # attach scope to axioms and propositions
                    if current_tag in "a=":

                        # get all variables and essential hypotheses in current scope
                        for frame in frames:
                            rule.variables.update(frame["v"])
                            rule.essentials.extend(frame["e"])

                        # identify mandatory variables
                        tokens = set(statement.tokens)
                        for essential in rule.essentials:
                            tokens.update(essential.tokens)
                        mandatory = rule.variables & tokens

                        # save mandatory floating hypotheses
                        for frame in frames:
                            for floating in frame["f"]:
                                if floating.tokens[1] in mandatory:
                                    rule.floatings.append(floating)

                        # get disjoint variable pairs
                        for frame in frames:
                            for disjoint in frame["d"]:
                                rule.disjoint.update(it.combinations(disjoint, 2))

                    # finalize completed statements and rules and add to database
                    if current_tag in "fea=":
                        statement.finalize()
                        rule.finalize()
                        db.statements[statement.label] = statement
                        db.rules[statement.label] = rule

                # update current tag
                if token[0] == "$" and token[1] not in "()": current_tag = token[1]
                if current_tag in ("$.", "$}"): current_tag = None

    return db

if __name__ == "__main__":

    import os

    fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    # fpath = 'badparse.mm'
    # fpath = "p2.mm"

    db = parse(fpath)

    db.print(start=-3)
    # db.print()
    print(f"{len(db.statements)} statements total, {len(db.rules)} rules total")

    # for (label, stmt) in db.statements.items():
    #     print(label, stmt)
    
    # print(db.rules['df-alsc'])
    # print(db.rules['alsconv'])

