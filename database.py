from collections import namedtuple

"""
Statement
    label: the label of the statement (str)
    tag: the type of statement ("$p", "$a", etc., str)
    tokens[n]: the nth token in the statement math symbol string (str)
    proof[n]: the nth token in the proof (str)
Rule:
    consequent: the label of the rule's conclusion statement (str)
    essentials[n]: the label of the nth essential hypothesis (str)
    floatings[n]: the label of the nth floating hypothesis (str)
Frame:
    frame[tag][n]: the nth
        constant or variable symbol if tag in "cv"
        list of disjoint variables if tag is "d"
        hypothesis if tag in "ef"
"""
Statement = namedtuple("Statement", ("label", "tag", "tokens", "proof"))

class Rule(namedtuple("Rule", ("database", "consequent", "essentials", "floatings"))):
    def print(self):
        consequent = self.database.statements[self.consequent]
        print(f"{consequent.label} {consequent.tag} {' '.join(consequent.tokens)} $.")
        for label in self.floatings + self.essentials:
            hypothesis = self.database.statements[label]
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
                        frames[-1][current_tag].append(statement.tokens)
                    if current_tag in "fe":
                        frames[-1][current_tag].append(statement)

                    # add completed statement to database
                    if current_tag in "feap":
                        db.statements[statement.label] = statement
    
                    # add completed rules to database
                    if current_tag == "f": 
                        rule = Rule(db, statement.label, [], [])
                        db.rules[rule.consequent] = rule

                    if current_tag in "a=":

                        # initialize new rule
                        rule = Rule(db, statement.label, [], [])

                        # get mandatory variables
                        tokens = set(statement.tokens)
                        for frame in frames:
                            for essential in frame["e"]:
                                tokens.update(essential.tokens)
                        variables = set([v for frame in frames for v in frame["v"]])
                        mandatory = variables & tokens

                        # get mandatory hypothesis labels
                        for frame in frames:
                            for essential in frame["e"]:
                                rule.essentials.append(essential.label)
                            for floating in frame["f"]:
                                if floating.tokens[1] in mandatory:
                                    rule.floatings.append(floating.label)

                        # insert rule into database
                        db.rules[rule.consequent] = rule

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

