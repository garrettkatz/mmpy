"""
data structure:

    label -> floating | essential | axiom | proposition
    floating: (label, symbol, type)
    essential: (label, symbols)
    axiom: (label, symbols)
    proposition: (label, symbols, hypotheses, proof)

    scopes? constants? variables? proofs?

"""
import numpy as np
import os

def dbprint(db, prefix=""):
    for rec in db:
        if rec[0] == "${":
            print(prefix + "${")
            dbprint(rec[1], prefix + " ")
            print(prefix + "$}")

        elif rec[0] in ("$c", "$v", "$d"):
            print(f"{prefix}{rec[0]} {' '.join(rec[1])} $.")

        elif rec[1] in ("$f", "$e", "$a"):
            print(f"{prefix}{rec[0]} {rec[1]} {' '.join(rec[2])} $.")

        elif rec[1] == "$p":
            print(f"{prefix}{rec[0]} {rec[1]} {' '.join(rec[2])} $= {' '.join(rec[3])} $.")

if __name__ == "__main__":

    fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    # fpath = 'badparse.mm'

    db = [] # nested list of all declarations and statements
    stack = [db] # current scope stack
    comment = False # True if currently in a comment
    symbol_list = False # True if currently in a symbol list
    proof = False # True if currently in a proof
    label = None # most recently defined label
    num_statements = 0

    with open(fpath, "r") as f:
        for n, line in enumerate(f):

            for token in line.strip().split():

                # comments
                if token == "$(": comment = True
                if token == "$)": comment = False
                if comment: continue

                # end of symbol lists or proofs
                if token == "$.":
                    symbol_list = proof = False
                    num_statements += 1

                # scope
                if token == "${":
                    stack.append([])
                if token == "$}":
                    db.append(["${", stack.pop(), "$}"])

                # non-labeled declarations
                if token in ("$c", "$v", "$d"):
                    stack[-1].append([token, []])

                # labeled statements
                if token in ("$f", "$e", "$a", "$p"):
                    assert label != None, \
                           f"line {n+1}: {token} not preceded by label"
                    stack[-1].append([label, token, []])

                if token in ("$c", "$v", "$d", "$f", "$e", "$a", "$p"):
                    symbol_list = True

                if token == "$=":
                    symbol_list = False
                    proof = True
                    # stack > block > statement: append list for proof tokens
                    stack[-1][-1].append([])

                if token[0] != "$":

                    assert "$" not in token, \
                           f"line {n+1}: '$' not allowed in middle of {token}"

                    if symbol_list or proof:
                        # stack > block > statement > list: append token to symbol or proof list
                        stack[-1][-1][-1].append(token)
                    else:
                        label = token


    # print(db)
    dbprint(db[-100:])

    print(f"{num_statements} statements total")
    

    # ### numpy stuff

    # print("loading...")

    # # with open(fpath, "r") as f: raw = f.read()
    # # tokens = raw.split()
    # # line_numbers = []

    # tokens = []
    # line_numbers = []
    # with open(fpath, "r") as f:
    #     for n, line in enumerate(f):
    #         line_tokens = line.strip().split()
    #         tokens.extend(line_tokens)
    #         line_numbers.extend([n]*len(line_tokens))

    # tokens = np.array(tokens)
    # line_numbers = np.array(line_numbers)

    # print(len(tokens))
    # print(len(line_numbers))

    # print("removing comments...")

    # comments = ((tokens == "$(").cumsum() - (tokens == "$)").cumsum()) > 0
    # keep = ~comments & ~(tokens == "$)")    
    # tokens = tokens[keep]
    # line_numbers = line_numbers[keep]

    # print(len(tokens))
    # print(len(line_numbers))

    # print("calculating scope depths...")
    # scope_depth = ((tokens == "${").cumsum() - (tokens == "$}").cumsum())
    # keep = ~(tokens == "${") & ~(tokens == "$}")
    # tokens = tokens[keep]
    # line_numbers = line_numbers[keep]

    # print(len(tokens))
    # print(len(line_numbers))

    # # raw = " ".join(tokens)
    # # assert raw[1:].count("$") == raw.count(" $")

    
