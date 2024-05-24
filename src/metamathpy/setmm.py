import os
from ..metamathpy import database as md

def load_imp():
    # last label before any ax-3 proofs is loowoz, "rule" 264
    print('loading..')
    db = md.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"), max_rules=265)
    return db

def load_ni():
    # last label before any new boolean operator definitions is bijust, "rule" 441
    print('loading..')
    db = md.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"), max_rules=442)
    return db

def load_pl():

    # last label before any FOL (universal quantifier) is xorexmid, it is "rule" 2849 (including hypotheses)
    print('loading..')
    db = md.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"), max_rules=2850)
    return db

if __name__ == "__main__":

    db = load_imp()
    db.print()

