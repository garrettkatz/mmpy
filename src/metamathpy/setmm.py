import os
import src.metamathpy.database as md

def load_imp(fpath = None):
    # last label before any ax-3 proofs is loowoz
    print('loading..')
    if fpath is None:
        fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = md.parse(fpath, last_rule="loowoz")
    # negation wffs and ax-3 not used
    db.rules.pop("wn")
    db.rules.pop("ax-3")
    return db

def load_ni(fpath = None):
    # last label before any new boolean operator definitions is bijust, "rule" 441
    print('loading..')
    if fpath is None:
        fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = md.parse(fpath, last_rule="bijust")
    return db

def load_pl(fpath = None):

    # last label before any FOL (universal quantifier) is xorexmid, it is "rule" 2849 (including hypotheses)
    print('loading..')
    if fpath is None:
        fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = md.parse(fpath, last_rule="xorexmid")
    return db

def load_all(fpath = None):
    print('loading..')
    if fpath is None:
        fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = md.parse(fpath)
    return db

def load_to(last_rule, fpath = None):
    print('loading..')
    if fpath is None:
        fpath = os.path.join(os.environ["HOME"], "metamath", "set.mm")
    db = md.parse(fpath, last_rule=last_rule)
    return db

def new_usage_discouraged(fpath = None):
    if fpath is None:
        fpath = os.path.join(os.environ["HOME"], "set.mm", "discouraged")
    head = 'New usage of "'
    discouraged_labels = []
    with open(fpath, "r") as f:
        for line in f:
            if line[:len(head)] != head: continue
            tail = line[len(head):]
            label = tail[:tail.find('"')]
            discouraged_labels.append(label)
    return discouraged_labels

if __name__ == "__main__":

    # db = load_imp()
    # db = load_ni()
    db = load_pl()
    db.print()

    exclude = new_usage_discouraged()
    assert "idi" in exclude
    assert "a1ii" in exclude
    assert "idALT" in exclude
    assert "4syl" in exclude
    print(f"{len(exclude)} total new usage discourageds")

