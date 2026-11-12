"""
Terms represented as trees
"""

class Term:
    def __init__(self, typecode, prule, children=()):
        self.typecode = typecode
        self.prule = prule
        self.children = children

    def tokenize(self):
        if len(self.children) == 0: return self.prule.consequent.tokens[1:]
        s = {f[1]: c.tokenize() for (f,c) in zip(self.prule.floatings, self.children)}
        return self.prule.scheme.substitute(s)[1:]

    def __str__(self):
        return " ".join(self.tokenize())

    def substitute(self, substitution):
        """
        direct substitution into term
        substitution = {var: replacement term, ...}
        returns new term
        """
        pass

if __name__ == "__main__":

    import src.metamathpy.setmm as ms
    db = ms.load_pl()
    rules = db.rules_up_to("mp2")

    tph = Term("wff", db.rules["wph"])
    tps = Term("wff", db.rules["wps"])
    ti = Term("wff", db.rules["wi"], (tph, tps))
    print(tph)
    print(tps)
    print(ti)

    # # print(rules["wff"]["wph"])
    # print(db.rules["wi"])
    # print(db.rules["wi"].mandatory)

