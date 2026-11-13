"""
Terms represented as trees
"""

def compose(s2, s1):
    """
    equivalent substitution to performing s1 followed by s2
    """
    s21 = {}
    for v1, t1 in s1.items():
        t1 = substitute(t1, s2)
        t = t1.prule.consequent.tokens
        if not (len(t) == 2 and t[1] == v1): s21[v1] = t1
    for v2, t2 in s2.items():
        if v2 not in s1: s21[v2] = t2
    return s21

class Term:
    def __init__(self, typecode, prule, children=()):
        self.typecode = typecode
        self.prule = prule
        self.children = children

    def tokenize(self):
        if len(self.children) == 0: return self.prule.consequent.tokens[1:]
        s = {v: c.tokenize() for (v,c) in zip(self.prule.mandatory.keys(), self.children)}
        return self.prule.scheme.substitute(s)[1:]

    def __repr__(self, prefix=''):
        # c = '\n'.join([c.__repr__(prefix+' ') for c in self.children])
        # return f'{prefix}Term({self.typecode}, {self.prule.consequent.label},\n{c})'
        return f"'{str(self)}'"

    def __str__(self):
        return " ".join(self.tokenize())

    def substitute(self, substitution):
        """
        direct substitution into term
        substitution = {var symbol: replacement term, ...}
        returns new term
        """
        t = self.prule.consequent.tokens
        if len(t) == 2 and t[1] in substitution: return substitution[t[1]]

        children = tuple(c.substitute(substitution) for c in self.children)
        return Term(self.typecode, self.prule, children)

    def contains(self, variable):
        """
        occurs check
        """
        t = self.prule.consequent.tokens
        if len(t) == 2 and t[1] == variable: return True

        for c in self.children:
            if c.contains(variable): return True

        return False

    def unify_with(self, other, variables):
        ts = self.prule.consequent.tokens
        to = other.prule.consequent.tokens
        if len(ts) == 2 and ts[1] in variables and not other.contains(ts[1]):
            return {ts[1]: other}
        elif len(to) == 2 and to[1] in variables and not self.contains(to[1]):
            return {to[1]: self}
        elif self.prule.consequent.label != other.prule.consequent.label:
            return None
        else:
            sub = {}
            for (cs, co) in zip(self.children, other.children):
                c_sub = cs.unify_with(co, variables)
                if c_sub is None: return None
                sub = compose(sub, c_sub)
            return sub

if __name__ == "__main__":

    import src.metamathpy.setmm as ms
    db = ms.load_pl()
    rules = db.rules_up_to("mp2")

    tph = Term("wff", db.rules["wph"])
    tps = Term("wff", db.rules["wps"])
    ti = Term("wff", db.rules["wi"], (tph, tps))
    subst = {"ph": ti, "ps": tph}
    print(subst)
    ts = ti.substitute(subst)
    print(tph)
    print(tps)
    print(ti)
    print(ts)
    assert tph.contains("ph")
    assert not tps.contains("ph")
    assert ti.contains("ph") and ti.contains("ph")
    assert ts.contains("ph") and ts.contains("ph")

    sub = ti.unify_with(ti, ("ph","ps"))
    print(sub)
    sub = ti.unify_with(ts, ("ph","ps"))
    print(sub)

    # # print(rules["wff"]["wph"])
    # print(db.rules["wi"])
    # print(db.rules["wi"].mandatory)

