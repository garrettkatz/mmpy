import numpy as np

# types for term elements
RULE, POINTER, VARIABLE, SENTINEL = range(4)

class Term:
    def __init__(self, data):
        """
        data = np.concatenate([types, values], axis=1)
        """
        self.data = data

    def __repr__(self):
        return f"Term(\n{self.data.T}.T)"

    def __eq__(self, other):
        return np.array_equal(self.data, other.data)

    def substitute(self, substitution):
        but substituting one variable with another should not create a pointer
    
    
        top_data = self.data.copy()
        all_data = [top_data]
        offset = len(self.data)
        var_mask = self.data[:,0] == VARIABLE
        for (v, t) in substitution.items():
            mask = var_mask & (self.data[:,1] == v)
            top_data[mask,:] = (POINTER, offset)
            all_data.append(t.data)
            offset += len(t.data)
        return Term(np.concatenate(all_data, axis=0))


class TermManager:
    def __init__(self, rules):
        """
        rules: list of wff rules (rule index is its id)
        """
        self.rules = rules
        self.arities = tuple(len(rule.floatings) for rule in rules)

    def rule_term(self, rule_index, subterms):
        but subterms that are variables should not create a pointer
        arity = self.arities[rule_index]
        offsets = np.cumsum([arity+1] + [t.data.shape[0] for t in subterms[:-1]])
        types = np.array([RULE] + [POINTER]*arity)
        values = np.concatenate([np.array([rule_index]), offsets])
        data = np.vstack([types, values]).T
        return Term(np.concatenate([data] + [t.data for t in subterms], axis=0))

    def variable_term(self, variable_index):
        return Term(np.array([[VARIABLE, variable_index]]))

    def sentinel_term(self, sentinel_index):
        return Term(np.array([[SENTINEL, sentinel_index]]))

    def unify(self, t1, t2):
        # t1, t2 are currently token sequences, replace with terms
        if t1 == t2: return True, {}
        return False, {}

if __name__ == "__main__":

    import src.metamathpy.setmm as ms
    db = ms.load_pl()
    rules = db.rules_up_to("mp2")
    tm = TermManager([rule for rule in rules["wff"] if rule.consequent.tag == "$a"])

    for r, rule in enumerate(tm.rules): print(r); print(rule)

    # t = Term(np.array([[1,2],[3,3]]))
    # print(t)

    s = tm.sentinel_term(0)
    t = tm.variable_term(0)
    print(t)
    
    t2 = tm.rule_term(1, [s, t])
    print(t2)

