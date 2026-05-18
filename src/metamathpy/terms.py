import numpy as np

# types for term elements
RULE, POINTER, VARIABLE, SENTINEL = range(3)

class Term:
    def __init__(self, data):
        """
        data = np.concatenate([types, values], axis=1)
        """
        self.data = data

    def __eq__(self, other):
        return np.array_equal(self.data, other.data)

    def substitute(self, substitution):
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
        arity = self.arities[rule_index]
        offsets = np.cumsum([arity] + [t.data.shape[0] for t in subterms[:-1]])
        types = np.array([RULE] + [POINTER]*arity)
        values = np.concatenate([np.array(rule_index), offsets])
        data = np.concatenate([types, values], axis=1)
        return Term(np.concatenate([data] + [t.data for t in subterms], axis=0))

    def variable_term(self, variable_index):
        return Term(np.array([[VARIABLE], [variable_index]]))

    def sentinel_term(self, sentinel_index):
        return Term(np.array([[SENTINEL], [sentinel_index]]))

    def unify(self, t1, t2):
        # t1, t2 are currently token sequences, replace with terms
        if t1 == t2: return True, {}
        return False, {}

if __name__ == "__main__":
    pass

