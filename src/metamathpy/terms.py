import numpy as np
np.seterr(over='raise') # for variable index proliferation

# types for term elements
RULE, POINTER, VARIABLE, SENTINEL = range(4)

class Term:
    def __init__(self, data):
        """
        data = np.stack([types, values])
        """
        self.data = data

    def __repr__(self):
        return f"Term(\n{self.data})"

    def __eq__(self, other):
        return np.array_equal(self.data, other.data)

    def substitute(self, substitution):
        """
        substitution = {variable_index: term, ...}
        """    
    
        top_data = self.data.copy()
        all_data = [top_data]
        offset = self.data.shape[1]
        var_mask = (self.data[0] == VARIABLE)
        for (v, t) in substitution.items():

            idx = var_mask & (self.data[1] == v)

            if t.data[0, 0] in (VARIABLE, SENTINEL):
                top_data[0, idx] = t.data[0, 0]
                top_data[1, idx] = t.data[1, 0]
            else:
                top_data[0, idx] = POINTER
                top_data[1, idx] = offset

                all_data.append(t.data)
                offset += t.data.shape[1]

        return Term(np.concatenate(all_data, axis=1))


class TermManager:
    def __init__(self, rules):
        """
        rules: list of wff rules (rule index is its id)
        """
        self.rules = rules
        self.arities = tuple(len(rule.floatings) for rule in rules)

    def compound_term(self, rule_index):
        arity = self.arities[rule_index]
        data = np.empty((2, arity+1), dtype=int)
        data[:, 0] = (RULE, rule_index)
        data[0,1:] = VARIABLE
        data[1,1:] = range(arity)
        return Term(data)

    def variable_term(self, variable_index):
        return Term(np.array([[VARIABLE, variable_index]]).T)

    def sentinel_term(self, sentinel_index):
        return Term(np.array([[SENTINEL, sentinel_index]]).T)

    def serialize_helper(self, data):
        if data[0,0] == VARIABLE: return (f"v{data[1,0]}",)
        if data[0,0] == SENTINEL: return (f"s{data[1,0]}",)

        rule = self.rules[data[1,0]]
        substitution = {}
        for f, floating in enumerate(rule.floatings):
            if data[0, 1+f] == POINTER:
                arg_data = data[:, data[1, 1+f]:]
            else:
                arg_data = data[:, 1+f:]
            substitution[floating.tokens[1]] = self.serialize_helper(arg_data)

        return rule.scheme.substitute(substitution)[1:] # omit typecode

    def serialize(self, term):
        return self.serialize_helper(term.data)

    def parse(self, tokens, variables, sentinels, terms=None):
        """
        Determines if leading portion of tokens is parsable
            rules: list of parsing rules
            tokens: token sequence to parse
            variables, sentinels: sequences of tokens treated as parse leaves
            terms: dictionary of {subtokens: subterm} for recurring subterms
        returns (term, length) where
            term: term for leading portion if parsed successfully else None
            length: length of parsed leading portion
        """
        if len(tokens) == 0: return None, 0
        if terms is None: terms = {}
        if tokens[0] in variables or tokens[0] in sentinels:
            key = tokens[:1]
            if key not in terms:
                if tokens[0] in variables: terms[key] = self.variable_term(variables.index(tokens[0]))
                else: terms[key] = self.sentinel_term(variables.index(tokens[0]))
            return terms[key], 1
        for rule_index in range(len(self.rules)):
            term, length = self.parse_rule(rule_index, tokens, variables, sentinels, terms)
            if term is not None:
                terms[tokens[:length]] = term
                return term, length
        return None, 0

    def parse_rule(self, rule_index, tokens, variables, sentinels, terms=None):
        i = 0
        rule = self.rules[rule_index]
        mandatory = tuple(f.tokens[1] for f in rule.floatings)
        substitution = {}
        for tok in rule.consequent.tokens[1:]: # omit typecode
            if i >= len(tokens): return None, 0
    
            if tok in mandatory:
                # try parsing
                term, length = self.parse(tokens[i:], variables, sentinels, terms)
                if term is None: return None, 0
    
                # update substitution
                v = mandatory.index(tok)
                if v not in substitution:
                    substitution[v] = term
                else: assert substitution[v] == term
    
                i += length
    
            elif tok != tokens[i]: return None, 0
    
            else: i += 1

        term = self.compound_term(rule_index).substitute(substitution)
        return term, i

    def unify_helper(self, d1, d2):
        if VARIABLE in (d1[0,0], d2[0,0]):
            if d1[0,0] == VARIABLE:
                n = 1
                if d2[0,0] == RULE:
                    this is problematic... need to know the full length of a term's data, not just its top level'
                    probably fixed with a third array row of lengths?
                    n = self.arities[d2[1,0]]+1
                return True, {d1[1,0]: d2[:,:n]}
        else:
            if d1[0,0] != d2[0,0]: return False, {}
            if d1[1,0] != d2[1,0]: return False, {}
            if d1[0,0] == d2[0,0] == SENTINEL: return True, {}
            
            arity = self.arities[d1[1,0]]
            for a in range(arity):
                if d1[
                you have to apply substitutions here to subterms

        return False, {}

    def unify(self, t1, t2):
        success, substitution = self.unify_helper(t1.data, t2.data)
        if success:
            substitution = {v: Term(t) for (v,t) in substitution.items()}
        return success, substitution


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
    print(s)
    print(" ".join(tm.serialize(s)))
    print(t)
    print(" ".join(tm.serialize(t)))
    
    # t2 = tm.rule_term(1, [s, t])
    # print(t2)
    t2 = tm.compound_term(1)
    print(t2)
    print(" ".join(tm.serialize(t2)))

    t3 = t2.substitute({0: s, 1: t})
    print(t3)
    print(" ".join(tm.serialize(t3)))

    t4 = t2.substitute({0: t3, 1: t2})
    print(t4)
    print(" ".join(tm.serialize(t4)))

    t5, length = tm.parse(tuple("( ( ph -> ps ) -> -. ph )".split()), ("ph","ps"), ())
    print(t5)
    print("parse length", length)
    print(" ".join(tm.serialize(t5)))

