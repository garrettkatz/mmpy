"""
Term representation is np.stack([types, values], dtype=int)
types are one of (RULE, POINTER, VARIABLE, SENTINEL)
data is not necessarily contiguous but it is monotonic (all subterms are later in the data array)
"""
you STILL have problems here. the potential for shared subterms complications substitution a lot? at least if you unify recursively.

something like this? shared variable table, so substition is just one pointer update.  a traversal iterator with a stack that walks current term top-level wff rule, and pushes current term when it hits a bound variable, dereferencing its pointer. each new term has standardized variables at each level to avoid clobbering. unification walks both iterators and updates free variable bindings on demand (iterator needs to dereference when advancing *past* a variable to reflect any on-demand changes just made). need a "trail" of most recent variables that were bound, so they can be undone when unification fails. this might cover everything except occurs-checking. occurs-checking has to be done like so: if checking whether to bind x in X to subterm of Y, continue walking the whole subterm checking for x until subterm is completely walked; only then do the binding (or fail). so the iterator has to expose its stack to some degree to check for subterms complete. the traversal iterator should still use operator form (dont re-traverse multiple occurrances of same subterm in token sequence).

seems like enough overhead to not be worth the single pointer update. maybe the issue is just the parsing? try to drive this top-down from unifor.

how bad would it be to store all the subterm lengths and just update all of them that span the substitution with a numpy few-liner?

import numpy as np
np.seterr(over='raise') # for variable index proliferation

# types for term elements
RULE, POINTER, VARIABLE, SENTINEL = range(4)

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
        return data

    def variable_term(self, variable_index):
        return np.array([[VARIABLE, variable_index]]).T

    def sentinel_term(self, sentinel_index):
        return np.array([[SENTINEL, sentinel_index]]).T

    def substitute(self, term, substitution):
        """
        term: data array
        substitution = {variable_index: replacement term, ...}
        """    
    
        top = term.copy()
        term_list = [top]
        offset = term.shape[1]
        var_mask = (term[0] == VARIABLE)
        for (v, subterm) in substitution.items():

            idx = var_mask & (term[1] == v)

            if subterm[0, 0] in (VARIABLE, SENTINEL):
                top[0, idx] = subterm[0, 0]
                top[1, idx] = subterm[1, 0]
            else:
                top[0, idx] = POINTER
                top[1, idx] = offset

                term_list.append(subterm)
                offset += subterm.shape[1]

        return np.concatenate(term_list, axis=1)

    def serialize(self, term):
        if term[0,0] == VARIABLE: return (f"v{term[1,0]}",)
        if term[0,0] == SENTINEL: return (f"s{term[1,0]}",)

        rule = self.rules[term[1,0]]
        substitution = {}
        for f, floating in enumerate(rule.floatings):
            if term[0, 1+f] == POINTER:
                subterm = term[:, term[1, 1+f]:]
            else:
                subterm = term[:, 1+f:]
            substitution[floating.tokens[1]] = self.serialize(subterm)

        return rule.scheme.substitute(substitution)[1:] # omit typecode

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

        term = self.substitute(self.compound_term(rule_index), substitution)
        return term, i

    def unify(self, d1, d2):
        if VARIABLE in (d1[0,0], d2[0,0]):
            if d1[0,0] != VARIABLE: d1, d2 = d2, d1
            if (d1[:,:1] == d2).all(axis=0).any(): return False, {} # occurs check
            return True, {d1[1,0]: d2}
        else:
            if (d1[0,0] != d2[0,0]) or (d1[1,0] != d2[1,0]): return False, {}
            if d1[0,0] == d2[0,0] == SENTINEL: return True, {}
            
            arity = self.arities[d1[1,0]]
            for a in range(arity):
                sd1, sd2 = d1[:,1+a:], d2[:,1+a:]
                if d1[0,1+a] == POINTER: sd1 = d1[:,d1[1,1+a]:]
                if d2[0,1+a] == POINTER: sd2 = d2[:,d2[1,1+a]:]

                success, subst = self.unify_helper(sd1, sd2)
                if not success: return False, {}

                d1
                you have to apply substitutions here to subterms

        return False, {}

if __name__ == "__main__":

    import src.metamathpy.setmm as ms
    db = ms.load_pl()
    rules = db.rules_up_to("mp2")
    tm = TermManager([rule for rule in rules["wff"] if rule.consequent.tag == "$a"])

    for r, rule in enumerate(tm.rules): print(r); print(rule)

    s = tm.sentinel_term(0)
    t = tm.variable_term(0)
    print(s)
    print(" ".join(tm.serialize(s)))
    print(t)
    print(" ".join(tm.serialize(t)))
    
    t2 = tm.compound_term(1)
    print(t2)
    print(" ".join(tm.serialize(t2)))

    t3 = tm.substitute(t2, {0: s, 1: t})
    print(t3)
    print(" ".join(tm.serialize(t3)))

    t4 = tm.substitute(t2, {0: t3, 1: t2})
    print(t4)
    print(" ".join(tm.serialize(t4)))

    t5, length = tm.parse(tuple("( ( ph -> ps ) -> -. ph )".split()), ("ph","ps"), ())
    print(t5)
    print("parse length", length)
    print(" ".join(tm.serialize(t5)))

