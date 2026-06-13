"""
term is represented as np.stack([ints, lens]).T where
    ints[i] is integer id of token at position i
    lens[i] is length of subterm starting at position i
"""
import numpy as np
np.seterr(over='raise') # for variable index proliferation

try:
    profile
except NameError:
    profile = lambda x: x

import src.metamathpy.database as md
import src.metamathpy.proof as mp

@profile
def rename(term, substitution):
    """
    substitution assuming all replacement terms are other variables
    used for standardizing apart, faster than substitute() below
    substitution = {old int id: new int id, ...}
    """
    renamed = term.copy()
    for (u,v) in substitution.items():
        renamed[(term[:,0] == u),0] = v
    return renamed

@profile
def substitute(term, substitution):
    """
    direct substitution into term
    substitution = {int id: replacement term, ...}
    returns new term (copied unless no changes)
    """

    # empty terms
    if len(term) == 0: return term

    # check if anything is being replaced
    replacement_index = [i for i in range(len(term)) if term[i,0] in substitution]
    if len(replacement_index) == 0: return term

    # update lengths
    term = term.copy()
    start = np.arange(len(term))
    stop = start + term[:,1]
    for i in replacement_index:
        bump = len(substitution[term[i,0]]) - 1 # -1 for singleton term being replaced
        inscope = (start <= i) & (i < stop)
        term[inscope,1] += bump

    # insert replacements
    chunks = [substitution[term[i,0]] if i in replacement_index else term[i:i+1] for i in range(len(term))]
    return np.concatenate(chunks, axis=0)

@profile
def substitute_single(term, v, t):
    """
    direct substitution into term
    substitution = {v: t}
    returns new term (copied unless no changes)
    """

    # empty terms
    if len(term) == 0: return term

    # check if anything is being replaced
    replacement_index = [i for i in range(len(term)) if term[i,0] == v]
    if len(replacement_index) == 0: return term

    # update lengths
    term = term.copy()
    start = np.arange(len(term))
    stop = start + term[:,1]
    for i in replacement_index:
        bump = len(t) - 1 # -1 for singleton term being replaced
        inscope = (start <= i) & (i < stop)
        term[inscope,1] += bump

    # insert replacements
    chunks = [t if i in replacement_index else term[i:i+1] for i in range(len(term))]
    return np.concatenate(chunks, axis=0)

@profile
def compose(s2, s1):
    """
    equivalent substitution to performing s1 followed by s2
    """
    s21 = {}
    for k, v in s1.items():
        t = substitute(v, s2)
        if t[0,0] != k: s21[k] = t
    for k, v in s2.items():
        if k not in s1: s21[k] = v
    return s21

@profile
def compose_single(v2, t2, s1):
    """
    equivalent substitution to performing s1 followed by {v2: t2}
    """
    s21 = {}
    for v1, t1 in s1.items():
        t = substitute_single(t1, v2, t2)
        if t[0,0] != v1: s21[v1] = t
    if v2 not in s1: s21[v2] = t2
    return s21

def singleton_term(int_id):
    return np.array([[int_id, 1]])

class TermManager:
    def __init__(self, rules):
        """
        rules: list of wff rules (rule index is its id)
        """
        self.rules = rules
        self.encoder = {}
        self.decoder = {}

        for rule in self.rules:
            for token in rule.consequent.tokens[1:]:
                self.encode(token)

    def encode(self, token):
        if token not in self.encoder:
            n = len(self.encoder)
            self.encoder[token] = n
            self.decoder[n] = token
        return self.encoder[token]

    def decode(self, i):
        return self.decoder.get(i, f"t{i}")

    def serialize(self, term):
        return tuple(map(self.decode, term[:,0]))

    def token_term(self, token):
        """
        Encodes token then wraps in a singleton term
        """
        return np.array([[self.encode(token), 1]])

    def rule_term(self, rule_index):
        """
        Term for a rule with no nested structure
        """
        rule_tokens = self.rules[rule_index].consequent.tokens[1:] # omit typecode
        term = np.array([[self.encode(token), 1] for token in rule_tokens])
        term[0,1] = len(term)
        return term

    def parse(self, tokens, sentinels):
        """
        Determines if leading portion of tokens is parsable
            tokens: token sequence to parse
            sentinels: tokens treated as parse leaves (typically variables)
        returns parsed term or None if parse fails
        """

        # no tokens left to parse
        if len(tokens) == 0: return None

        # next token is a leaf
        if tokens[0] in sentinels: return self.token_term(tokens[0])

        # next token starts a compound term, recurse
        for rule_index in range(len(self.rules)):
            term = self.parse_rule(rule_index, tokens, sentinels)
            if term is not None: return term

        # no matching rules, parse failed
        return None

    def parse_rule(self, rule_index, tokens, sentinels):
        """
        Determines if leading portion of tokens is parsable by particular rule
            rule_index: particular parsing rule to try
            tokens: token sequence to parse
            sentinels: tokens treated as parse leaves (typically variables)
        returns parsed term or None if parse fails
        """

        # extract rule and mandatory variables
        rule = self.rules[rule_index]

        # process tokens left to right, building up substitution 
        i = 0 # index in provided token sequence, not rule token sequence
        substitution = {}
        for tok in rule.consequent.tokens[1:]: # omit typecode

            # ran out of provided tokens, rule does not apply
            if i >= len(tokens): return None
    
            # current rule token is mandatory variable
            if tok in rule.mandatory:

                # try parsing replacement sub-term
                subterm = self.parse(tokens[i:], sentinels)
                if subterm is None: return None # parsing failed, rule does not apply
    
                # update substitution with parsed subterm
                v = self.encode(tok)
                if v not in substitution: substitution[v] = subterm
                else: assert np.array_equal(substitution[v], subterm)
    
                # advance past parsed subterm
                i += len(subterm)
    
            # current rule token is constant and does not match, rule does not apply
            elif tok != tokens[i]: return None

            # current rule token is constant and does match, advance one position
            else: i += 1

        # at this point the rule parsed successfully, form term and apply substitution
        return substitute(self.rule_term(rule_index), substitution)

    # def bind(self, tokens, variables, term):
    #     """
    #     bind variables in a token sequence to match a term
    #     fails if the term is not an instance of the token sequence
    #     returns substitution or None if failure
    #     """
    def instantiate(self, tokens, variables, term):
        """
        find substitution of variables in tokens that instantiate term
        "one-way" version of unification
        for example, application of a rule with given tokens and variables as consequent produces a term that it justifies
        fails if the term is not an instance of the token sequence
        returns substitution or None if failure
        """
        i, s = 0, {}
        for tok in tokens:
            if tok in variables:
                s[tok] = term[i:i+term[i,1]]
                i += term[i,1]
            else:
                if self.encode(tok) != term[i,0]: return None
                i += 1
        return s

    def parse_proof(self, term, steps):
        """
        Reconstruct the proof that the term is well-formed
        steps is a ProofStep dictionary to avoid duplicate subproofs
        """

        if len(term) == 1:
            v = self.decode(term[0,0])
            consequent = md.Statement('w'+v, '$a', ("wff", v), ())
            rule = md.Rule(consequent, (), (), (), (v,))
            rule.finalize()
            conclusion = consequent.tokens
            if conclusion not in steps:
                steps[conclusion] = mp.ProofStep(consequent.tokens, rule)
            return steps[conclusion]

        for rule in self.rules:
            # s = self.bind(rule.consequent.tokens[1:], rule.mandatory, term)
            s = self.instantiate(rule.consequent.tokens[1:], rule.mandatory, term)
            if s is None: continue

            conclusion = ("wff",) + self.serialize(term)
            if conclusion not in steps:
                dependencies = {}
                for f in rule.floatings:
                    dependencies[f.label] = self.parse_proof(s[f.tokens[1]], steps)
                substitution = {v: self.serialize(t) for (v,t) in s.items()}
                steps[conclusion] = mp.ProofStep(conclusion, rule, dependencies, substitution)
            return steps[conclusion]

@profile
def unify(t1, t2, variables):
    """
    unify two terms
        t1, t2: terms to unify, assumed to be standardized apart
        variables: set of integer ids representing substitutable variables
    returns substitution dictionary if successful else None
    """
    # build up substitution while consuming term heads until empty
    s = {}
    while len(t1) > 0 and len(t2) > 0:

        # if heads match, advance to tails
        if t1[0,0] == t2[0,0]:
            t1 = t1[1:]
            t2 = t2[1:]
            continue

        # check if either term head is a variable
        v1 = (t1[0,0] in variables)
        v2 = (t2[0,0] in variables)
        if v1 or v2:

            # swap if needed so t1 has the variable head
            if not v1: t1, t2 = t2, t1

            # extract variable and subterm
            v = t1[0,0] # variable integer id
            n = t2[0,1] # length of replacement term
            st = t2[:n] # replacement term

            # fail if v occurs in st
            if v in st[:,0]: return None

            # otherwise incorporate substitution and advance to term tails
            # s = compose_single(v, st, s)
            # t1 = substitute_single(t1[1:], v, st)
            # t2 = substitute_single(t2[n:], v, st)
            new_s = {v: st}
            s = compose(new_s, s)
            t1 = substitute(t1[1:], new_s)
            t2 = substitute(t2[n:], new_s)

        # otherwise term heads are distinct constants so fail
        else: return None

    # success if both terms fully consumed
    if len(t1) == len(t2) == 0: return s

    # otherwise failure
    return None

if __name__ == "__main__":

    import src.metamathpy.setmm as ms
    db = ms.load_pl()
    rules = db.rules_up_to("mp2")

    t1 = np.array([[1,0,0],[3,1,1]]).T
    t2 = substitute(t1, {0: t1})
    assert np.array_equal(t2, np.array([[1,1,0,0,1,0,0], [7,3,1,1,3,1,1]]).T)

    tm = TermManager([rule for rule in rules["wff"] if rule.consequent.tag == "$a"])
    t0 = tm.rule_term(0)
    t1 = tm.rule_term(1)
    assert " ".join(tm.serialize(t0)) == "-. ph"
    assert " ".join(tm.serialize(t1)) == "( ph -> ps )"

    for (s,v,r) in [
        ("-. ph", ["ph"], True),
        ("( ph -> ph )", ["ph"], True),
        ("( ph -> ps )", ["ph","ps"], True),
        ("( -. ph -> -. ( ps -> ph ) )", ["ph","ps"], True),

        ("-. (", ["ph"], False),
        ("( ph -> )", ["ph"], False),
        ("( ph ps )", ["ph","ps"], False),
        ("( -. ph -> -. ( ps -> ph )", ["ph","ps"], False),
    ]:
        print(s)
        t = tm.parse(s.split(), v)
        if r: 
            assert " ".join(tm.serialize(t)) == s
        else:
            assert t is None

    t1 = tm.parse("( ph -> ps )".split(), ["ph","ps"])
    t2 = tm.parse("( ph -> ph )".split(), ["ph"])
    t3 = tm.parse("( ch -> -. ( ta -> ch ) )".split(), ["ch", "ta"])

    s = unify(t1, t3, set(map(tm.encode, ["ph","ps","ch","ta"])))
    assert s is not None
    print({tm.decode(v): " ".join(tm.serialize(t)) for (v,t) in s.items()})

    s = unify(t2, t3, set(map(tm.encode, ["ph","ch","ta"])))
    assert s is None

