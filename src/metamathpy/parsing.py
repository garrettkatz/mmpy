"""
Routines for parsing logical formulae (not parsing a .mm database)
"""
import src.metamathpy.database as md
import src.metamathpy.proof as mp

try:
    profile
except NameError:
    profile = lambda x: x

class ParseTrieNode:
    def __init__(self):
        self.rule = None
        self.constant_children = {}
        self.variable_children = {}

    def add(self, tokens, rule):

        # base case: no tokens left
        if len(tokens) == 0:
            # confirm that each rule has a unique leaf
            assert len(self.constant_children) + len(self.variable_children) == 0
            self.rule = rule
            return

        # confirm that each rule has a unique leaf
        assert self.rule is None

        typecode = rule.mandatory.get(tokens[0], None) # None is constant
        if typecode is None:
            if tokens[0] not in self.constant_children:
                self.constant_children[tokens[0]] = ParseTrieNode()
            self.constant_children[tokens[0]].add(tokens[1:], rule)

        else:
            if tokens[0] not in self.variable_children:
                self.variable_children[tokens[0]] = (typecode, ParseTrieNode())
            self.variable_children[tokens[0]][1].add(tokens[1:], rule)

    def tree_string(self, prefix=""):
        s = ""
        for (token, node) in self.constant_children.items():
            s += prefix + f"[{token}]: "
            if node.rule is not None: s += node.rule.consequent.label
            s += "\n"
            s += node.tree_string(prefix+" ")
        for (token, (typecode, node)) in self.variable_children.items():
            s += prefix + f"[{token} {typecode}]: "
            if node.rule is not None: s += node.rule.consequent.label
            s += "\n"
            s += node.tree_string(prefix+" ")
        return s

    def prove(self, tokens, variables):

        # base case: out of tokens
        if len(tokens) == 0:
            if self.rule is None: return False, None
            return True, self.rule

        # base case: first token is a variable
        if tokens[0] in variables:
            return True, None

        if tokens[0] in self.constant_children:
            node = self.constant_children[tokens[0]]
            return node.prove(tokens[1:], variables)

        for v, (typecode, node) in self.variable_children.items(): pass
            

        return False, None

    # def prove(self, root, tokens, variables, substitution=None):
    #     """
    #     Build a proof that tokens are instances of a floating typecode
    #     Returns result, step, end
    #         result: True or False for successful proof or not
    #         step: top-level proof step
    #         end: proof applies to leading tokens[:end]
    #     """

    #     # initialize substitution at root
    #     if substitution is None: substitution = {}

    #     # base case: out of tokens
    #     if len(tokens) == 0:
    #         if self.rule is None: return False, None, 0
    #         return True, self.rule, 0
    #         # mp.ProofStep(conclusion, rule, dependencies=None, substitution=None, disjoint=None):

    #     # base case: first token is a variable
    #     if tokens[0] in variables:
    #         return True, None, 1

    #     # recursive case: first token is constant, proceed to tail
    #     if tokens[0] in self.constant_children:
    #         node = self.constant_children[tokens[0]]
    #         result, step, end = node.prove(root, tokens[1:], variables, substitution)
    #         return result, step, end+1

    #     # recursive case: first token begins a sub-formula
    #     for v, (typecode, node) in self.variable_children.items():
    #         success, step, end = root.prove(root, (typecode,) + tokens, variables, substitution)
    #         if not success: continue
    #         new_substitution = substitution | {v: tokens[:end]}
    #         success, step, end2 = node.prove(root, tokens[end:], variables, new_substitution)
    #         if success: return success, step, end + end2
        

def build_parse_trie(db, typecodes):
    root = ParseTrieNode()
    for label, rule in db.rules.items():
        if rule.consequent.tag != "$a": continue
        tokens = rule.consequent.tokens
        if tokens[0] in typecodes:
            root.add(tokens[1:], rule)
    return root

@profile
def trie_parse(root, node, tokens, singletons, prefix=None):
    """
    root: root of parse trie
    node: current position in parse trie, initialize to root
    tokens: token sequence to parse
    singletons: tokens to be parsed as length-1 formulae
    """

    # success if leaf node has been reached
    if node.rule is not None: return True, 0

    # otherwise, failure if tokens have been exhausted
    elif len(tokens) == 0: return False, 0

    # if top-level call (node is root) and next token is a singleton, success
    if node is root and tokens[0] in singletons: return True, 1

    # if next token is a valid constant, recurse on tail
    if tokens[0] in node.constant_children:
        result, length = trie_parse(root, node.constant_children[tokens[0]], tokens[1:], singletons, prefix)
        return result, length + 1

    # otherwise, failure if no variables at this position in trie
    if len(node.variable_children) == 0: return False, 0

    # at this point are at a variable, parse leading sub-formula for its substitution
    var_result, var_length = trie_parse(root, root, tokens, singletons, prefix)
    if not var_result: return False, 0

    # recurse on tail after leading sub-formula
    for (typecode, child) in node.variable_children.values():
        result, length = trie_parse(root, child, tokens[var_length:], singletons, prefix)
        if result: return True, var_length + length

    # no ways left to parse
    return False, 0

@profile
def parse_rule(rule, rules, tokens, variables, sentinels):
    """
    Determines if leading portion of tokens is parsable by particular rule as first argument
    Other arguments and return values as in parse(...)
    """

    # chunk = rule.scheme.chunks[0][1:]
    # i = len(chunk)
    # if chunk != tokens[:i]: return False, 0

    # for (v, chunk) in zip(rule.scheme.vartoks, rule.scheme.chunks[1:]):
    #     result, length = parse(rules, tokens[i:], variables)
    #     if not result: return False, 0
    #     i += length
    #     if chunk != tokens[i:i+len(chunk)]: return False, 0
    #     i += len(chunk)

    # return True, i

    # keep around for prefix tree?
    i = 0
    for tok in rule.consequent.tokens[1:]: # omit typecode
        if i >= len(tokens): return False, 0

        if tok in rule.mandatory:
            result, length = parse(rules, tokens[i:], variables, sentinels)
            if not result: return False, 0
            i += length

        elif tok != tokens[i]: return False, 0

        else: i += 1

    return True, i

@profile
def parse(rules, tokens, variables, sentinels):
    """
    Determines if leading portion of tokens is parsable
        rules: list of parsing rules
        tokens: token sequence to parse
        variables, sentinels: sets of tokens treated as parse leaves
    returns (parsed, length) where
        parsed: True if leading portion parsed successfully else False
        length: length of parsed leading portion
    """
    if len(tokens) == 0: return False, 0
    if tokens[0] in variables or tokens[0] in sentinels: return True, 1
    for rule in rules:
        result, length = parse_rule(rule, rules, tokens, variables, sentinels)
        if result: return True, length
    return False, 0

def parse_proof(rules, tokens, variables, sentinels, steps):
    """
    Like parse but returns a proof of parsability
    steps = {conc: step...} is a dictionary of already proven steps to avoid redundancy, initialize to {} before top-level call
    Returns (step, length):
        step is root of proof if successful, None otherwise
        length is same as parse(...)
    """
    if len(tokens) == 0: return None, 0
    if tokens[0] in variables or tokens[0] in sentinels:
        conclusion = ("wff", tokens[0])
        if conclusion not in steps:
            rule = md.Rule(md.Statement("w"+tokens[0], "$a", conclusion, ()), (), (), (), ())
            rule.finalize()
            steps[conclusion] = mp.ProofStep(conclusion, rule)
        return steps[conclusion], 1
    for rule in rules:
        step, length = parse_rule_proof(rule, rules, tokens, variables, sentinels, steps)
        if step is not None:
            steps[step.conclusion] = step
            return step, length
    return None, 0

def parse_rule_proof(rule, rules, tokens, variables, sentinels, steps):
    """
    Like parse_rule but returns a proof of parsability
    steps as in parse_proof
    Returns (step, length):
        step is root of proof if successful, None otherwise
        length is same as parse_rule(...)
    """
    i = 0
    substitution = {}
    dependencies = {}
    for tok in rule.consequent.tokens[1:]: # omit typecode
        if i >= len(tokens): return None, 0

        if tok in rule.mandatory:
            # try parsing
            step, length = parse_proof(rules, tokens[i:], variables, sentinels, steps)
            if step is None: return None, 0

            # store dependency
            idx = [f.tokens[1] for f in rule.floatings].index(tok)
            dependencies[rule.floatings[idx].label] = step

            # update substitution
            if tok not in substitution:
                substitution[tok] = tokens[i:i+length]
            else: assert substitution[tok] == tokens[i:i+length]

            i += length

        elif tok != tokens[i]: return None, 0

        else: i += 1

    conclusion = ("wff",) + tokens[:i]
    step = mp.ProofStep(conclusion, rule, dependencies, substitution)
    return step, i

@profile
def unify(x, y, variables, sentinels, rules):
    """
    x, y: token tuples to be unified, should be standardized apart
    variables: set of variable tokens in x and y
    sentinels: additional tokens like variables but not substitutable (for original metavariables in claims being proved)
    rules: list of available parsing rules
    returns success, subst
        success: True if unification succeeds else False
        subst: unifying substitution
    """
    t = 0
    subst = {}
    while t < len(x) and t < len(y):
        if x[t] == y[t]:
            t += 1

        elif x[t] in variables or y[t] in variables:
            if x[t] in variables:
                result, length = parse(rules, y[t:], variables, sentinels)
                replacement = y[t:t+length]
                if x[t] in replacement: return False, None # occurs check
                s = {x[t]: replacement}
            else:
                result, length = parse(rules, x[t:], variables, sentinels)
                replacement = x[t:t+length]
                if y[t] in replacement: return False, None # occurs check
                s = {y[t]: replacement}
            subst = mp.compose(s, subst)
            x = x[:t] + mp.substitute(x[t:], s)
            y = y[:t] + mp.substitute(y[t:], s)
            t += length

        else: # x[t], y[t] distinct constants
            return False, None

    if t == len(x) == len(y): return True, subst

    return False, None

@profile
def unify_trie(x, y, variables, sentinels, root):
    """
    x, y: token tuples to be unified, should be standardized apart
    variables: set of variable tokens in x and y
    sentinels: additional tokens like variables but not substitutable (for original metavariables in claims being proved)
    root: root of parse trie
    returns success, subst
        success: True if unification succeeds else False
        subst: unifying substitution if success else None
    """
    singletons = variables | sentinels
    t = 0
    subst = {}
    while t < len(x) and t < len(y):
        if x[t] == y[t]:
            t += 1

        elif x[t] in variables or y[t] in variables:
            if x[t] in variables:
                result, length = trie_parse(root, root, y[t:], singletons)
                replacement = y[t:t+length]
                if x[t] in replacement: return False, None # occurs check
                s = {x[t]: replacement}
            else:
                result, length = trie_parse(root, root, x[t:], singletons)
                replacement = x[t:t+length]
                if y[t] in replacement: return False, None # occurs check
                s = {y[t]: replacement}
            subst = mp.compose(s, subst)
            x = x[:t] + mp.substitute(x[t:], s)
            y = y[:t] + mp.substitute(y[t:], s)
            t += length

        else: # x[t], y[t] distinct constants
            return False, None

    if t == len(x) == len(y): return True, subst

    return False, None

if __name__ == "__main__":

    import metamathpy.setmm as ms

    db = ms.load_pl()
    root = build_parse_trie(db, ("wff","class"))
    print(root.tree_string())
    # input('.')

    wff_rules = [rule for rule in db.rules.values() if rule.consequent.tag == "$a" and rule.consequent.tokens[0] in ("wff", "class")]

    tests = [
        ("wff ph", set(["ph"]), True),
        ("wff ps", set(["ps"]), True),
        ("wff (", set(["ps"]), False),
        ("wff -. ph", set(["ph"]), True),
        ("wff ( ph", set(["ph"]), False),
        ("wff ( ph -> ph )", set(["ph"]), True),
        ("wff ( ph -> ph", set(["ph"]), False),
        ("wff ( ph -> ps )", set(["ph","ps"]), True),
        ("wff ( ph -> -. ( ps -> ph ) )", set(["ph","ps"]), True),
        ("wff ( ph -> ps -> ph )", set(["ph","ps"]), False),
        ("wff ( ( ph -> ps )", set(["ph","ps"]), False),
    ]
    for _ in range(1): # 100 for timing
        for s, v, t in tests:
            # result, rule = root.prove(tuple(s.split()), v)
            # if result:
            #     if rule is None: print(f"{s}: True <= $f")
            #     else: print(f"{s}: True <= {rule.consequent.label}")
            # else: print(f"{s}: Fail")
            tokens = tuple(s.split())
            result, length = parse(wff_rules, tokens[1:], v, ())
            print(s, result, length)
    
            # print("trie parse:")
            # tresult, tlength = trie_parse(root, root, tokens[1:], v, "")
            tresult, tlength = trie_parse(root, root, tokens[1:], v)
            print(tresult, tlength)
    
            assert result == tresult == t
            if result: assert length == tlength == len(tokens)-1
    
            step, length = parse_proof(wff_rules, tokens[1:], v, (), {})
            assert result == (step is not None)
            # if result:
            #     print(step.tree_string())
            #     input('.')

    # try with a sentinel
    step, length = parse_proof(wff_rules, tuple("( ph -> st )".split()), set(["ph"]), set(["st"]), {})
    assert step is not None
    print(step.tree_string())
    # input('.')

    pairs = [ # generally assumes standardized apart
        (("ph", "ph"), True), # though this should still work with empty substitution
        (("ph", "ps"), True),
        (("ph", "-. ps"), True),
        (("( ph -> ph )", "-. ps"), False),
        (("( ph -> ph )", "ps"), True),
        (("( ph -> ta )", "( ps -> ( ch -> ps ) )"), True),
        (("( ph -> ph )", "( ps -> ( ch -> ps ) )"), False),
        (("( ph -> ta )", "( ps -> ( ch -> ps )"), False),
    ]

    for _ in range(100):
        for p, t in pairs:
            success, subst = unify(tuple(p[0].split()), tuple(p[1].split()), ("ph","ps","ch","ta"), (), wff_rules)
            tsuccess, tsubst = unify_trie(tuple(p[0].split()), tuple(p[1].split()), set(["ph","ps","ch","ta"]), set(), root)
            print(p, success, subst)
            assert success == tsuccess == t

