"""
Routines for parsing logical formulae (not parsing a .mm database)
"""
import metamathpy.proof as mp

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
            root.add(tokens, rule)
    return root

def parse_rule(rule, rules, tokens, variables):

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
    for tok in rule.consequent.tokens[1:]:
        if i >= len(tokens): return False, 0

        if tok in rule.mandatory:
            result, length = parse(rules, tokens[i:], variables)
            if not result: return False, 0
            i += length

        elif tok != tokens[i]: return False, 0

        else: i += 1

    return True, i

def parse(rules, tokens, variables):
    if len(tokens) == 0: return False, 0
    if tokens[0] in variables: return True, 1
    for rule in rules:
        result, length = parse_rule(rule, rules, tokens, variables)
        if result: return True, length
    return False, 0

def unify(x, y, variables, rules):
    t = 0
    while t < len(x) and t < len(y):
        if x[t] in variables or y[t] in variables:
            if x[t] in variables:
                result, length = parse(rules, y[t:], variables)
                replacement = y[t:t+length]
                if x[t] in replacement: return False # occurs check
                s = {x[t]: replacement}
            else:
                result, length = parse(rules, x[t:], variables)
                replacement = x[t:t+length]
                if y[t] in replacement: return False # occurs check
                s = {y[t]: replacement}
            x = x[:t] + mp.substitute(x[t:], s)
            y = y[:t] + mp.substitute(y[t:], s)
            t += length
        else:
            if x[t] != y[t]: return False
            t += 1

    return t == len(x) == len(y)
    # return True

if __name__ == "__main__":

    import metamathpy.setmm as ms

    db = ms.load_pl()
    # root = build_parse_trie(db, ("wff","class"))
    # print(root.tree_string())

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
    for s, v, t in tests:
        # result, rule = root.prove(tuple(s.split()), v)
        # if result:
        #     if rule is None: print(f"{s}: True <= $f")
        #     else: print(f"{s}: True <= {rule.consequent.label}")
        # else: print(f"{s}: Fail")
        tokens = tuple(s.split())
        result, length = parse(wff_rules, tokens[1:], v)
        print(s, result)
        assert result == t
        if result: assert length == len(tokens)-1

    pairs = [ # standardize apart
        (("ph", "ps"), True),
        (("ph", "-. ps"), True),
        (("( ph -> ph )", "-. ps"), False),
        (("( ph -> ph )", "ps"), True),
        (("( ph -> ta )", "( ps -> ( ch -> ps ) )"), True),
        (("( ph -> ph )", "( ps -> ( ch -> ps ) )"), False),
        (("( ph -> ta )", "( ps -> ( ch -> ps )"), False),
    ]

    for p, t in pairs:
        result = unify(tuple(p[0].split()), tuple(p[1].split()), ("ph","ps","ch","ta"), wff_rules)
        print(p, result)
        assert result == t

