"""
Prefix tree (trie) for fast binding against piles of proof steps
"""
try:
    profile
except NameError:
    profile = lambda x: x

class PileTrieNode:
    def __init__(self):
        self.step = None
        self.children = {}

    @profile
    def traverse(self, prefix):
        """
        Traverse path for given prefix and return node at the end (or None)
        """

        # base case: prefix traversed
        if len(prefix) == 0: return self

        # base case: this prefix not stored
        if prefix[0] not in self.children: return None

        # recursive case: traverse next token in prefix
        return self.children[prefix[0]].traverse(prefix[1:])

    def lookup(self, tokens):
        """
        Return the step (if any) for requested tokens, else None
        """
        node = self.traverse(tokens)
        if node is None: return None
        return node.step

    def __contains__(self, tokens):
        return self.lookup(tokens) is not None

    def __getitem__(self, tokens):
        step = self.lookup(tokens)
        if step is None: raise KeyError
        return step

    @profile
    def add(self, tokens, step):
        """
        Insert a new step whose conclusion is given tokens
        Called recursively on the tail of the tokens
        """

        # base case: all tokens traversed
        if len(tokens) == 0:
            self.step = step
            return

        # recursive case: traverse tokens, constructing new nodes when needed
        if tokens[0] not in self.children: self.children[tokens[0]] = PileTrieNode()
        self.children[tokens[0]].add(tokens[1:], step)

    def tree_string(self, prefix=""):
        s = ""
        for (token, node) in self.children.items():
            s += prefix + f"[{token}]: "
            if node.step is not None: s += str(node.step)
            s += "\n"
            s += node.tree_string(prefix+" ")
        return s

def trieify(pile):
    """
    Wrap existing pile dictionary (pile[conc] = step) in a PileTrie, return root
    """
    root = PileTrieNode()
    for key, value in pile.items(): root.add(key, value)
    return root

if __name__ == "__main__":

    strings = ["ph", "ph -> ps", "-. ph", "-. ps"]
    root = trieify({tuple(s.split()): s for s in strings})

    for s in strings:
        tokens = s.split()
        step = root.lookup(tokens)
        assert step == s

    assert root.lookup("ch -> ta".split()) is None
    assert root.lookup("ph -> ta".split()) is None

    print("all tests passed, tree string:")
    print(root.tree_string())
    
