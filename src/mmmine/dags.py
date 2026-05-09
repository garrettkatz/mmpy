"""
To show:  the distribution of topologically sorted dag adjacency matrices is non-uniform and maybe band-limited (or band-limit is a predictable function of node index), e.g. binomial distribution curve? constant? linear? decay?
"""
import numpy as np

def allocate(conclusion, node_index):
    if conclusion in node_index: return node_index[conclusion]
    n = len(node_index) // 2
    node_index[conclusion] = n
    node_index[n] = conclusion
    return n

def dag(steps):
    A = np.zeros((len(steps), len(steps)))
    N = {}
    for (c, s) in steps.items():
        i = allocate(c, N)
        for d in s.dependencies.values():
            j = allocate(d.conclusion, N)
            # print(N)
            A[i,j] = 1
    return A, N

if __name__ == "__main__":
    from src.metamathpy.setmm import load_pl
    from src.metamathpy.proof import verify_compressed_proof
    db = load_pl()

    # marginalized unnormalized distributions of dag adjacency matrices by shape
    dists = {}

    print(db)
    r = 0
    for label, claim in db.rules.items():
        if claim.consequent.tag != "$p": continue
        print(claim)
        root, steps = verify_compressed_proof(db, claim)
        print(root.tree_string())
        # for step in steps.values():print(step)
        A, N = dag(steps)
        print(A.astype(int))
        print(N)
        for n in range(len(steps)): print(f"{n=}: {' '.join(N[n])}")
        r += 1
        # if r == 3: break
        print("seems it's already topologically sorted??")
        assert np.allclose(np.tril(A), A)

        if len(N) not in dists:
            dists[len(N)] = np.zeros(A.shape)
        dists[len(N)] += A

        # input('.')

        if r == 100: break

    np.set_printoptions(linewidth=100)
    for size in sorted(dists.keys()):
        print(f"\n{size=}")
        print(dists[size].astype(int))

    # you saw some kind of [a?]symmetry. in chaining from root vs leaves. what about "dag forests" with multiple roots? in other words sources and sinks in the dag.
    # from sources you can even have zero hypotheses. but from sink(s) you always have exactly one consequent.  on forward how do you want to balance <= 1 hyp vs >=1 hyp with == 1 consequent? does it influence search effort?

        

