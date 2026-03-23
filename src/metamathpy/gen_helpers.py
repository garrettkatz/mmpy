# all n-tuples (n>0) of positive integers with constant sum s>=n
def constant_sum(s, n):
    if n == 1: yield (s,)
    else:
        for i in range(1,s-n+2):
            for t in constant_sum(s-i, n-1): yield (i,) + t


# all n-tuples (n>0) of positive integers p[i]>0 with multiplicity m[i], such that <p,m> = constant sum s
def constant_multisum(s, m):
    if len(m) == 1:
        q = s // m[0]
        if s == q*m[0]: yield (q,)
    else:
        slack = s - sum(m[1:])
        q = slack // m[0]
        if slack == q*m[0]:
            for i in range(1,q+1):
                for t in constant_multisum(s-i*m[0], m[1:]): yield (i,) + t


