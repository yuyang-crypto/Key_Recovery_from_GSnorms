"""
Toy implementation of the totally positive recovery algorithm in the
power basis (Algorithm 5.1 in the paper).

For a more serious implementation (also supporting approximate inputs),
try enum-chi.cpp.
"""

R=ZZ['t']
t=R.gen()

def genpol(n):
    return [randint(-2,2) for _ in range(n)]

def genkey(n):
    f = genpol(n)
    g = genpol(n)
    Mf= matrix(ZZ, n, lambda i,j: f[(j-i)%n] * (-1)^(i>j))
    Mg= matrix(ZZ, n, lambda i,j: g[(j-i)%n] * (-1)^(i>j))
    return (f, g, Mf.augment(Mg))

def gsonorms(B):
    G,_ = B.gram_schmidt()
    return [v.norm()^2 for v in G.rows()]
    
def extendstep(s,b):
    k = s.length() + 1
    S = matrix(ZZ, k-1, lambda i,j: s[abs(j-i)])
    dS= S.det()
    nu=-S.adjoint() * vector(R, [t] + s.list()[-1:0:-1])
    nu= vector(nu.list() + [dS])
    
    nn= [sum([nu[i]*nu[i-j] for i in range(j,k)])*(1+(j>0)) for j in range(k)]
    st= s.list() + [t]
    eq= R(sum([nn[i] * st[i] for i in range(k)]) - dS^2*b)
    if is_square(eq.disc()):
        return [vector(ZZ, s.list() + [r]) \
                    for r in eq.roots(multiplicities=False)]
    return []

def gsorecovery(bsq):
    cands = [vector(ZZ,[bsq[0]])]
    for b in bsq[1:]:
        candsnew = [extendstep(s,b) for s in cands]
        cands = []
        map(cands.extend, candsnew)
        #cands = sorted(set(cands))
        #print len(cands)
    return cands

def testrecovery(n):
    f,g,B = genkey(n)
    bsq = gsonorms(B)
    
    L = R.quotient(t^n+1)
    fbar = [f[0]] + [-f[n-j] for j in range(1,n)]
    gbar = [g[0]] + [-g[n-j] for j in range(1,n)]
    s = vector(ZZ, (L(f) * L(fbar) + L(g) * L(gbar)).list())

    print "Real value of s = ff*+gg*:"
    print s
    cands = gsorecovery(bsq)

    print "Recovered candidates (%d in total):" % len(cands)
    for sc in cands:
        print sc

    return s in cands

# vim: ft=python
