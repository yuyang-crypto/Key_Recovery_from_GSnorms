"""
Implementation of the recovery of the Falcon secret key given the
Gram-Schmidt norms of the Falcon basis (Algorithm 5.2 in the paper,
together with the subsequent steps described in Section 4).

To test the code on parameters corresponding to the real implementation
of FALCON-512, you can for example try:

  testtowerrec(512)

which should take a few minutes to complete, and output ff* together with
the ideal (f). (Note that the final verification step testing the
equality of ideals takes a long time because PARI is slow, but this is
not part of the actual recovery algorithm).

A smaller toy example like:

  testtowerrec(64)

should be very fast.

The code requires a relatively recent version of SageMath.
"""

import itertools
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler

class SquareCheck(object):
    def __init__(self, bound=512,qprec=3):
        n=1
        self.primes = dict()
        self.ws     = dict()
        while n <= bound:
            n*= 2
            p = next(itertools.ifilter(lambda p: p>5000 and \
                        is_pseudoprime(p), itertools.count(2*n+1, 4*n)))
            self.primes[n] = p
            qp= Qp(p, prec=qprec)
            w = qp.primitive_root_of_unity(2*n)
            self.ws[n] = w
    
    def check(self, n, u):
        if n==1:
            return is_square(u)
        else:
            return is_square(u.lift().subs(self.ws[n]))
              
sqck = SquareCheck()

def PowerTwoCyclo(n):
    if n==1:
        return ZZ
    else:
        return QuotientRing(ZZ['x'], x^n + 1)

def sigma(y):
    l = y.list()
    return (y.parent())([(-1)^k*l[k] for k in range(len(l))])

def bar(y):
    l = y.list()
    n = len(l)
    if n==1:
        return y
    return (y.parent())(l[:1] + [-yi for yi in l[:0:-1]])

def resquad(y):
    l = y.list()
    n = len(l)
    if n==2:
        return l[0]
    else:
        return PowerTwoCyclo(n//2)([l[2*k] for k in range(n//2)])

def reltrace(y):
    return 2*resquad(y)

def relnorm(y):
    return resquad(y*sigma(y))

def div(y,k):
    l = y.list()
    if len(l)==1:
        return y/2
    return (y.parent())([yi/k for yi in l])

def liftquad(y):
    if y is None:
        return None
    l = y.list()
    n = len(l)
    return PowerTwoCyclo(2*n)([l[k//2] if is_even(k) else 0 for k in range(2*n)])

def cyclosqrtrec(n,y,fastsqcheck=True):
    """
    Compute the square root of y, an element of the ring of integers of
    the cyclotomic ring Z[zeta_{2n}], where n is assumed to be a power
    of two. The approach is a simple recursion.
    """
    if n==1:
        if is_square(y):
            return sqrt(y)
        else:
            return None

    tracey = reltrace(y)
    z  = y.parent().gen()
    zm2= bar(resquad(z^2))
    
    normx = cyclosqrtrec(n//2, relnorm(y), fastsqcheck)
    if normx is None:
        return None

    if fastsqcheck:
        if not sqck.check(n//2, tracey + 2*normx):
            normx = -normx

        tracex = cyclosqrtrec(n//2, tracey + 2*normx, fastsqcheck)
        if tracex is None:
            return None
    else:
        tracex = cyclosqrtrec(n//2, tracey + 2*normx, fastsqcheck)
        if tracex is None:
            normx = -normx
            tracex = cyclosqrtrec(n//2, tracey + 2*normx, fastsqcheck)
            if tracex is None:
                return None

    invtrx = cyclosqrtrec(n//2, (tracey - 2*normx)*zm2, fastsqcheck)
    if invtrx is None:
        return None
    
    x = div(liftquad(tracex) + z * liftquad(invtrx), 2)
    if x^2 == y:
        return x
    x = div(liftquad(tracex) - z * liftquad(invtrx), 2)
    if x^2 == y:
        return x

    return None

def cycrand(n,b=10):
    return PowerTwoCyclo(n).random_element(x=-b, y=b+1)

def testcyclosqrt(n,b=10,fastsqcheck=True):
    print """\
Computing square root of a random square in Z[x]/(x^%d + 1)
with coefficients up to %d.\
    """ % (n,b)
    y = cycrand(n,b)^2
    
    t = cputime(subprocesses=True)
    x = cyclosqrtrec(n,y,fastsqcheck)
    t = cputime(t)

    if x is None:
        print "Failed!"
    else:
        print "Done in %f seconds." % t

def is_totally_positive(n,u):
    if u != bar(u):
        return False
    w = CDF(exp(i*pi/n))
    e = min([u.lift().subs(w^(2*k+1)).real_part() for k in range(n//2)])
    return e >= 0

def towerrec(n,m):
    if n<=2:
        return [PowerTwoCyclo(n)(m[0])]

    nn= n//2
    tcands = towerrec(nn, m[:nn])
    mhat = [mi/m[nn-1] for mi in m[nn:]]
    acands = towerrec(nn, mhat)
    rcands = []
    for t in tcands:
        tl = liftquad(t)
        for a in acands:
            s = t*(t-a)
            u = cyclosqrtrec(nn, s/s.parent().gen())
            if u is None:
                continue
            u = liftquad(u)
            u = u*u.parent().gen()
            rcands += [tl + u, tl - u]
    return rcands

def genconj(n,u):
    w=u.parent().gen()
    return (u.lift().subs(w^(2*k+1)) for k in range(n//2))

def towerrecint(n,m,d=1):
    if n<=2:
        return PowerTwoCyclo(n)(m[0])

    nn= n//2
    t = towerrecint(nn, m[:nn], d)
    da= m[nn-1]
    ac= towerrecint(nn, m[nn:], da)
    for a in genconj(nn,ac):
        ta = d*t*a
        if gcd(ta.lift().coefficients()) % da != 0:
            continue
        s = t*t-ta/da
        u = cyclosqrtrec(nn, s*bar(s.parent().gen()))
        #if u is None:
        #    continue
        u = liftquad(u)
        u = u*u.parent().gen()
        return liftquad(t) + u


def bitrev(k,j):
    return reduce(lambda x,y: 2*x+y, j.digits(2, padto=k))

def falconmat(n,u):
    z = u.parent().gen()
    A = matrix(ZZ, [(u*z^k).list() for k in range(n)]) 
    k = ceil(log(n,2))
    p = [bitrev(k,ZZ(j))+1 for j in range(n)]
    P = Permutation(p).to_matrix()
    return P*A*P^(-1)
    
def falconminors(n,u):
    F = falconmat(n,u)
    return [F[:k,:k].det() for k in range(1,n+1)]

def falconrand(n,q=12289):
    Rq= QuotientRing(GF(q)['x'], x^n + 1) 
    sigma = RR(1.17*sqrt(q/(2*n)))
    D = DiscreteGaussianDistributionIntegerSampler(sigma=sigma)
    while True:
        f = PowerTwoCyclo(n)([D() for _ in range(n)])
        g = PowerTwoCyclo(n)([D() for _ in range(n)])
        Nf= f.norm()
        Ng= g.norm()
        if gcd(Nf,Ng)==1 and gcd(Nf,q)==1:
            break

    h = Rq(g.list()) / Rq(f.list())
    return f,g,h,f*bar(f) + g*bar(g)

def centlift(x,c):
    return c + (x-c).lift_centered()

def testtowerrec(n,q=12289):
    print "Generating random FALCON key."
    t = cputime(subprocesses=True)
    f,g,h,a = falconrand(n,q)
    t = cputime(t)
    print "Done in %.2f secs. Computing minors." % t
    t = cputime(subprocesses=True)
    m = falconminors(n,a)
    t = cputime(t)
    print "Done in %.2f secs. Start conjugate recovery." % t
    t = cputime(subprocesses=True)
    a0= towerrecint(n,m)
    t = cputime(t)
    print "Found candidate in %.2f secs. Start ideal recovery." % t
    hv= 1/(1+h*bar(h))
    K = CyclotomicField(2*n)
    Kf= K(f.list())

    t = cputime(subprocesses=True)
    for ac in genconj(n,a0):
        fql = (h.parent()(ac.list()) * hv).list()
        fcl = [centlift(fql[0], floor(1.17^2*q/2))] + \
                [centlift(fi,0) for fi in fql[1:]]
        if sum([fi^2 for fi in fcl[1:]]) > 2*q^2:
            continue
        ffc = K(fcl)
        gql = (h.parent()(ffc.list()) * bar(h)).list()
        gcl = [centlift(gi,0) for gi in gql]
        fgc = K(gcl)
        idc = K.ideal([ffc, fgc])
        break
    t = cputime(t)

    print "Recovered ff* and the ideal (f) in %.2f secs. Verifying..." % t
    t = cputime(subprocesses=True)
    check = (ffc == Kf*bar(Kf) and idc == K.ideal(Kf))
    t = cputime(t)
    print "Done in %.2f secs. Correct recovery? %s" % (t,check)

    return Kf, ffc, idc

# vim: ft=python
