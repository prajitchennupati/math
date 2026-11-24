import sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from review_jack import *
from fractions import Fraction
# J_(2)^{(a)} = p1^2 + (a-1)/2 p2 expected
print(jack_p((2,), fmpq(3)), jack_p((1,1), fmpq(3)))
# alpha=1: J_mu = hook-product * s_mu
for mu in [(3,1),(2,2),(4,2,1)]:
    n=sum(mu); J=jack_p(mu,fmpq(1)); S=schur_p(mu)
    h=1
    c=conj(mu)
    for i,r in enumerate(mu):
        for j in range(r): h*= (r-j-1)+(c[j]-i-1)+1
    ok = all(J.get(r,0)==h*S.get(r,0) for r in set(J)|set(S))
    print(mu,'alpha=1 hook*s_mu:',ok)
# paper: <J~_(3), s_21> = 2a^3-2a ; mu=lambda product formula prod(arm + a(leg+1))
for a in [2,3,5]:
    print('J~_(3),s_21', jt_coeff((3,),(2,1),a), 2*a**3-2*a)
def prod(mu,a):
    c=conj(mu); t=1
    for i,r in enumerate(mu):
        for j in range(r): t*= (r-j-1)+a*((c[j]-i-1)+1)
    return t
for mu in [(2,2),(3,2),(3,1,1),(4,2),(3,3),(2,2,2)]:
    for a in [2,7]:
        try:
            print(mu,a,jt_coeff(mu,mu,a)==prod(mu,a))
        except AssertionError:
            # this method needs a 1-dimensional eigenspace; it does not apply when two
            # Laplace-Beltrami eigenvalues coincide (e.g. (3,3) at alpha=2). It does apply to (8,8).
            print(mu,a,'skipped: eigenvalue collision, method not applicable')
# Theorem: a_k((n),lam)= n! QYT_{=k+1}(lam') ; check n=4 sum of a_k = n! * #SYT
print('sum a_k check n=3 lam=21: p(alpha)=2a^3-2a =', 2, 'binoms')
