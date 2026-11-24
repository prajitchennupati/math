import sys, time; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from review_jack import *
import sympy as sp
mu=(8,8); lam=(2,)*8; n=16
S=schur_p(lam)
# sanity: s_lam from dual JT, check <s_lam,s_lam>=1
print('<s,s> =', pairing(S,S))
alphas=[1009+2*k for k in range(n+2)]   # generic points (avoid eigenvalue collisions); 17 for interpolation + 1 check
vals=[]
for a in alphas:
    t=time.time(); J=jack_p(mu, 1/fmpq(a)); v=fmpq(a)**n*pairing(J,S); vals.append(v)
    print(a, 'done', round(time.time()-t,1),'s', flush=True)
x=sp.Symbol('x')
pts=[(sp.Integer(a), sp.Rational(int(v.p),int(v.q))) for a,v in zip(alphas,vals)]
p=sp.Poly(sp.interpolate(pts[:n+1],x),x)
assert p.degree()<=n and p.eval(pts[n][0])==pts[n][1], 'deg check fails'
print('p =',p.as_expr())
author=sp.Poly(112*x**2*(x-1)**2*(x-2)**2*(x-3)**2*(x+1)*(2*x+1)*(104*x**6-684*x**5+2258*x**4-2901*x**3+8033*x**2+4530*x+12600),x)
print('equals author polynomial:', p==author)
A=sp.Matrix([[sp.binomial(sp.Integer(m)+k,n) for k in range(n+1)] for m in range(1,n+2)])
a=list(A.LUsolve(sp.Matrix([p.eval(m) for m in range(1,n+2)])))
print('a_k =',a)
z=sp.Symbol('z')
core=sp.Poly(sum(a[k]*z**(k-1) for k in range(1,n+1)),z)
print('a_0 =',a[0],'; deg core',core.degree(),'real roots (Sturm)',core.count_roots(),'squarefree',sp.gcd(core,core.diff(z)).degree()==0)
print('roots numeric', [sp.N(r,12) for r in sp.Poly(core).nroots(n=15,maxsteps=200)])
