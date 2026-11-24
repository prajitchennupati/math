import sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from review_jack import *
import sympy as sp
x=sp.Symbol('x'); z=sp.Symbol('z')
def hit(mu,lam):
    n=sum(mu); S=schur_p(lam)
    al=[1009+2*k for k in range(n+2)]
    v=[fmpq(a)**n*pairing(jack_p(mu,1/fmpq(a)),S) for a in al]
    pts=[(sp.Integer(a),sp.Rational(int(w.p),int(w.q))) for a,w in zip(al,v)]
    p=sp.Poly(sp.interpolate(pts[:n+1],x),x); assert p.eval(pts[n][0])==pts[n][1]
    A=sp.Matrix([[sp.binomial(sp.Integer(m)+k,n) for k in range(n+1)] for m in range(1,n+2)])
    a=list(A.LUsolve(sp.Matrix([p.eval(m) for m in range(1,n+2)])))
    H=sp.Poly(sum(a[k]*z**k for k in range(n+1)),z)
    core=sp.Poly(sp.cancel(H.as_expr()/z**min(k for k in range(n+1) if a[k]!=0)),z)
    return all(c.is_integer and c>=0 for c in a), core.degree(), core.count_roots()
for k in range(2,10):
    try: print(k, hit((k,k),(2,)*k), flush=True)
    except AssertionError as e: print(k,'eigenvalue collision, method not applicable')
