import sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from jack import *
# (1) alpha=1: J_kappa = H_kappa s_kappa (H = product of hook lengths)
for n in range(1, 7):
    for kappa in partitions(n):
        S = schur_coeffs(jack_J_monomial(kappa, Fr(1)), n)
        kc = conj(kappa); H = 1
        for i, row in enumerate(kappa):
            for j in range(row): H *= (row - j - 1) + (kc[j] - i - 1) + 1
        assert S == {kappa: Fr(H)}, (kappa, S)
# (2) J_(2) = (1+alpha) m_2 + 2 m_11 ; J_(1,1) = 2 m_11
al = Fr(3, 7)
assert jack_J_monomial((2,), al) == {(2,): 1+al, (1, 1): Fr(2)}
assert jack_J_monomial((1, 1), al) == {(1, 1): Fr(2)}
# (3) AHW Prop: <J~_mu, h_{1^n}> = coefficient of m_{1^n} = n! alpha^n
for n in range(1, 7):
    for mu in partitions(n):
        al = Fr(5, 3)
        J = jack_J_monomial(mu, 1/al)
        assert J.get(tuple([1]*n), 0) * al**n == factorial(n) * al**n, mu
# (4) AHW mu=lambda: <J~_mu, s_mu> = prod_{s} (arm + alpha (leg+1))
for n in range(1, 7):
    for mu in partitions(n):
        al = Fr(7, 2)
        S = schur_coeffs({k: v*al**n for k, v in jack_J_monomial(mu, 1/al).items()}, n)
        kc = conj(mu); pr = Fr(1)
        for i, row in enumerate(mu):
            for j in range(row): pr *= (row - j - 1) + al*((kc[j] - i - 1) + 1)
        assert S[mu] == pr, (mu, S[mu], pr)
print('self-tests passed')
