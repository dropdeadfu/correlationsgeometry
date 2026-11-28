#!/usr/bin/env python3
"""Lapse response of the oscillators on the kernel graph (population level, flat slice) and the conjecture
eta = 4 pi b_lapse.

Question.  Is there a coefficient of the ground-state energy that measures the "lapse curvature" and equals
eta/(4 pi), eta the area-law coefficient of the entanglement entropy?  Covariance (hand derivation in the
report of task N3): for a static metric -N^2 dt^2 + h one has sqrt(-g) R4 = N sqrt(h) R_h - 2 sqrt(h) Lap_h N,
so on a FLAT slice  int sqrt(-g) R4 = -2 int Lap N = 0  and the induced action b int sqrt(-g) R4 gives NO term
of second order in delta N with two derivatives.  In the parametrisation (potential) of the paper,
L = ... + b_R R + b_a (grad ln N)^2, covariance demands b_a = 0.  The only lapse coefficient that carries b is
the MIXED one, b int delta N delta R (local curvature energy density, scripts/static_response_gamma.py).

This script computes, for N = 1 + eps cos(Q x_1),
   E2(Q) / (eps^2 Vol) = -(1/16) int d^Dk/(2 pi)^D  F(k,Q)^2 / (w_k w_q (w_k + w_q)),   q = k - Q,
(exact second-order perturbation theory on the infinite flat slice, uniform node density, continuum of modes),
and the effective coefficient  b_eff(Q) = -2 E2/(eps^2 Q^2)  (E = -L contains -b_a int (grad ln N)^2).
Realisations of the lapse:
  (L-A) H = int N h_A,  h_A = pi^2/2 + phi (L phi)/2 + m^2 phi^2/2       ->  F = (w_k - w_q)^2 / 2
  (L-B) H = int N h_B,  h_B with the edge energy split between the endpoints ->  F = F_A + (exp(-Q^2 xi^2/2)-1)/xi^2
        (divergent in the continuum of modes; radial mode cutoff kmax as a proxy for the node density)
  (M)   position-dependent gap m(x)^2 = mbar^2 Omega(x)^2 (Proposition "lapse" of the paper)  ->  F = 2 mbar^2
        (plus a Q-independent first-order term; only E(Q) - E(0) is reported)
Dispersion of the kernel graph: w^2 = (2/xi^2)(1 - exp(-xi^2 k^2/2)) + m^2; controls with w^2 = k^2 + m^2.
Analytic control: relativistic (M) has b_eff -> -mbar^2/(96 pi^2) in D = 3 (Euclidean bubble), i.e. E2 grows
with +mbar^2 Q^2/(192 pi^2); relativistic lapse with sharp cutoff: E2 = -(Q^4/2) ln(L/m)/(240 pi^2) + O(Q^4).

Also printed for the comparison table: b_R and rho_eff (eq. bRgraph), a (eq. aT, numerically), eta (imported
from scripts/area_law_vs_curvature.py, eta_continuum), and the mixed coefficient b_loc at q = 1 (imported from
scripts/static_response_gamma.py, n = 48, xi = 0.05).

Usage: lapse_response_coefficient.py      deterministic, no random numbers, about one minute.
"""
import sys
sys.dont_write_bytecode = True
import os
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def zeta(s, J=200000):
    j = np.arange(1, J + 1, dtype=float)
    c = np.empty(J)
    c[0] = 0.5
    c[1:] = 0.5 * np.cumprod((2 * j[:-1] - 1) / (2 * j[:-1] + 2))
    tail = c[-1] * J ** 1.5 * J ** (-(0.5 + s)) / (0.5 + s)
    return float(np.sum(c * j ** (-s)) + tail)


def panels(edges, n):
    x, w = np.polynomial.legendre.leggauss(n)
    X, Wt = [], []
    for a, b in zip(edges[:-1], edges[1:]):
        X.append(0.5 * (b - a) * x + 0.5 * (b + a))
        Wt.append(0.5 * (b - a) * w)
    return np.concatenate(X), np.concatenate(Wt)


def grids(D, Q, m, kmax):
    kmin = 1e-3 * min(m, Q)
    ke = np.concatenate([[0.0], np.geomspace(kmin, kmax, 140)])
    k, wk = panels(ke, 12)
    if D == 3:
        s = np.geomspace(2.0, 1e-7, 16)                    # 1 - c, refined towards c = 1 (q small for k ~ Q)
        ce = np.concatenate([[-1.0], 1.0 - s[1:], [1.0]])
        c, wc = panels(ce, 12)
        wang = 2 * np.pi * wc                               # int d^3k = int k^2 dk int dc 2 pi
        meas = k ** 2 / (2 * np.pi) ** 3
    else:
        te = np.concatenate([[np.pi], np.geomspace(np.pi / 2, 1e-6, 14), [0.0]])[::-1]
        th, wth = panels(te, 12)
        c = np.cos(th)
        wang = 2 * wth                                      # int d^2k = int k dk int_0^pi 2 dtheta
        meas = k / (2 * np.pi) ** 2
    return k, wk * meas, c, wang


def omega2(k2, xi, m, rel):
    return (k2 + m ** 2) if rel else (2 / xi ** 2) * (-np.expm1(-xi ** 2 * k2 / 2)) + m ** 2


def E2(D, Q, xi, m, form, rel=False, kmax=None, mbar=None):
    """E2(Q)/(eps^2 Vol) for the realisation `form` in {'A', 'B', 'min', 'M'}; for 'M' returns E2(Q)-E2(0)."""
    if kmax is None:
        kmax = 12.0 / xi
    k, wk, c, wang = grids(D, Q, m, kmax)
    K, C = np.meshgrid(k, c, indexing='ij')
    W = np.outer(wk, wang)
    q2 = K ** 2 + Q ** 2 - 2 * K * Q * C
    wk_ = np.sqrt(omega2(K ** 2, xi, m, rel))
    wq_ = np.sqrt(omega2(q2, xi, m, rel))
    if form == 'M':
        F2 = (2 * mbar ** 2) ** 2
        g = 1 / (wk_ * wq_ * (wk_ + wq_)) - 1 / (2 * wk_ ** 3)
        return -F2 / 16 * float(np.sum(W * g))
    # stable w_k - w_q:  (w_k^2 - w_q^2)/(w_k + w_q),  w_k^2 - w_q^2 = W(k) - W(q),  q^2 - k^2 = Q^2 - 2kQc
    d2 = Q ** 2 - 2 * K * Q * C
    if rel:
        dW = -d2
    else:
        dW = (2 / xi ** 2) * np.exp(-xi ** 2 * K ** 2 / 2) * np.expm1(-xi ** 2 * d2 / 2)
    diff = dW / (wk_ + wq_)
    F = 0.5 * diff ** 2                                     # form A
    if form == 'B':
        F = F + np.expm1(-Q ** 2 * xi ** 2 / 2) / xi ** 2
    elif form == 'min':                                     # relativistic minimal: m^2 - k.(Q-k) - w_k w_q
        F = F - Q ** 2 / 2
    return -1 / 16 * float(np.sum(W * F ** 2 / (wk_ * wq_ * (wk_ + wq_))))


def a_coeff(D, xi, m):
    """eq. (aT): a = 1/(8D(D+2)) int d^Dk/(2pi)^D k^4 W'(k^2)^2 / w^5,  W'(k^2) = exp(-xi^2 k^2/2)."""
    k, wk = panels(np.concatenate([[0.0], np.geomspace(1e-4 / xi, 15 / xi, 200)]), 12)
    sph = 4 * np.pi if D == 3 else 2 * np.pi
    w = np.sqrt(omega2(k ** 2, xi, m, False))
    integ = sph * k ** (D - 1) / (2 * np.pi) ** D * k ** 4 * np.exp(-xi ** 2 * k ** 2) / w ** 5
    return float(np.sum(wk * integ)) / (8 * D * (D + 2))


def main():
    xi = 1.0                                                 # all lengths in units of xi
    print("All quantities in units of xi (xi = 1); coefficients are 'times xi^{D-1}' etc.")
    # ---------------- controls ----------------
    print("\nControl 1: relativistic field, position-dependent mass (M), D = 3, m = mbar = 1, kmax = 400:")
    print("   Q      b_eff(Q) = -2 [E2(Q)-E2(0)]/(eps^2 Q^2)     analytic -1/(96 pi^2) = %.6e" % (-1 / (96 * np.pi ** 2)))
    for Q in (0.1, 0.03, 0.01):
        v = E2(3, Q, xi, 1.0, 'M', rel=True, kmax=400.0, mbar=1.0)
        print(f"  {Q:5.2f}   {-2 * v / Q ** 2: .6e}")
    print("\nControl 2: relativistic field, lapse H = int N h (minimal density), D = 3, m = 1, sharp cutoff kmax:")
    print("   kmax     Q     E2/(eps^2 Q^2)      E2/(eps^2 Q^4)     slope d/dln kmax (pred -1/(480 pi^2) = %.4e)"
          % (-1 / (480 * np.pi ** 2)))
    prev = None
    for km in (100.0, 200.0, 400.0):
        Q = 0.01
        v = E2(3, Q, xi, 1.0, 'min', rel=True, kmax=km)
        r4 = v / Q ** 4
        sl = "" if prev is None else f"{(r4 - prev[1]) / np.log(km / prev[0]): .4e}"
        print(f"  {km:6.0f}  {Q:5.2f}  {v / Q ** 2: .3e}     {r4: .6e}     {sl}")
        prev = (km, r4)

    # ---------------- comparison numbers ----------------
    D = 3
    rho = -zeta(D / 2) / (np.sqrt(2) * xi * (2 * np.pi * xi ** 2) ** (D / 2))
    bR = zeta(D / 2 - 1) * xi / (12 * np.sqrt(2) * (2 * np.pi * xi ** 2) ** (D / 2))
    a3 = a_coeff(3, xi, 0.0)
    a3m = a_coeff(3, xi, 0.05)
    from area_law_vs_curvature import eta_continuum
    eta3, _ = eta_continuum(128, 0.05, 1.0)                 # xi = 0.05, m xi = 0.05, chain of length 1
    eta3 *= 0.05 ** 2                                        # eta xi^2
    from static_response_gamma import node_energy
    n, xs = 48, 0.05
    e0 = node_energy(n, xs, 0.0, 1)
    rho_meas = (e0.mean() - np.sqrt(2) / xs / 2) * n ** 3
    eps = 0.02
    x1 = np.arange(n) / n
    de = (node_energy(n, xs, eps, 1) - node_energy(n, xs, -eps, 1)) / (2 * eps)
    cq = 2 * np.mean(de * np.cos(2 * np.pi * x1)) * n ** 3
    bloc = (cq + 3 * rho_meas) / (4 * (2 * np.pi) ** 2)
    bR_s = zeta(0.5) * xs / (12 * np.sqrt(2) * (2 * np.pi * xs ** 2) ** 1.5)
    print("\nComparison numbers, D = 3 (times xi^2):")
    print(f"  rho_eff xi^4 = {rho:.6e}, b_R xi^2 = {bR:.6e}  (eq. bRgraph)")
    print(f"  a xi^2 (eq. aT, m=0) = {a3:.6e};  with m xi = 0.05: {a3m:.6e}")
    print(f"  eta xi^2 (area_law_vs_curvature.eta_continuum(128, 0.05, 1.0)) = {eta3:.6e};  eta/(4 pi) xi^2 = {eta3 / (4 * np.pi):.6e}")
    print(f"  mixed lapse x curvature coefficient b_loc (static_response_gamma, n=48, xi=0.05, q=1, (2 pi xi)^2 = {(2*np.pi*xs)**2:.4f}):"
          f" b_loc/b_R = {bloc / bR_s:.4f}, b_loc xi^2 = {bloc * xs ** 2:.6e}")
    print(f"  ratios: (eta/4pi)/b_R = {eta3 / (4 * np.pi) / bR:.4f}, (eta/4pi)/a = {eta3 / (4 * np.pi) / a3:.4f},"
          f" (eta/4pi)/b_loc = {eta3 / (4 * np.pi) / (bloc * xs ** 2):.4f}, b_R/a = {bR / a3:.4f}")

    # ---------------- kernel graph: lapse response ----------------
    for D in (3, 2):
        bRD = zeta(D / 2 - 1) * xi / (12 * np.sqrt(2) * (2 * np.pi * xi ** 2) ** (D / 2))
        print(f"\nKernel graph, D = {D}, b_R xi^(D-1) = {bRD:.6e}.  b_eff(Q) = -2 E2/(eps^2 Q^2) in units of b_R:")
        print("  m xi    Q xi    (L-A) b_eff/b_R    (L-A) E2/(eps^2 Q^4)    (L-B,kmax=pi*3/xi) b_eff/b_R    (M, mbar=m) b_eff/b_R")
        for m in (0.05, 0.2):
            for Q in (1.0, 0.3, 0.1, 0.03, 0.01):
                vA = E2(D, Q, xi, m, 'A')
                vB = E2(D, Q, xi, m, 'B', kmax=3 * np.pi)
                vM = E2(D, Q, xi, m, 'M', mbar=m)
                print(f"  {m:4.2f}  {Q:6.3f}   {-2 * vA / Q ** 2 / bRD: .3e}        {vA / Q ** 4: .5e}"
                      f"            {-2 * vB / Q ** 2 / bRD: .3e}              {-2 * vM / Q ** 2 / bRD: .3e}")
        if D == 3:
            print("  (M) against the relativistic IR value -mbar^2/(96 pi^2), Q xi = 0.01:")
            for m in (0.2, 0.05, 0.01):
                vM = E2(3, 0.01 * m / 0.05 if m < 0.05 else 0.01, xi, m, 'M', mbar=m)
                Qu = 0.01 * m / 0.05 if m < 0.05 else 0.01
                print(f"     m xi = {m:5.3f}:  b_eff/(-mbar^2/(96 pi^2)) = {(-2 * vM / Qu ** 2) / (-m ** 2 / (96 * np.pi ** 2)):.5f}"
                      f",  b_eff/b_R = {-2 * vM / Qu ** 2 / bRD: .3e}")
        print("  (L-B) Q^4 coefficient against the mode cutoff (node density proxy), m xi = 0.05, Q xi = 0.01:")
        for km in (np.pi, 2 * np.pi, 4 * np.pi):
            vB = E2(D, 0.01, xi, 0.05, 'B', kmax=km)
            print(f"     kmax xi = {km:6.3f}:  E2/(eps^2 Q^4) = {vB / 0.01 ** 4: .5e},  b_eff/b_R = {-2 * vB / 0.01 ** 2 / bRD: .3e}")


if __name__ == "__main__":
    main()
