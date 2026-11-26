#!/usr/bin/env python3
"""Modular Hamiltonian of a half space for the oscillators on the kernel graph: is it a boost?

Setting as in area_law_vs_curvature.py (flat slice, D = 3, nodes on a regular grid, transverse directions in the
continuum): for transverse momentum k the problem is a periodic chain of n sites (length 1) with
omega^2 = (2/xi^2)(1 - theta(k_1) exp(-xi^2 k^2/2)) + m^2.  Region A = sites 0..n/2-1 (cuts at x = 0 and x = 1/2).
The reduced state is Gaussian with covariances X_A, P_A; its modular Hamiltonian is
  K = (1/2) p^T N p + (1/2) x^T B x,   N = P^{-1/2} U (eps nu) U^T P^{-1/2},
where P^{1/2} X P^{1/2} = U nu^2 U^T and eps = log((nu + 1/2)/(nu - 1/2)).
For a Lorentz-invariant vacuum (Bisognano-Wichmann) K = 2 pi * (boost generator), i.e. the kinetic weight of the
node at distance x from the cut is N_ii = 2 pi x (field speed 1, which is the speed of the long waves here).
The script prints N_ii / (2 pi x_i), x_i = (i + 1/2)/n.  High precision arithmetic (mpmath) is needed because
the symplectic eigenvalues approach 1/2 exponentially.  Deterministic.

Usage: modular_boost_check.py [n] [xi]     (default 128 0.03)
"""
import sys
import mpmath as mp

mp.mp.dps = 90


def theta(n, xi):
    out = []
    g = []
    for j in range(n):
        jj = j if j <= n // 2 else j - n
        s = mp.mpf(0)
        for w in range(-3, 4):
            s += mp.exp(-((mp.mpf(jj) + w * n) / n) ** 2 / (2 * xi ** 2))
        g.append(s)
    for k in range(n):
        out.append(sum(g[j] * mp.cos(2 * mp.pi * k * j / n) for j in range(n)))
    return [t / out[0] for t in out]


def modular_N(n, xi, m, kperp, th):
    half = n // 2
    om = [mp.sqrt((2 / xi ** 2) * (1 - th[k] * mp.exp(-xi ** 2 * kperp ** 2 / 2)) + m ** 2) for k in range(n)]
    cx = [sum(mp.cos(2 * mp.pi * k * d / n) / (2 * om[k]) for k in range(n)) / n for d in range(half)]
    cp = [sum(mp.cos(2 * mp.pi * k * d / n) * om[k] / 2 for k in range(n)) / n for d in range(half)]
    X = mp.matrix(half, half)
    P = mp.matrix(half, half)
    for i in range(half):
        for j in range(half):
            X[i, j] = cx[abs(i - j)]
            P[i, j] = cp[abs(i - j)]
    ep, Up = mp.eigsy(P)
    Ph = Up * mp.diag([mp.sqrt(e) for e in ep]) * Up.T
    Pmh = Up * mp.diag([1 / mp.sqrt(e) for e in ep]) * Up.T
    nu2, U = mp.eigsy(Ph * X * Ph)
    w = []
    for v in nu2:
        nu = mp.sqrt(v)
        w.append(mp.log((nu + mp.mpf(1) / 2) / (nu - mp.mpf(1) / 2)) * nu)
    Nm = Pmh * U * mp.diag(w) * U.T * Pmh
    return [Nm[i, i] for i in range(half)], min(mp.sqrt(v) - mp.mpf(1) / 2 for v in nu2)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 128
    xi = mp.mpf(sys.argv[2]) if len(sys.argv) > 2 else mp.mpf('0.03')
    th = theta(n, xi)
    half = n // 2
    sel = sorted(set([0, 1, 2, 3, 5, 8, 12, 16, 24, half // 2 - 1]))
    sel = [i for i in sel if i < half // 2]
    print(f"n = {n}, xi = {mp.nstr(xi, 4)}, nodes per xi = {mp.nstr(n * xi, 4)}; N_ii/(2 pi x_i) at x_i = (i+1/2)/n")
    print("   kperp     m     min(nu-1/2)   " + "  ".join(f"x/xi={mp.nstr((i + mp.mpf(1) / 2) / n / xi, 3):>5}" for i in sel))
    for kperp, m in [(0, 1), (0, 5), (10, 0), (30, 0), (60, 0)]:
        Nd, gap = modular_N(n, xi, mp.mpf(m), mp.mpf(kperp), th)
        vals = [Nd[i] / (2 * mp.pi * (i + mp.mpf(1) / 2) / n) for i in sel]
        print(f" {kperp:7.1f} {m:5.1f}   {mp.nstr(gap, 3):>10}   " + "  ".join(f"{mp.nstr(v, 5):>10}" for v in vals), flush=True)


if __name__ == "__main__":
    main()
