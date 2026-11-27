#!/usr/bin/env python3
"""Direct check of lambda = -1/2 for the oscillators on the kernel graph (Proposition "Oscillators on the
kernel graph", eq. (graphlong)), in D = 3, without the population-level formula.

Nodes on the regular grid (Z/n)^3 of the unit torus with the constant metric h(eps) = (1 + eps K)^2 (a
homogeneous flow with gradient K acting on the mutual distances; the coordinates of the nodes are fixed).
Gaussian profile K_ij = exp(-d_h^2/(2 xi^2)), S = K / sum K (constant normalisation on a regular grid),
A = (2/xi^2)(1 - S) + m^2.  All A(eps) are circulant, so the eigenvectors do not change and the adiabatic kinetic
term (eq. (adiab)) is  L_K = sum_k (dA_k/d eps)^2 / (64 omega_k^5).

With L_K = a (K_ab K^ab - lambda K^2):  shear K = diag(1,-1,0) gives 2a, dilation K = identity gives
a (3 - 9 lambda), hence  lambda = (3 - 2 L_K(dilation)/L_K(shear)) / 9;  a third flow K = diag(1,0,0) gives
a (1 - lambda) and serves as a consistency check.  Deterministic, no random numbers.

Usage: graph_lambda_check.py
"""
import numpy as np


def eig_S(n, xi, h):
    """Eigenvalues of S on the grid for the constant metric h = diag(h1, h2, h3) (h_a = (1 + eps K_a)^2)."""
    j = (np.arange(n) + n // 2) % n - n // 2
    th = []
    for a in range(3):
        g = np.zeros(n)
        for w in range(-3, 4):
            g += np.exp(-h[a] * ((j + w * n) / n) ** 2 / (2 * xi ** 2))
        t = np.fft.fft(g).real
        th.append(t / t[0])
    return th[0][:, None, None] * th[1][None, :, None] * th[2][None, None, :]


def LK(n, xi, m, Kdiag, eps=1e-4):
    Kd = np.array(Kdiag, dtype=float)
    sp = eig_S(n, xi, (1 + eps * Kd) ** 2)
    sm = eig_S(n, xi, (1 - eps * Kd) ** 2)
    s0 = eig_S(n, xi, np.ones(3))
    dA = (2 / xi ** 2) * (-(sp - sm) / (2 * eps))
    om = np.sqrt((2 / xi ** 2) * (1 - s0) + m ** 2)
    return float(np.sum(dA ** 2 / (64 * om ** 5)))          # total over the unit volume


def main():
    print("   xi     n   n*xi    m*xi    L_K(shear)   L_K(dilation)   L_K(one axis)    lambda    lambda (from one axis)")
    for xi, n, m in [(0.07, 32, 1.0), (0.07, 48, 1.0), (0.07, 64, 1.0), (0.05, 64, 1.0), (0.05, 96, 1.0),
                     (0.05, 96, 0.1), (0.035, 96, 1.0), (0.1, 48, 1.0)]:
        Ls = LK(n, xi, m, (1, -1, 0))
        Ld = LK(n, xi, m, (1, 1, 1))
        L1 = LK(n, xi, m, (1, 0, 0))
        a = Ls / 2
        lam = (3 - 2 * Ld / Ls) / 9
        lam1 = 1 - L1 / a
        print(f" {xi:6.3f} {n:4d} {n * xi:6.2f} {m * xi:7.3f} {Ls:12.6g} {Ld:14.6g} {L1:14.6g} {lam:10.5f} {lam1:12.5f}",
              flush=True)


if __name__ == "__main__":
    main()
