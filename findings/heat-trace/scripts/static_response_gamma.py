#!/usr/bin/env python3
"""Static potential sector of the oscillators on the kernel graph: is the curvature coefficient of the
LOCAL ground-state energy equal to the coefficient b_R of the integrated energy (eq. (bRgraph) of the paper)?

Setting (D = 3, population level, no sampling): nodes on the regular grid (Z/n)^3 of the unit torus, spatial
metric  hat g = (1 - 2 Psi) delta,  Psi = eps cos(2 pi q x_1);  Gaussian profile K = exp(-d^2 / (2 xi^2)) in the
distance d of hat g (to first order in eps: Euclidean length times the mean of 1 - Psi along the segment; the
symmetric difference in eps removes the even orders), normalisation W = K/(q_i q_j), S = D^{-1/2} W D^{-1/2},
L = (2/xi^2)(1 - S), massless field, H = sum_i N_i h_i with h_i the energy of node i.  Ground state:
<h_i> = (1/2) (L^{1/2})_{ii}.

Continuum prediction if the energy is the spectral function of the paper and the heat-kernel coefficient is
local:   <h_i> = omega_inf/2 + (rho_eff - b_R R(x_i)) sqrt(hat g)(x_i) / n^3,   R = 4 Laplace(Psi) to first order,
so that  d<h_i>/dPsi(x_i) * n^3 = -3 rho_eff + 4 b_loc (2 pi q)^2  with  b_loc = b_R.
The ratio b_loc/b_R is the parameter gamma of Proposition "static-test" (iv) for this node system, AFTER the
vacuum term rho_eff is set aside (it dominates and has no flat solution) and IF the background is stationary
for the total energy; neither is shown here.

Usage: static_response_gamma.py [n] [xi]      (default 64 0.05); deterministic, no random numbers.
"""
import sys
import numpy as np


def zeta(s, J=200000):
    # c_j = |binom(1/2, j)|: c_1 = 1/2, c_{j+1} = c_j (2j-1)/(2j+2);  zeta_s = sum_j c_j j^{-s}, tail ~ j^{-3/2-s}
    j = np.arange(1, J + 1, dtype=float)
    c = np.empty(J)
    c[0] = 0.5
    c[1:] = 0.5 * np.cumprod((2 * j[:-1] - 1) / (2 * j[:-1] + 2))
    tail = c[-1] * J ** 1.5 * J ** (-(0.5 + s)) / (0.5 + s)      # integral of C j^{-3/2-s} from J
    return float(np.sum(c * j ** (-s)) + tail)


def node_energy(n, xi, eps, q):
    """<h_i> as a function of the first coordinate i/n (the metric depends on x_1 only)."""
    w = int(np.ceil(7.5 * xi * n))
    assert 2 * w + 1 <= n
    off = np.arange(-w, w + 1)
    x1 = np.arange(n) / n
    m = (np.arange(n) + n // 2) % n - n // 2                 # minimal image offsets in the transverse directions
    r2 = (m[:, None] ** 2 + m[None, :] ** 2) / n ** 2
    K = np.empty((n, 2 * w + 1, n, n))
    for b, o in enumerate(off):
        d1 = o / n
        if o == 0:
            mean = np.cos(2 * np.pi * q * x1)
        else:
            a = 2 * np.pi * q
            mean = (np.sin(a * (x1 + d1)) - np.sin(a * x1)) / (a * d1)
        fac = (1.0 - eps * mean) ** 2                           # (d / Euclidean length)^2
        K[:, b] = np.exp(-(d1 ** 2 + r2)[None] * fac[:, None, None] / (2 * xi ** 2))
    idx = (np.arange(n)[:, None] + off[None, :]) % n            # neighbour index in direction 1
    qn = K.sum(axis=(1, 2, 3))
    W = K / (qn[:, None, None, None] * qn[idx][:, :, None, None])
    D = W.sum(axis=(1, 2, 3))
    S = W / np.sqrt(D[:, None, None, None] * D[idx][:, :, None, None])
    del K, W
    Sh = np.fft.rfft2(S, axes=(2, 3)).real                      # S is even in the transverse offset
    del S
    diag = np.zeros(n)
    for k2 in range(n):
        for k3 in range(n // 2 + 1):
            M = np.zeros((n, n))
            M[np.arange(n)[:, None], idx] = Sh[:, :, k2, k3]
            M = 0.5 * (M + M.T)
            ev, U = np.linalg.eigh(M)
            om = np.sqrt(np.clip((2 / xi ** 2) * (1 - ev), 0, None))
            mult = 1 if (k3 == 0 or 2 * k3 == n) else 2
            diag += mult * np.einsum('ij,j,ij->i', U, om, U)
    return 0.5 * diag / n ** 2


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    xi = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05
    Dm = 3
    rho_eff = -zeta(Dm / 2) / (np.sqrt(2) * xi * (2 * np.pi * xi ** 2) ** (Dm / 2))
    b_R = zeta(Dm / 2 - 1) * xi / (12 * np.sqrt(2) * (2 * np.pi * xi ** 2) ** (Dm / 2))
    om_inf = np.sqrt(2) / xi
    print(f"n = {n}, xi = {xi}, grid spacings per xi = {xi * n:.2f}")
    print(f"paper: zeta_3/2 = {zeta(1.5):.6f}, zeta_1/2 = {zeta(0.5):.6f}, rho_eff = {rho_eff:.6g}, b_R = {b_R:.6g}")
    e0 = node_energy(n, xi, 0.0, 1)
    print(f"flat slice: (<h_i> - omega_inf/2) n^3 = {(e0.mean() - om_inf / 2) * n ** 3:.6g}"
          f"   (prediction rho_eff = {rho_eff:.6g}); spread over nodes {np.ptp(e0) * n ** 3:.2e}")
    eps = 0.02
    x1 = np.arange(n) / n
    print(" q   (2 pi q xi)^2   c(q) n^3      -3 rho_eff(pred)   b_loc(q) = (c n^3 + 3 rho_eff)/(4 (2 pi q)^2)   b_loc/b_R"
          "   same with the measured flat value")
    rho_meas = (e0.mean() - om_inf / 2) * n ** 3
    for q in (1, 2, 3):
        de = (node_energy(n, xi, eps, q) - node_energy(n, xi, -eps, q)) / (2 * eps)
        cq = 2 * np.mean(de * np.cos(2 * np.pi * q * x1)) * n ** 3
        res = de - cq / n ** 3 * np.cos(2 * np.pi * q * x1)
        bl = (cq + 3 * rho_eff) / (4 * (2 * np.pi * q) ** 2)
        bl2 = (cq + 3 * rho_meas) / (4 * (2 * np.pi * q) ** 2)
        print(f" {q}   {(2 * np.pi * q * xi) ** 2:9.4f}   {cq:12.6g}   {-3 * rho_eff:12.6g}   {bl:12.6g}"
              f"   {bl / b_R:8.4f}   {bl2 / b_R:8.4f}   (non-cosine part of the response: {np.abs(res).max() * n ** 3:.2e})")


if __name__ == "__main__":
    main()
