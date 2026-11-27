#!/usr/bin/env python3
"""Does the local ground-state energy of the oscillators on the kernel graph depend on the node density?

Background.  The node energy is  <h_i> = (omega_inf/2)(1 - sum_j c_j (S^j)_ii),  a sum of return probabilities.
If the energy per volume is  u = rho_eff - b R + c Laplace(ln n)  with n the node density, the last term
integrates to zero, so it cannot be seen in the total energy, but it shifts the LOCAL curvature coefficient:
for the metric (1 - 2 Psi) delta with nodes fixed in the coordinates (scripts/static_response_gamma.py) one has
ln n = 3 Psi + const and R = 4 Laplace(Psi), hence  b_loc = b_int - 3c/4.  The parameter gamma of that script is
1 at long wavelengths if and only if c = 0.

Here c is measured directly: FLAT metric, D = 3, unit torus, nodes at  x_1(i) = i/n + (eps/a) sin(a i/n),
a = 2 pi q, regular in the two transverse directions, so that the node density is n^3 / (1 + eps cos(a i/n)).
Prediction:  (<h_i> - omega_inf/2) n^3 = rho_eff + eps cos(a x_1) (rho_eff + c a^2) + O(eps^2).
Deterministic; first order in eps by a symmetric difference.

Usage: density_response_flat.py [n] [xi]     (default 64 0.05)
"""
import sys
import numpy as np


def zeta(s, J=200000):
    j = np.arange(1, J + 1, dtype=float)
    c = np.empty(J)
    c[0] = 0.5
    c[1:] = 0.5 * np.cumprod((2 * j[:-1] - 1) / (2 * j[:-1] + 2))
    tail = c[-1] * J ** 1.5 * J ** (-(0.5 + s)) / (0.5 + s)
    return float(np.sum(c * j ** (-s)) + tail)


def node_energy(n, xi, eps, q):
    a = 2 * np.pi * q
    lab = np.arange(n) / n
    x1 = lab + (eps / a) * np.sin(a * lab)                    # node positions in direction 1
    w = int(np.ceil(7.5 * xi * n / (1 - abs(eps)))) + 1
    assert 2 * w + 1 <= n
    off = np.arange(-w, w + 1)
    idx = (np.arange(n)[:, None] + off[None, :]) % n
    wrap = ((np.arange(n)[:, None] + off[None, :]) - idx) / n  # integer shift of the periodic image
    d1 = x1[idx] + wrap - x1[:, None]                          # (n, 2w+1)
    m = (np.arange(n) + n // 2) % n - n // 2
    r2 = (m[:, None] ** 2 + m[None, :] ** 2) / n ** 2
    K = np.exp(-(d1[:, :, None, None] ** 2 + r2[None, None]) / (2 * xi ** 2))
    qn = K.sum(axis=(1, 2, 3))
    W = K / (qn[:, None, None, None] * qn[idx][:, :, None, None])
    D = W.sum(axis=(1, 2, 3))
    S = W / np.sqrt(D[:, None, None, None] * D[idx][:, :, None, None])
    del K, W
    Sh = np.fft.rfft2(S, axes=(2, 3)).real
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
    return 0.5 * diag / n ** 2, x1


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    xi = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05
    Dm = 3
    rho_eff = -zeta(Dm / 2) / (np.sqrt(2) * xi * (2 * np.pi * xi ** 2) ** (Dm / 2))
    b_R = zeta(Dm / 2 - 1) * xi / (12 * np.sqrt(2) * (2 * np.pi * xi ** 2) ** (Dm / 2))
    om_inf = np.sqrt(2) / xi
    e0, _ = node_energy(n, xi, 0.0, 1)
    rho_meas = (e0.mean() - om_inf / 2) * n ** 3
    print(f"n = {n}, xi = {xi}, n*xi = {n * xi:.2f}; rho_eff = {rho_eff:.6g} (measured flat {rho_meas:.6g}), b_R = {b_R:.6g}")
    print(" q   (2 pi q xi)^2   coefficient of eps cos    rho (measured)    c(q)       c/b_R     shift of b_loc/b_R = -3c/(4 b_R)"
          "   non-cosine part")
    eps = 0.02
    for q in (1, 2, 3):
        ep, xp = node_energy(n, xi, eps, q)
        em, xm = node_energy(n, xi, -eps, q)
        lab = np.arange(n) / n
        de = (ep - em) / (2 * eps)                              # at fixed node label; positions differ at O(eps)
        cq = 2 * np.mean(de * np.cos(2 * np.pi * q * lab)) * n ** 3
        res = de * n ** 3 - cq * np.cos(2 * np.pi * q * lab)
        c = (cq - rho_meas) / (2 * np.pi * q) ** 2
        print(f" {q}   {(2 * np.pi * q * xi) ** 2:9.4f}   {cq:16.6g}   {rho_meas:14.6g}   {c:10.5g}   {c / b_R:8.4f}"
              f"   {-0.75 * c / b_R:10.4f}                 {np.abs(res).max():.2e}", flush=True)


if __name__ == "__main__":
    main()
