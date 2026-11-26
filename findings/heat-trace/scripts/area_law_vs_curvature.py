#!/usr/bin/env python3
"""Area-law coefficient of the oscillators on the kernel graph against the curvature coefficient of their energy.

Question (Proposition "The two principles agree" of the paper): (P1) uses the induced constant of the action,
(P2) the area-law coefficient eta of the entanglement, and the proposition quotes eta = 2 pi M_ind^2 for
minimally coupled fields.  With the static Lagrangian -E = int sqrt(g)(-rho_eff + b R) and the Einstein-Hilbert
normalisation (M_ind^2/2) R this reads  eta = 4 pi b.  Here eta is computed for the model of Proposition
"Curvature term"(b) on a FLAT slice and compared with b_R of eq. (bRgraph) and with the measured coefficient
(about 1.8 b_R, scripts/sphere_energy_curvature.py and static_response_gamma.py).

Model (D = 3, flat unit torus, population level, no sampling): nodes on the grid (Z/n)^3, Gaussian profile,
S = K / sum K (the normalisation is constant on a regular grid), L = (2/xi^2)(1 - S),
H = (1/2) sum p_i^2 + (1/2) x^T (L + m^2) x.  Ground state: X = <x x> = (L+m^2)^{-1/2}/2, P = (L+m^2)^{1/2}/2.
Region A = slab {0 <= x_1 < 1/2}; its boundary consists of two planes of area 1 each.  By translation
invariance in the two transverse directions the entropy is the sum over transverse momenta of the entropies of
chains of n sites.  eta = S_A / 2 (entropy per unit area, in units of the torus).

Usage: area_law_vs_curvature.py        deterministic, no random numbers.
"""
import numpy as np


def zeta(s, J=200000):
    j = np.arange(1, J + 1, dtype=float)
    c = np.empty(J)
    c[0] = 0.5
    c[1:] = 0.5 * np.cumprod((2 * j[:-1] - 1) / (2 * j[:-1] + 2))
    tail = c[-1] * J ** 1.5 * J ** (-(0.5 + s)) / (0.5 + s)
    return float(np.sum(c * j ** (-s)) + tail)


def theta(n, xi):
    """Fourier transform of the periodised one-dimensional Gaussian on the grid, normalised to 1 at k = 0."""
    j = (np.arange(n) + n // 2) % n - n // 2
    g = np.zeros(n)
    for w in range(-3, 4):                                   # periodisation
        g += np.exp(-((j + w * n) / n) ** 2 / (2 * xi ** 2))
    th = np.fft.fft(g).real
    return th / th[0]


def entropy(nu):
    nu = np.clip(nu, 0.5 + 1e-13, None)
    return float(np.sum((nu + 0.5) * np.log(nu + 0.5) - (nu - 0.5) * np.log(nu - 0.5)))


def slab_entropy(n, xi, m):
    th = theta(n, xi)
    half = n // 2
    idx = np.arange(n)
    phase = np.exp(2j * np.pi * np.outer(idx, idx) / n)      # e^{i k x}
    S = 0.0
    S_zero = 0.0
    for k2 in range(n):
        for k3 in range(k2, n):                              # theta(k2) theta(k3) is symmetric in (k2, k3)
            mult = 1 if k3 == k2 else 2
            om = np.sqrt((2 / xi ** 2) * (1 - th * th[k2] * th[k3]) + m ** 2)
            X = (phase * (0.5 / om)[None, :]) @ phase.conj().T / n
            Pm = (phase * (0.5 * om)[None, :]) @ phase.conj().T / n
            XA = X.real[:half, :half]
            PA = Pm.real[:half, :half]
            Lc = np.linalg.cholesky(PA)
            nu = np.sqrt(np.clip(np.linalg.eigvalsh(Lc.T @ XA @ Lc), 0.25, None))
            s = entropy(nu)
            S += mult * s
            if k2 == 0 and k3 == 0:
                S_zero = s
    return S, S_zero


def chain_entropy(n, xi, m, kperp):
    """Entropy of half of a periodic chain of n sites (length 1) at transverse momentum kperp (continuum in the
    transverse directions: factor exp(-xi^2 kperp^2/2) of the Gaussian profile)."""
    th = theta(n, xi)
    half = n // 2
    idx = np.arange(n)
    phase = np.exp(2j * np.pi * np.outer(idx, idx) / n)
    om = np.sqrt((2 / xi ** 2) * (1 - th * np.exp(-xi ** 2 * kperp ** 2 / 2)) + m ** 2)
    X = (phase * (0.5 / om)[None, :]) @ phase.conj().T / n
    Pm = (phase * (0.5 * om)[None, :]) @ phase.conj().T / n
    Lc = np.linalg.cholesky(Pm.real[:half, :half])
    nu = np.sqrt(np.clip(np.linalg.eigvalsh(Lc.T @ X.real[:half, :half] @ Lc), 0.25, None))
    return entropy(nu)


def eta_continuum(n, xi, m, kmax_xi=9.0, nq=160):
    """eta = int d^2k/(2 pi)^2 s(k)/2, transverse directions infinite; s(k) = entropy of the half chain (two cuts)."""
    x, w = np.polynomial.legendre.leggauss(nq)
    k = 0.5 * (x + 1) * kmax_xi / xi
    wk = 0.5 * w * kmax_xi / xi
    s = np.array([chain_entropy(n, xi, m, kk) for kk in k])
    return float(np.sum(wk * k * s) / (2 * np.pi) / 2), s[-1]


def main():
    D = 3
    print("Part 2: transverse directions infinite (integral over the transverse momentum), chain of length 1")
    print("   xi     n   n*xi    m*xi      eta       eta xi^2    s(kmax)    4 pi b_R    eta/(4 pi b_R)")
    for xi, n, m in [(0.05, 64, 1.0), (0.05, 128, 1.0), (0.05, 128, 0.2), (0.05, 128, 0.02),
                     (0.025, 128, 0.2), (0.025, 256, 0.2), (0.0125, 256, 0.2), (0.1, 64, 0.2)]:
        b_R = zeta(D / 2 - 1) * xi / (12 * np.sqrt(2) * (2 * np.pi * xi ** 2) ** (D / 2))
        eta, slast = eta_continuum(n, xi, m)
        print(f" {xi:7.4f} {n:4d} {n * xi:6.2f} {m * xi:8.4f} {eta:10.4f} {eta * xi ** 2:10.5f} {slast:9.2e}"
              f" {4 * np.pi * b_R:11.4f} {eta / (4 * np.pi * b_R):10.4f}", flush=True)
    print()
    print("Part 1: slab on the unit torus (transverse momenta 2 pi j)")
    print("eta = S_A/2 for the slab; prediction of eta = 4 pi b with b = b_R of eq. (bRgraph)")
    print("   xi     n   n*xi    m*xi      S_A      zero-mode chain     eta        eta xi^2    4 pi b_R     eta/(4 pi b_R)")
    for xi, n, m in [(0.07, 32, 1.0), (0.07, 48, 1.0), (0.07, 64, 1.0),
                     (0.05, 48, 1.0), (0.05, 64, 1.0), (0.05, 96, 1.0),
                     (0.035, 64, 1.0), (0.035, 96, 1.0),
                     (0.05, 64, 0.2), (0.05, 64, 5.0)]:
        b_R = zeta(D / 2 - 1) * xi / (12 * np.sqrt(2) * (2 * np.pi * xi ** 2) ** (D / 2))
        S, S0 = slab_entropy(n, xi, m)
        eta = S / 2
        print(f" {xi:6.3f} {n:4d} {n * xi:6.2f} {m * xi:7.3f} {S:10.4f} {S0:12.4f} {eta:14.4f} {eta * xi ** 2:10.5f}"
              f" {4 * np.pi * b_R:11.4f} {eta / (4 * np.pi * b_R):12.4f}", flush=True)


if __name__ == "__main__":
    main()
