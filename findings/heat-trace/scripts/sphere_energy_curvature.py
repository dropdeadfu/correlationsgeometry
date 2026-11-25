#!/usr/bin/env python3
"""Curvature term of the ground-state energy of the oscillators on the kernel graph, tested on the unit
sphere S^2 at the population level (uniform density, no sampling).

Population walk: eigenvalue on the degree-l harmonics  s_l = E[P_l(cos theta)]  for theta with density
proportional to exp(-theta^2/(2 xi^2)) sin(theta) on [0, pi] (Gaussian profile in the geodesic distance).
omega_l^2 = (2/xi^2)(1 - s_l), massless field.  Energy above the node term:
    E - N omega_inf/2 = sum_l (2l+1) (omega_l - omega_inf)/2 ,   omega_inf = sqrt(2)/xi .
Formula (graphE)/(bRgraph) of the paper for D = 2 predicts  rho_eff * 4 pi - b_R * 8 pi + o(1)  with
    rho_eff = -zeta_1/(sqrt(2) xi 2 pi xi^2),  b_R = zeta_0 xi/(12 sqrt(2) 2 pi xi^2),  zeta_0 = 1,
that is, a constant term  -8 pi b_R = -1/(3 sqrt(2) xi).  The script prints the measured constant term times xi.
Deterministic (Gauss-Legendre quadrature).
"""
import numpy as np


def zeta(s, J=400000):
    j = np.arange(1, J + 1, dtype=float)
    c = np.empty(J); c[0] = 0.5
    c[1:] = 0.5 * np.cumprod((2 * j[:-1] - 1) / (2 * j[:-1] + 2))
    return float(np.sum(c * j ** (-s)) + c[-1] * J ** 1.5 * J ** (-(0.5 + s)) / (0.5 + s))


def s_l(xi, lmax, nq=6000):
    t, w = np.polynomial.legendre.leggauss(nq)
    th = 0.5 * np.pi * (t + 1); w = 0.5 * np.pi * w
    dens = np.exp(-th ** 2 / (2 * xi ** 2)) * np.sin(th) * w
    dens /= dens.sum()
    x = np.cos(th)
    s = np.empty(lmax + 1)
    p0 = np.ones_like(x); p1 = x.copy()
    s[0] = 1.0; s[1] = np.dot(dens, p1)
    for l in range(1, lmax):
        p0, p1 = p1, ((2 * l + 1) * x * p1 - l * p0) / (l + 1)
        s[l + 1] = np.dot(dens, p1)
    return s


z1 = zeta(1.0)
print(f"zeta_1 = {z1:.6f}; prediction for (constant term) * xi: {-1 / (3 * np.sqrt(2)):.5f}")
print("  xi     sum_l (2l+1)(omega_l-omega_inf)/2    4 pi rho_eff     constant term     (constant term)*xi   ratio to prediction")
for xi in (0.2, 0.1, 0.05, 0.025):
    lmax = int(60 / xi)
    s = s_l(xi, lmax)
    l = np.arange(lmax + 1)
    om = np.sqrt(np.clip((2 / xi ** 2) * (1 - s), 0, None))
    E = np.sum((2 * l + 1) * (om - np.sqrt(2) / xi) / 2)
    rho = -z1 / (np.sqrt(2) * xi * 2 * np.pi * xi ** 2)
    c = E - 4 * np.pi * rho
    print(f"  {xi:5.3f}  {E:16.6f}  {4 * np.pi * rho:16.6f}  {c:12.6f}  {c * xi:10.5f}  {c * xi / (-1 / (3 * np.sqrt(2))):8.4f}"
          f"   (last |s_l| = {abs(s[-1]):.1e})")

# ---- the same on the unit sphere S^3 (D = 3): zonal eigenvalue s_l = E[ sin((l+1) theta) / ((l+1) sin theta) ]
# for the density proportional to exp(-theta^2/(2 xi^2)) sin^2(theta); multiplicity (l+1)^2, Vol = 2 pi^2, R = 6.
# Formula (bRgraph) for D = 3 predicts the term  -b_R * 12 pi^2  with  b_R = zeta_{1/2} xi/(12 sqrt(2) (2 pi xi^2)^{3/2}).
z32, z12 = zeta(1.5), zeta(0.5)
print()
print("S^3:  xi    E - N omega_inf/2      2 pi^2 rho_eff      difference      -12 pi^2 b_R (formula)    ratio")
t, w = np.polynomial.legendre.leggauss(20000)
th = 0.5 * np.pi * (t + 1); w = 0.5 * np.pi * w
for xi in (0.2, 0.1, 0.05, 0.025):
    lmax = int(60 / xi)
    g = np.exp(-th ** 2 / (2 * xi ** 2)) * np.sin(th) * w
    norm = np.dot(g, np.sin(th))
    l1 = np.arange(1, lmax + 2, dtype=float)
    s = np.array([np.dot(g, np.sin(k * th)) for k in l1]) / (l1 * norm)
    om = np.sqrt(np.clip((2 / xi ** 2) * (1 - s), 0, None))
    E = np.sum(l1 ** 2 * (om - np.sqrt(2) / xi) / 2)
    rho = -z32 / (np.sqrt(2) * xi * (2 * np.pi * xi ** 2) ** 1.5)
    bR = z12 * xi / (12 * np.sqrt(2) * (2 * np.pi * xi ** 2) ** 1.5)
    c = E - 2 * np.pi ** 2 * rho
    print(f"      {xi:5.3f}  {E:16.5f}  {2 * np.pi ** 2 * rho:16.5f}  {c:12.5f}  {-12 * np.pi ** 2 * bR:12.5f}  {c / (-12 * np.pi ** 2 * bR):8.4f}")
