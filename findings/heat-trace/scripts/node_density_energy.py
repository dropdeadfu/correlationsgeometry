#!/usr/bin/env python3
"""Ground-state energy per node of the oscillators on the kernel graph as a function of the node density.

Flat unit three-torus, nodes on the regular grid (Z/n)^3, Gaussian profile with scale xi, massless field.
M = (2 pi)^{3/2} (n xi)^3 is the number of nodes per kernel volume (2 pi xi^2)^{3/2}.  In the dense limit
eq. (bRgraph) gives  E/N = (omega_inf/2)(1 - zeta_{3/2}/M),  omega_inf = sqrt(2)/xi.
Question: does the energy per node have a minimum at a finite density (an equilibrium density, at which the
vacuum term would exert no pressure)?  Answer of this computation: no, it increases monotonically with M.
Deterministic.  Usage: node_density_energy.py
"""
import numpy as np
from graph_lambda_check import eig_S


def zeta(s, J=200000):
    j = np.arange(1, J + 1, dtype=float)
    c = np.empty(J)
    c[0] = 0.5
    c[1:] = 0.5 * np.cumprod((2 * j[:-1] - 1) / (2 * j[:-1] + 2))
    tail = c[-1] * J ** 1.5 * J ** (-(0.5 + s)) / (0.5 + s)
    return float(np.sum(c * j ** (-s)) + tail)


def main():
    n = 48
    z = zeta(1.5)
    print(" n*xi        M      E/N / (omega_inf/2)     1 - zeta_{3/2}/M")
    for nx in (0.15, 0.2, 0.3, 0.4, 0.5, 0.6, 0.8, 1.0, 1.5, 2.0, 3.0):
        xi = nx / n
        s = eig_S(n, xi, np.ones(3))
        om = np.sqrt(np.clip((2 / xi ** 2) * (1 - s), 0, None))
        e = om.mean() / 2 / (1 / (np.sqrt(2) * xi))
        M = (2 * np.pi) ** 1.5 * nx ** 3
        print(f"{nx:6.2f} {M:9.3f} {e:18.6f} {1 - z / M:22.6f}")


if __name__ == "__main__":
    main()
