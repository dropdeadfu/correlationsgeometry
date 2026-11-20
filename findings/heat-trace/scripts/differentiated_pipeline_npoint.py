"""Draft B2 (paper/drafts/time_and_dynamics.tex): the N-point version of the differentiated pipeline.

Independent uniform points on the flat torus [0,1)^2 with the family of flat metrics
  h_tau = (1 + a tau)^2 dx^2 + dy^2,     d/dtau h = 2 K,  K = diag(a, 0) at tau = 0,
Gaussian profile exp(-d^2 / (2 xi^2)) (c_h = 1), graph operator of the paper (two-sided normalisation,
self-loops included):  L_N f (i) = (2 / xi^2) (f_i - sum_j P_ij f_j).

Compared, for f = sin(2 pi x): the tau-derivative of L_N f at tau = 0 (central difference, same sample)
(a) with the derivative of the population operator, which on a flat torus with the Gaussian profile is
(1 - exp(-sig lam_tau))/sig on the eigenfunction f, sig = xi^2/2, lam_tau = 4 pi^2/(1 + a tau)^2, and
(b) with the continuum value -d/dtau (Laplace_{h_tau} f) = 2 a f_xx. Printed: root mean square and
maximum over the sample points, the relative bias of the population value, and delta'/xi with
delta' = sqrt(log N / (N xi^d)).

Caveat: the script uses the nearest image only, so the comparison value (a) is the population value of the
periodised kernel, not of the kernel used; the difference is negligible for xi <= 0.10 and visible for
xi >= 0.14 (it explains the constant 0.066 at xi = 0.20).

Single samples with a fixed seed; the table shows the size of the errors, it is not a proof of a rate.
Usage: python differentiated_pipeline_npoint.py
"""
import numpy as np

A_DEF = 1.0
DTAU = 1e-3


def graph_laplacian(pts, xi, tau, f):
    dx = pts[:, 0][:, None] - pts[:, 0][None, :]
    dy = pts[:, 1][:, None] - pts[:, 1][None, :]
    dx -= np.round(dx)
    dy -= np.round(dy)
    d2 = ((1.0 + A_DEF * tau) * dx) ** 2 + dy ** 2
    k = np.exp(-d2 / (2.0 * xi ** 2))
    q = k.mean(axis=1)
    w = k / np.outer(q, q)
    p = w / w.sum(axis=1, keepdims=True)
    return (2.0 / xi ** 2) * (f - p @ f)


def run(n, xi, seed):
    rng = np.random.default_rng(seed)
    pts = rng.random((n, 2))
    x = pts[:, 0]
    f = np.sin(2 * np.pi * x)                        # eigenfunction of Laplace_{h_tau} for every tau
    lam = (2 * np.pi) ** 2                           # -Laplace f = lam f at tau = 0
    dlam = -2.0 * A_DEF * lam                        # d/dtau of lam / (1 + a tau)^2 at tau = 0
    sig = xi ** 2 / 2.0
    dl = (graph_laplacian(pts, xi, DTAU, f) - graph_laplacian(pts, xi, -DTAU, f)) / (2 * DTAU)
    cont = dlam * f                                  # continuum: -d/dtau Laplace_{h_tau} f = 2 a f_xx
    pop = np.exp(-sig * lam) * dlam * f              # population operator (1 - exp(-sig lam_tau))/sig
    scale = np.sqrt(np.mean(cont ** 2))
    e_pop = dl - pop
    e_cont = dl - cont
    dprime = np.sqrt(np.log(n) / (n * xi ** 2))
    return (np.sqrt(np.mean(e_pop ** 2)) / scale, np.abs(e_pop).max() / scale,
            np.sqrt(np.mean(e_cont ** 2)) / scale, np.abs(e_cont).max() / scale,
            1.0 - np.exp(-sig * lam), dprime / xi)


def main():
    print("flat torus, d = 2, h_tau = (1 + tau)^2 dx^2 + dy^2, f = sin(2 pi x)")
    print("d/dtau (L_N f) at tau = 0; errors relative to the root mean square of the continuum value 2 a f_xx")
    print("    N    xi   against population: rms    max   | against continuum: rms    max   | bias 1-exp(-sig lam) | delta'/xi")
    for xi in (0.20, 0.14, 0.10, 0.07):
        for n in (500, 1000, 2000, 3000):
            r = run(n, xi, seed=11)
            print("%5d  %4.2f                  %6.3f  %6.3f |                 %6.3f  %6.3f |        %6.3f        |  %6.2f" % ((n, xi) + r))


if __name__ == "__main__":
    main()
