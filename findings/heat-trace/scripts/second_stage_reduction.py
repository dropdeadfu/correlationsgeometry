"""Check of Proposition "Reduction of the trace to a polynomial statistic" on single samples.

Flat 2-torus, Gaussian kernel with self-loops. For k = 1, 2, 4, 8, 16 the script prints the error
Tr P^(k+1) - m_(k+1), the polynomial statistic Pi_k and the remainder, relative to m_(k+1), and the
remainder divided by delta'^2 k m_(k+1) (the bound of the proposition up to its constant) and by
(M/N) m_(k+1). delta'^2 = M log N / N. One sample per configuration, fixed seed.
"""
import gc

import numpy as np


def theta(dx, var):
    return sum(np.exp(-(dx + a) ** 2 / (2 * var)) for a in range(-6, 7)) / np.sqrt(2 * np.pi * var)


def run(N, xi, ks=(1, 2, 4, 8, 16), seed=3):
    rng = np.random.default_rng(seed)
    X = rng.random((N, 2))
    dx = X[:, None, 0] - X[None, :, 0]
    dy = X[:, None, 1] - X[None, :, 1]
    pk = lambda s: theta(dx, s * xi**2) * theta(dy, s * xi**2)
    K = pk(1)
    M = K[0, 0]
    q = K.sum(1) / N
    eps = q - 1
    Pt = K / N
    W = K / np.outer(q, q)
    P = W / W.sum(1)[:, None]
    del W
    dl2 = M * np.log(N) / N
    print(f"N={N} xi={xi} M/N={M/N:.4f} delta'^2={dl2:.4f} delta={np.abs(eps).max():.3f}", flush=True)
    th1 = -eps[None, :] - eps[:, None] + (Pt @ eps)[:, None]      # theta^1[b, i]
    A = Pt * (1 - eps)[None, :]
    rowA = A.sum(1)
    Pi = {k: np.einsum("ib,bi,bi->", pk(k), K, th1) / N**2 for k in ks}
    del th1
    for m in range(1, max(ks) + 1):
        hh = A @ pk(m) - rowA[:, None] * pk(m + 1)                # hat h_m[b, i]
        for k in ks:
            if k > m:
                Pi[k] += np.einsum("ib,bi->", pk(k - m), hh) / N**2
            elif k == m:
                Pi[k] += np.trace(hh) / N
        del hh
        gc.collect()
    Pk = np.eye(N)
    for k in range(1, max(ks) + 1):
        Pk = Pk @ P
        if k not in ks:
            continue
        mk1 = pk(k + 1)[0, 0]
        err = np.einsum("ab,ba->", Pk, P) - mk1
        R = err - Pi[k]
        print(f"   k={k:2d}: error {err/mk1:+.4f}  Pi_k {Pi[k]/mk1:+.4f}  remainder {R/mk1:+.4f}  | remainder/(delta'^2 k m) = {R/(dl2*k*mk1):+.4f}  remainder/((M/N) m) = {R/(M/N*mk1):+.3f}", flush=True)


for N, xi in ((1500, 0.05), (3000, 0.05), (1500, 0.08)):
    run(N, xi)
    gc.collect()
