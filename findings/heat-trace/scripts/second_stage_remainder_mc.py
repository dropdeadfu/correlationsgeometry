"""Monte Carlo for the remainder of Proposition "Reduction of the trace to a polynomial statistic".

Flat 2-torus, Gaussian kernel with self-loops, xi = 0.1. For N = 400, 800, 1600 the script prints mean and
standard deviation over independent samples of the remainder R_k = Tr P^(k+1) - m_(k+1) - Pi_k, divided by
(M/N) m_(k+1). Question under test: is the remainder a bias of order M/N with fluctuations of smaller
order (then sd/((M/N) m) falls with N), or does it fluctuate at the order delta'^2 k of the proven bound?
Fixed seed; few samples.
"""
import gc

import numpy as np

KS = (1, 2, 4, 8, 16)


def theta(dx, var):
    return sum(np.exp(-(dx + a) ** 2 / (2 * var)) for a in range(-6, 7)) / np.sqrt(2 * np.pi * var)


def remainder(X, xi):
    N = len(X)
    dx = X[:, None, 0] - X[None, :, 0]
    dy = X[:, None, 1] - X[None, :, 1]
    pk = lambda s: theta(dx, s * xi**2) * theta(dy, s * xi**2)
    K = pk(1)
    q = K.sum(1) / N
    eps = q - 1
    Pt = K / N
    W = K / np.outer(q, q)
    P = W / W.sum(1)[:, None]
    th1 = -eps[None, :] - eps[:, None] + (Pt @ eps)[:, None]
    A = Pt * (1 - eps)[None, :]
    rowA = A.sum(1)
    Pi = {k: np.einsum("ib,bi,bi->", pk(k), K, th1) / N**2 for k in KS}
    for m in range(1, max(KS) + 1):
        hh = A @ pk(m) - rowA[:, None] * pk(m + 1)
        for k in KS:
            if k > m:
                Pi[k] += np.einsum("ib,bi->", pk(k - m), hh) / N**2
            elif k == m:
                Pi[k] += np.trace(hh) / N
    out, Pk = [], np.eye(N)
    for k in range(1, max(KS) + 1):
        Pk = Pk @ P
        if k in KS:
            mk1 = pk(k + 1)[0, 0]
            out.append((np.einsum("ab,ba->", Pk, P) - mk1 - Pi[k]) / mk1)
    return out


rng = np.random.default_rng(5)
xi = 0.1
M = float(theta(np.zeros(1), xi**2)[0]) ** 2
for N, reps in ((400, 40), (800, 24), (1600, 10)):
    v = np.array([remainder(rng.random((N, 2)), xi) for _ in range(reps)]) / (M / N)
    gc.collect()
    print(f"N={N} xi={xi} M/N={M/N:.4f} sqrt(M)/N={np.sqrt(M)/N:.5f} samples={reps}", flush=True)
    for j, k in enumerate(KS):
        print(f"   k={k:2d}: mean R/((M/N) m) = {v[:, j].mean():+.3f} (se {v[:, j].std()/np.sqrt(reps):.3f})   sd/((M/N) m) = {v[:, j].std():.3f}   sd*N/(sqrt(M) m) = {v[:, j].std()*np.sqrt(M):.3f}", flush=True)
