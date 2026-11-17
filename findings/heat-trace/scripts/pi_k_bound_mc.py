"""Monte Carlo test of Lemma "Bound for the polynomial statistic": E|Pi_k| <= C (M/N) k m_k.

Flat 2-torus, Gaussian kernel with self-loops. Pi_k is computed as in second_stage_reduction.py. For each
configuration the script prints, for k = 1, 2, 4, 8, 16, 32, the mean of Pi_k, the mean of |Pi_k| and the
standard deviation, each divided by (M/N) k m_k. If the lemma holds, the column E|Pi_k| stays bounded in
k, N and xi; growth in any of them would contradict it. Fixed seed; the number of samples is small.
"""
import gc

import numpy as np

KS = (1, 2, 4, 8, 16, 32)


def theta(dx, var):
    return sum(np.exp(-(dx + a) ** 2 / (2 * var)) for a in range(-6, 7)) / np.sqrt(2 * np.pi * var)


def pi_k(X, xi):
    N = len(X)
    dx = X[:, None, 0] - X[None, :, 0]
    dy = X[:, None, 1] - X[None, :, 1]
    pk = lambda s: theta(dx, s * xi**2) * theta(dy, s * xi**2)
    K = pk(1)
    eps = K.sum(1) / N - 1
    Pt = K / N
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
        del hh
    return [Pi[k] for k in KS]


def heat0(s, xi):
    return float(theta(np.zeros(1), s * xi**2)[0]) ** 2


rng = np.random.default_rng(11)
for N, xi, reps in ((300, 0.1, 40), (600, 0.1, 30), (1200, 0.1, 12), (600, 0.07, 30), (1200, 0.07, 12), (1200, 0.05, 12)):
    M = heat0(1, xi)
    vals = np.array([pi_k(rng.random((N, 2)), xi) for _ in range(reps)])
    gc.collect()
    print(f"N={N} xi={xi} M/N={M/N:.4f} samples={reps}", flush=True)
    for j, k in enumerate(KS):
        u = M / N * k * heat0(k, xi)
        v = vals[:, j]
        print(f"   k={k:2d}: E Pi_k {v.mean()/u:+.3f}   E|Pi_k| {np.abs(v).mean()/u:.3f}   sd {v.std()/u:.3f}", flush=True)
