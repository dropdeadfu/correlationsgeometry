"""Entrywise form of the reduction (Remark "On the second stage", item (iii)), on single samples.

Flat 2-torus, Gaussian kernel with self-loops. Printed for k = 1, 2, 4, 8, 16: the maximum over all
entries (a, i) of |N P^(k+1) - p_(k+1)| (first-order error, Theorem "kernel") and of
|N P^(k+1) - p_(k+1) - Pi_k(a, i)| (after subtracting the explicit first-order term), both divided by
m_(k+1), and the latter divided by delta'^2 k m_(k+1). One sample per configuration, fixed seed.
"""
import numpy as np

KS = (1, 2, 4, 8, 16)


def theta(dx, var):
    return sum(np.exp(-(dx + a) ** 2 / (2 * var)) for a in range(-6, 7)) / np.sqrt(2 * np.pi * var)


def run(N, xi, seed=3):
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
    th1 = -eps[None, :] - eps[:, None] + (Pt @ eps)[:, None]          # theta^1[b, i]
    A = Pt * (1 - eps)[None, :]
    rowA = A.sum(1)
    Pi = {k: pk(k) @ (K * th1) / N for k in KS}                       # Pi_k[a, i]
    for m in range(1, max(KS) + 1):
        hh = A @ pk(m) - rowA[:, None] * pk(m + 1)                    # hat h_m[b, i]
        for k in KS:
            if k > m:
                Pi[k] += pk(k - m) @ hh / N
            elif k == m:
                Pi[k] += hh
    dl2 = M * np.log(N) / N
    print(f"N={N} xi={xi} M/N={M/N:.4f} delta'^2={dl2:.4f} delta={np.abs(eps).max():.3f}", flush=True)
    Pk = np.eye(N)
    for k in range(1, max(KS) + 1):
        Pk = Pk @ P
        if k in KS:
            p1 = pk(k + 1)
            E = N * (Pk @ P) - p1
            mk1 = p1[0, 0]
            print(f"   k={k:2d}: max|error|/m = {np.abs(E).max()/mk1:.4f}   max|error - Pi_k|/m = {np.abs(E - Pi[k]).max()/mk1:.4f}"
                  f"   /(delta'^2 k m) = {np.abs(E - Pi[k]).max()/(dl2*k*mk1):.4f}", flush=True)


run(1000, 0.1)
run(1000, 0.07)
