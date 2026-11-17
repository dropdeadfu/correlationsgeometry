"""Kernel of the sampled walk against the heat kernel in the supremum norm, flat 2-torus, Gaussian kernel.

For one sample the script prints, for k = 1, 2, 4, ..., the relative error max_{a,i} |N (P^k)_{ai} -
p_k(x_a - x_i)| / m_k of Theorem "The kernel of the sampled walk, uniformly in the number of steps", and,
for m = 1, 2, 4, ..., the size of the consistency defect h_m of Lemma "Consistency of the normalised walk"
relative to delta' m^{-1/2} p_{6m}, where delta' = sqrt(M log N / N). One sample per N, fixed seed; not
evidence for a rate.
"""
import numpy as np


def theta(dx, var):  # periodised one-dimensional Gaussian density of variance var
    return sum(np.exp(-(dx + a) ** 2 / (2 * var)) for a in range(-6, 7)) / np.sqrt(2 * np.pi * var)


for N in (2000, 4000):
    xi = 0.05
    rng = np.random.default_rng(3)
    X = rng.random((N, 2))
    dx = X[:, None, 0] - X[None, :, 0]
    dy = X[:, None, 1] - X[None, :, 1]
    pk = lambda s: theta(dx, s * xi**2) * theta(dy, s * xi**2)
    K = pk(1)
    M = K[0, 0]
    q = K.sum(1) / N
    W = K / np.outer(q, q)
    P = W / W.sum(1)[:, None]
    dl = np.sqrt(M * np.log(N) / N)
    print(f"N={N} xi={xi} M/N={M/N:.4f} delta'={dl:.4f} delta=max|eps|={np.abs(q - 1).max():.3f}")
    Pk, k = P.copy(), 1
    while k <= 64:
        p = pk(k)
        mk = p[0, 0]
        E = np.abs(N * Pk - p).max() / mk
        print(f"   k={k:3d}: sup |N P^k - p_k| / m_k = {E:.3f}   divided by delta' sqrt(k): {E/(dl*np.sqrt(k)):.3f}   Tr P^k/m_k - 1 = {np.trace(Pk)/mk - 1:+.4f}")
        Pk, k = Pk @ Pk, 2 * k
    for m in (1, 2, 4, 8, 16, 32, 64):
        h = P @ pk(m) - pk(m + 1)      # h[b, i] = (P p_m(. - x_i))(b) - p_{m+1}(x_b - x_i)
        r = (np.abs(h) * np.sqrt(m) / pk(6 * m)).max()
        print(f"   m={m:3d}: sup |h_m| sqrt(m) / p_6m = {r:.3f}   divided by delta': {r/dl:.3f}")
