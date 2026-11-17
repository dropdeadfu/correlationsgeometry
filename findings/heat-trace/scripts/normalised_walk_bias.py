"""Bias of Tr P^k for the walk with the estimated normalisation, flat d-torus, periodised Gaussian kernel.

For each (d, N, xi) the mean of Tr P^k - m_k over independent samples is printed with its standard error,
relative to m_k and in units of M/N, once with the diagonal of the kernel kept (self-loops, the construction
of the paper) and once with the diagonal removed. m_k = Theta(k sigma), sigma = xi^2/2, M = p(0).

Exploratory numerics for the open problem on smaller kernel scales (Remark "What remains open for the
heat trace"). Heuristic under test: with self-loops the walk holds with probability about M/N per step,
which gives a relative bias of about (d/2) M/N, independent of k.

Also printed: the conjectured coefficient beta_k of the 1/N term of E Tr P^k - m_k (formula proposed by a
second session, derived as the expectation of the expansion to second order in the normalisation errors;
NOT proven):
    beta_k = k [ 1/2 T_0 - 2 T_1 + 3 T_2 - 2 T_3 + 1/2 T_4 ] + k m_k (m_4 - 3 m_3 + 3 m_2 - m_1),
    T_c = sum_{l=1}^{k-1} int p_l p_{k-l} p_c,   p_c = p^{*c},
and without self-loops beta_k - k M (m_{k-1} - m_k) for k >= 3, beta_2 - M^2 + 2 M m_2 for k = 2.

Fixed seed; a handful of samples per configuration is not evidence for a rate.
"""
import numpy as np

KS = [1, 2, 4, 8, 16, 32, 64]
CONFIGS = [  # (d, N, xi, samples)
    (2, 750, 0.08, 16), (2, 1500, 0.08, 12), (2, 3000, 0.08, 6),
    (2, 1500, 0.05, 12), (2, 3000, 0.05, 6), (2, 1500, 0.12, 12),
    (1, 1500, 0.01, 12), (3, 2500, 0.12, 8),
]


def heat0(t, d, cut=60):
    n = np.arange(-cut, cut + 1)
    return (np.exp(-4 * np.pi**2 * n**2 * t).sum()) ** d


def triple(a, b, c, sig, d):
    """int p_a p_b p_c on the d-torus (p_0 = delta), by Fourier sums."""
    w = 4 * np.pi**2 * sig
    cut = int(np.sqrt(40.0 / (w * max(min(a, b), 1)))) + 2 if c == 0 else int(np.sqrt(40.0 / w)) + 2
    n = np.arange(-cut, cut + 1)
    if c == 0:
        return (np.exp(-w * a * n**2).sum() * np.exp(-w * b * n**2).sum()) ** d
    n1, n2 = n[:, None], n[None, :]
    return (np.exp(-w * (a * n1**2 + b * n2**2 + c * (n1 + n2) ** 2)).sum()) ** d


def beta(k, sig, d, loops):
    m = lambda c: heat0(c * sig, d)
    T = [sum(triple(l, k - l, c, sig, d) for l in range(1, k)) for c in range(5)]
    b = k * (0.5 * T[0] - 2 * T[1] + 3 * T[2] - 2 * T[3] + 0.5 * T[4]) + k * m(k) * (m(4) - 3 * m(3) + 3 * m(2) - m(1))
    if loops:
        return b
    if k == 1:
        return float("nan")
    if k == 2:
        return b - m(1) ** 2 + 2 * m(1) * m(2)
    return b - k * m(1) * (m(k - 1) - m(k))


def traces(d, N, xi, reps, loops, rng):
    out = []
    for _ in range(reps):
        X = rng.random((N, d))
        K = np.ones((N, N))
        for c in range(d):            # product kernel; images -1, 0, 1 suffice for xi <= 0.12
            dx = X[:, None, c] - X[None, :, c]
            K *= sum(np.exp(-(dx + a) ** 2 / (2 * xi**2)) for a in (-1, 0, 1))
        if not loops:
            np.fill_diagonal(K, 0)
        q = K.sum(1) / N
        W = K / np.outer(q, q)
        D = W.sum(1)
        s = np.linalg.eigvalsh(W / np.sqrt(np.outer(D, D)))
        out.append([(s**k).sum() for k in KS])
    return np.array(out)


for loops in (True, False):
    rng = np.random.default_rng(21)
    print("=== kernel diagonal", "kept (self-loops)" if loops else "removed (no self-loops)")
    for d, N, xi, reps in CONFIGS:
        sig = xi**2 / 2
        M = heat0(sig, d)
        tr = traces(d, N, xi, reps, loops, rng)
        print(f"d={d} N={N} xi={xi} M={M:.2f} M/N={M/N:.5f} samples={reps}  (heuristic with loops: {d/2})")
        for j, k in enumerate(KS):
            mk = heat0(k * sig, d)
            B = tr[:, j].mean() - mk
            se = tr[:, j].std() / np.sqrt(reps)
            bk = beta(k, sig, d, loops) / N
            print(f"  k={k:3d} m_k={mk:8.3f}  Tr P^k - m_k = {B:+.4f} ({se:.4f})  conjecture beta_k/N = {bk:+.4f}  relative/(M/N): observed {B/mk/(M/N):+.3f}, conjecture {bk/mk/(M/N):+.3f}")
