"""The corrected estimator T - (sigma t/2) T'' on a sampled graph (Corollary "corrected estimator on the
sampled graph"). Flat 2-torus, Gaussian kernel, with and without the diagonal of the kernel.

T(t) = Tr e^{-tL} - N e^{-tau}, tau = 2t/xi^2; in the variable tau the corrected estimator is
T - (tau/2) d^2T/dtau^2. Printed: the relative deviation from Tr e^{t Delta} of the estimator and of the
corrected estimator, for the population walk (eigenvalues e^{-sigma lambda}) and as mean and standard
deviation over independent samples. Fixed seed, few samples: not evidence for a rate.
"""
import numpy as np

TAUS = (5, 10, 20, 40, 80)


def theta1(dx, var):
    return sum(np.exp(-(dx + a) ** 2 / (2 * var)) for a in range(-6, 7)) / np.sqrt(2 * np.pi * var)


def est(s, tau, n_sub):
    """estimator and corrected estimator from walk eigenvalues s; n_sub = number of subtracted terms."""
    e = np.exp(-tau * (1 - s))
    T = e.sum() - n_sub * np.exp(-tau)
    T2 = ((1 - s) ** 2 * e).sum() - n_sub * np.exp(-tau)
    return T, T - tau / 2 * T2


def run(N, xi, reps, seed=7):
    sig = xi**2 / 2
    n = np.arange(-60, 61)
    lam = 4 * np.pi**2 * (n[:, None] ** 2 + n[None, :] ** 2).ravel()
    spop = np.exp(-sig * lam)
    rng = np.random.default_rng(seed)
    res = {True: [], False: []}
    for _ in range(reps):
        X = rng.random((N, 2))
        K = theta1(X[:, None, 0] - X[None, :, 0], xi**2) * theta1(X[:, None, 1] - X[None, :, 1], xi**2)
        for loops in (True, False):
            Kc = K.copy()
            if not loops:
                np.fill_diagonal(Kc, 0)
            q = Kc.sum(1) / N
            W = Kc / np.outer(q, q)
            D = W.sum(1)
            s = np.linalg.eigvalsh(W / np.sqrt(np.outer(D, D)))
            res[loops].append([est(s, tau, N) for tau in TAUS])
    M = float(theta1(np.zeros(1), xi**2)[0]) ** 2
    print(f"N={N} xi={xi} M/N={M/N:.4f} samples={reps}")
    for j, tau in enumerate(TAUS):
        t = tau * sig
        Th = (np.exp(-4 * np.pi**2 * n**2 * t).sum()) ** 2
        # population: the subtraction of N e^{-tau} is replaced by the exact limit (all modes, s -> 0)
        e = np.exp(-tau * (1 - spop)) - np.exp(-tau)
        Tp = e.sum()
        Tp2 = ((1 - spop) ** 2 * np.exp(-tau * (1 - spop)) - np.exp(-tau)).sum()
        line = f"  tau={tau:3d}: population {Tp/Th-1:+.4f}, corrected {(Tp - tau/2*Tp2)/Th-1:+.4f}"
        for loops in (True, False):
            a = np.array(res[loops])[:, j, :] / Th - 1
            line += f" | {'loops' if loops else 'no loops'}: {a[:,0].mean():+.4f} ({a[:,0].std():.4f}), corrected {a[:,1].mean():+.4f} ({a[:,1].std():.4f})"
        print(line, flush=True)


run(1000, 0.1, 8)
run(2000, 0.1, 5)
run(2000, 0.07, 5)
