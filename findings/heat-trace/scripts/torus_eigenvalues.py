"""Eigenvalues of the graph Laplacian on the flat 2-torus against the population walk.

For one sample the script prints, for selected indices j (in increasing order, counting from zero), the
eigenvalue lambda_j of -Delta, the population value (1 - exp(-sigma lambda_j))/sigma of Theorem "The
eigenvalues of the sampled graph on a flat torus, uniformly", and the eigenvalue of the graph Laplacian
L = (2/xi^2)(1 - S). Gaussian kernel with self-loops, sigma = xi^2/2. One sample per configuration, fixed
seed; delta'/xi is printed and is not small in these runs.
"""
import numpy as np


def theta(dx, var):
    return sum(np.exp(-(dx + a) ** 2 / (2 * var)) for a in range(-6, 7)) / np.sqrt(2 * np.pi * var)


for N, xi in ((1500, 0.1), (3000, 0.1), (3000, 0.05)):
    rng = np.random.default_rng(5)
    X = rng.random((N, 2))
    dx = X[:, None, 0] - X[None, :, 0]
    dy = X[:, None, 1] - X[None, :, 1]
    K = theta(dx, xi**2) * theta(dy, xi**2)
    M = K[0, 0]
    del dx, dy
    q = K.sum(1) / N
    W = K / np.outer(q, q)
    D = W.sum(1)
    s = np.sort(np.linalg.eigvalsh(W / np.sqrt(np.outer(D, D))))[::-1]
    del W, K
    sig = xi**2 / 2
    lamN = (1 - s) / sig
    n = np.arange(-12, 13)
    lam = np.sort((4 * np.pi**2 * (n[:, None] ** 2 + n[None, :] ** 2)).ravel())
    pop = (1 - np.exp(-sig * lam)) / sig
    dl = np.sqrt(M * np.log(N) / N)
    print(f"N={N} xi={xi} M/N={M/N:.4f} delta'/xi={dl/xi:.2f}")
    for j in (1, 2, 5, 9, 13, 21, 29, 45, 57):
        print(f"   j={j:2d}: lambda_j = {lam[j]:8.2f}   population = {pop[j]:8.2f}   graph = {lamN[j]:8.2f}   graph - population = {lamN[j]-pop[j]:+7.3f}")


# Clusters of equal eigenvalues: mean relative deviation from the population value (a bias) and the
# spread of the graph eigenvalues within the cluster (a random splitting), three samples each.
CLUSTERS = [(1, 5), (5, 9), (9, 13), (13, 21), (21, 25), (25, 29), (29, 37)]
print("clusters: mean relative deviation from the population value, and spread within the cluster")
for N, xi in ((1500, 0.1), (3000, 0.1), (1500, 0.05), (3000, 0.05)):
    sig = xi**2 / 2
    n = np.arange(-12, 13)
    lam = np.sort((4 * np.pi**2 * (n[:, None] ** 2 + n[None, :] ** 2)).ravel())
    pop = (1 - np.exp(-sig * lam)) / sig
    acc = {c: [] for c in CLUSTERS}
    for seed in (5, 6, 7):
        rng = np.random.default_rng(seed)
        X = rng.random((N, 2))
        dx = X[:, None, 0] - X[None, :, 0]
        dy = X[:, None, 1] - X[None, :, 1]
        K = theta(dx, xi**2) * theta(dy, xi**2)
        M = K[0, 0]
        del dx, dy
        q = K.sum(1) / N
        W = K / np.outer(q, q)
        D = W.sum(1)
        s = np.sort(np.linalg.eigvalsh(W / np.sqrt(np.outer(D, D))))[::-1]
        del W, K
        lamN = (1 - s) / sig
        for c in CLUSTERS:
            acc[c].append((lamN[c[0]:c[1]] - pop[c[0]:c[1]]) / pop[c[0]:c[1]])
    print(f"N={N} xi={xi} M/N={M/N:.4f} 1/sqrt(N)={1/np.sqrt(N):.4f}")
    for c in CLUSTERS:
        a = np.array(acc[c])
        print(f"   lambda={lam[c[0]]:7.1f} multiplicity {c[1]-c[0]}: mean {a.mean():+.4f} = {a.mean()/(M/N):+.2f} M/N;   spread {a.std(axis=1).mean():.4f} = {a.std(axis=1).mean()*np.sqrt(N):.2f}/sqrt(N)")
