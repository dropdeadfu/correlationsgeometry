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
