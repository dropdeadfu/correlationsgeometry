"""Regime of the machine-checked weak form of the eigenvalue statement.

Evaluates the hypotheses of `heatTorus_eig_sample_bernstein` (lean/CorrelationsToGeometryReal.lean)
for the first nonconstant eigenvalue (frequency |n| = 1, alpha = exp(-c)) on the flat torus of
dimension d, kernel scale xi (sigma = xi^2/2, c = 2 pi^2 sigma), and asks for the smallest sample
size N (among powers of ten) for which the parameters k, m, R, eps_n, eps_c, eta can be chosen so
that all inequalities hold and the bound on the failure probability is at most p0.

This is a computation with the explicit constants of the Lean statement, not a simulation. The
choice of the free parameters is a search over a grid, so the reported N is an upper bound for
the smallest admissible N of the statement, not the exact threshold.
"""
import itertools
import math

P0 = 0.1


def lattice_shell(d, R):
    """Nonzero frequencies with |n|^2 < R, one of each pair n, -n; returns list of |n|^2."""
    r = int(math.isqrt(int(math.ceil(R)))) + 1
    out = []
    for n in itertools.product(range(-r, r + 1), repeat=d):
        s = sum(x * x for x in n)
        if 0 < s < R:
            # half-set: first nonzero coordinate positive
            first = next(x for x in n if x != 0)
            if first > 0:
                out.append(s)
    return out


def bern_eps(logterm, var, b):
    """Smallest eps with eps^2 / (4 var + 2 b eps) >= logterm."""
    # eps^2 - 2 b L eps - 4 var L = 0
    return b * logterm + math.sqrt((b * logterm) ** 2 + 4 * var * logterm)


def ratio(d, c, N, k, m, R):
    """Returns (lhs/rhs of h3, delta) for the best eps_n, eps_c, eta at failure probability P0."""
    M = (1 + math.sqrt(math.pi / c)) ** d
    L = 2 * math.pi * (2 / c) * (1 + math.sqrt(2 * math.pi / c)) ** d
    Lstar = L * M + M * L + 2 * L

    def B(j):  # bound of the heat kernel at time j c
        return (1 + math.sqrt(math.pi / (j * c))) ** d

    shell = lattice_shell(d, R)
    nF = 1 + 2 * len(shell)
    logm = math.log(m)
    eps_n = bern_eps(math.log(6 / P0) + d * logm, N * M, M)
    # one eps_c for all j < k: the j = 0 term has the largest variance proxy
    if k > 0:
        eps_c = bern_eps(math.log(6 * k / P0) + 2 * d * logm, N * M * B(1) * B(2), M * B(1))
    else:
        eps_c = 0.0
    eta = 2 * math.sqrt(2 * math.log(6 * nF * nF / P0) / N)
    delta = (eps_n + 2 * N * L / m) / N
    if delta > 1 / 8:
        return math.inf, delta
    epsc = (eps_c + 2 * N * Lstar / m) / N
    E = sum(3 * epsc + 11 * delta * B(j + 2) for j in range(k))
    Dk = 10 * delta * (B(k + 1) + E) + E
    t = math.exp(-(k + 1) * c * R / 2) * (1 + math.sqrt(2 * math.pi / ((k + 1) * c))) ** d
    eps = 3 * delta * (B(k + 1) + Dk) + Dk + t
    S = 1 + 2 * sum(math.exp(-(k + 1) * c * s / 2) for s in shell)
    lhs = 2 * (eps + eta * S)
    rhs = math.exp(-(k + 1) * c)
    return lhs / rhs, delta


def search(d, xi):
    c = math.pi ** 2 * xi ** 2
    for e in range(3, 61):
        N = 10.0 ** e
        best = (math.inf, None)
        for k in [0, 1, 2, 4, 8, 16, 32, 64, 128]:
            for me in range(2, 60, 2):
                m = 10.0 ** me
                for R in [2, 3, 5, 9, 17, 33, 65]:
                    if d >= 2 and R > 17:
                        continue
                    r, _ = ratio(d, c, N, k, m, R)
                    if r < best[0]:
                        best = (r, (k, me, R))
        if best[0] <= 1:
            return e, best
    return None, best


if __name__ == "__main__":
    print("smallest power of ten N for which the hypotheses of heatTorus_eig_sample_bernstein")
    print("can be met for the first nonconstant eigenvalue, failure probability <= %.1f" % P0)
    print("  d   xi      c       log10 N   k   log10 m   R    lhs/rhs")
    for d in (1, 2):
        for xi in (0.5, 0.3, 0.2, 0.1):
            e, best = search(d, xi)
            c = math.pi ** 2 * xi ** 2
            if e is None:
                print("  %d  %.2f  %7.4f   none up to 10^60 (best ratio %.3g)" % (d, xi, c, best[0]))
            else:
                k, me, R = best[1]
                print("  %d  %.2f  %7.4f   %5d   %4d   %5d   %3d   %.3f" % (d, xi, c, e, k, me, R, best[0]))
