"""Evaluates the numerical hypotheses of the Lean statement `heat_kernel_sharp_sample`
(lean/CorrelationsToGeometryReal.lean) and of its variant with the two bounds of Step 3
(`kernel_theorem_matrix_min`), with the explicit constants of the file.

The parameter sigma of the Lean statements is the VARIANCE of the periodised Gaussian kernel,
sigma_Lean = xi^2 = 2 sigma_paper (heatTorus d (2 pi^2 sigma_Lean) = p^(sigma_Lean)); an earlier
version of this script used xi^2/2 (corrected on 19 November 2026).

For dimension d, kernel scale xi (sigma = xi^2 below), sample size N and number of
steps K the script chooses the free parameters (grid g, tolerance eps, level L) so that the
failure probability
    (2 + 4K) * 2 g^d exp(-eps^2/(4 N M + 2 M eps)) + 4 K N^2 exp(-L)
is at most 0.1, computes delta = (eps + 2 N Lip/g)/N and the smallest admissible
    W_{j+1} = (sum_{m<j} T(j,m) + etasup_{j+1}) / mu_{j+2},
where T(j,m) = min(2 mu_{j-m} etabar_{m+1}, etasup_{m+1}) (variant "min", the hypothesis `hsum`
of `heat_kernel_sharp_sample`) or 2 mu_{j-m} etabar_{m+1} (variant "mean", for comparison; not a
statement of the file), and etabar is `heatEtaBar` of the file,
and checks `hW`: 4 delta + (1 + 4 delta) W_{j+1} <= 1 for all j + 1 < K.

It reports, for each configuration, the smallest N among powers of ten for which both
hypotheses hold (an upper bound for the threshold), the resulting relative bound
4 delta + (1 + 4 delta) W at the last step, and the ratio W / (delta' sqrt(k)) with
delta' = sqrt(M log N / N).  Nothing here is a proof; the script only evaluates formulas.
"""
import math

PI = math.pi


def heatM(d, c):
    return (1 + math.sqrt(PI / c)) ** d


def mu(d, sigma, k):
    return heatM(d, 2 * PI ** 2 * k * sigma) if k > 0 else 0.0


def pre(t):
    return 1 / math.sqrt(2 * PI * t)


def heatKB(d, sigma, s):
    return (pre(sigma) * pre(s) * (math.sqrt(4 * PI * sigma) + 1)) ** d / pre(s + 2 * sigma) ** d


def heatCV(d, sigma, s):
    eps = sigma / s * (4 / (PI * s)) * ((1 + math.sqrt(12 * PI * s)) * math.sqrt(12 * PI * s))
    alpha = (1 + math.sqrt(PI / (2 * PI ** 2 * s))) * math.sqrt(6 * s / (sigma + s))
    return d * eps * alpha ** (d - 1)


def defnum(d, sigma, N, m, M, L, delta, pa, pb, q):
    s = m * sigma
    KB, CV = heatKB(d, sigma, s), heatCV(d, sigma, s)
    B = KB * pa + M * pb
    thr = 2 * B * L + 2 * math.sqrt(N * M * CV * L) * q
    return ((thr + 2 * B) + 2 * delta * (N * math.sqrt(CV) * q + thr + 2 * B)) / (N / 3)


def heatQ(d, c):
    return (math.sqrt(1 / math.sqrt(c / PI)) / (1 / math.sqrt(2 * c / PI))) ** d


def etabar(d, sigma, N, m, M, L, delta):
    q = min(N * math.sqrt(1 + delta),
            heatQ(d, 2 * PI ** 2 * 6 * m * sigma) * N * (1 + delta))
    return defnum(d, sigma, N, m, M, L, delta, N * (1 + delta), N * (1 + delta), q) / N


def etasup(d, sigma, N, m, M, L, delta):
    s = m * sigma
    c = lambda t: 2 * PI ** 2 * t
    return defnum(d, sigma, N, m, M, L, delta, heatM(d, c(s + 2 * sigma)),
                  heatM(d, c(sigma + s)), math.sqrt(heatM(d, c(6 * s))))


def parameters(d, sigma, N, K):
    c = 2 * PI ** 2 * sigma
    M = heatM(d, c)
    Lip = 2 * PI * (2 / c) * (1 + math.sqrt(2 * PI / c)) ** d
    L = math.log(80 * K * N ** 2)
    g = 1
    for _ in range(60):
        T = math.log((2 + 4 * K) * 2 * g ** d / 0.05)
        eps = M * T + math.sqrt(M ** 2 * T ** 2 + 4 * N * M * T)
        g_new = max(1, math.ceil(2 * N * Lip / eps))
        if g_new == g:
            break
        g = g_new
    T = math.log((2 + 4 * K) * 2 * g ** d / 0.05)
    eps = M * T + math.sqrt(M ** 2 * T ** 2 + 4 * N * M * T)
    delta = (eps + 2 * N * Lip / g) / N
    return M, L, delta


def evaluate(d, xi, N, K, variant):
    sigma = xi ** 2
    M, L, delta = parameters(d, sigma, N, K)
    if delta > 1 / 8:
        return None
    eb = [0.0] + [etabar(d, sigma, N, m, M, L, delta) for m in range(1, K + 1)]
    es = [0.0] + [etasup(d, sigma, N, m, M, L, delta) for m in range(1, K + 1)]
    mus = [mu(d, sigma, k) for k in range(K + 3)]
    Wlast = None
    for j in range(0, K - 1):          # j + 1 < K
        tot = es[j + 1]
        for m in range(j):
            a = 2 * mus[j - m] * eb[m + 1]
            tot += a if variant == "mean" else min(a, es[m + 1])
        W = tot / mus[j + 2]
        if 4 * delta + (1 + 4 * delta) * W > 1:
            return None
        Wlast = W
    dprime = math.sqrt(M * math.log(N) / N)
    rel = 4 * delta + (1 + 4 * delta) * (Wlast if Wlast is not None else 0.0)
    ratio = Wlast / (dprime * math.sqrt(K)) if Wlast is not None else float("nan")
    return delta, rel, ratio


def closed_form(d, xi, N, K):
    """Hypotheses of `heat_kernel_rate_sample`: closed constants, W_K = 2 2^d max(2a, b) sqrt(K)."""
    sigma = xi ** 2
    if sigma > 1 or K * sigma > 1:
        return None
    M, L, delta = parameters(d, sigma, N, K)
    if delta > 1 / 8:
        return None
    kb = (pre(sigma) * ((math.sqrt(4 * PI) + 1) * math.sqrt(3))) ** d
    theta = (2 * L + 2) * (kb + M) * math.sqrt(K) / N
    cv = 4 / PI * (1 + math.sqrt(12 * PI)) * math.sqrt(12 * PI) * math.sqrt(2 * PI)
    r = math.sqrt(d * cv * (2 * math.sqrt(6)) * (12 * (1 + math.sqrt(2 * PI))) ** (d - 1))
    r2 = math.sqrt(d * cv * math.sqrt(6) ** (d - 1))
    S = math.sqrt(N * M * L) / N
    a = 3 * (1 + delta) * ((1 + 2 * delta) * (theta + 2 * S * r) + 2 * delta * r)
    b = 3 * ((1 + 2 * delta) * (theta + 2 * S * r2) + 2 * delta * r2)
    W = 2 * 2 ** d * max(2 * a, b) * math.sqrt(K)
    if 4 * delta + (1 + 4 * delta) * W > 1:
        return None
    dprime = math.sqrt(M * math.log(N) / N)
    return delta, 4 * delta + (1 + 4 * delta) * W, W / (dprime * math.sqrt(K))


def explicit_form(d, xi, N, K):
    """Hypotheses of `heat_kernel_rate_explicit`: T = log((2+4K) 2 g^d N^3), L = log(4 K N^5),
    delta = 6 sqrt(N M T)/N, theta = (2L+2)(kb+M) sqrt(K)/N; failure probability 2/N^3."""
    sigma = xi ** 2
    if sigma > 1 or K * sigma > 1:
        return None
    c = 2 * PI ** 2 * sigma
    M = heatM(d, c)
    Lip = 2 * PI * (2 / c) * (1 + math.sqrt(2 * PI / c)) ** d
    L = math.log(4 * K * N ** 5)
    g = 1
    for _ in range(200):
        T = math.log((2 + 4 * K) * 2 * g ** d * N ** 3)
        g_new = max(1, math.ceil(2 * N * Lip / (3 * math.sqrt(N * M * T))))
        if g_new <= g:
            break
        g = g_new
    T = math.log((2 + 4 * K) * 2 * g ** d * N ** 3)
    if 2 * N * Lip / g > 3 * math.sqrt(N * M * T) or 6 * math.sqrt(N * M * T) > N / 8:
        return None
    delta = 6 * math.sqrt(N * M * T) / N
    kb = (pre(sigma) * ((math.sqrt(4 * PI) + 1) * math.sqrt(3))) ** d
    theta = (2 * L + 2) * (kb + M) * math.sqrt(K) / N
    cv = 4 / PI * (1 + math.sqrt(12 * PI)) * math.sqrt(12 * PI) * math.sqrt(2 * PI)
    r = math.sqrt(d * cv * (2 * math.sqrt(6)) * (12 * (1 + math.sqrt(2 * PI))) ** (d - 1))
    r2 = math.sqrt(d * cv * math.sqrt(6) ** (d - 1))
    S = math.sqrt(N * M * L) / N
    a = 3 * (1 + delta) * ((1 + 2 * delta) * (theta + 2 * S * r) + 2 * delta * r)
    b = 3 * ((1 + 2 * delta) * (theta + 2 * S * r2) + 2 * delta * r2)
    W = 2 * 2 ** d * max(2 * a, b) * math.sqrt(K)
    if 4 * delta + (1 + 4 * delta) * W > 1:
        return None
    dprime = math.sqrt(M * math.log(N) / N)
    return delta / dprime, 4 * delta + (1 + 4 * delta) * W, W / (dprime * math.sqrt(K))


def lattice(d, R):
    """Squared norms of the nonzero integer vectors with |n|^2 < R."""
    import itertools
    m = int(math.sqrt(R)) + 1
    out = []
    for n in itertools.product(range(-m, m + 1), repeat=d):
        q = sum(x * x for x in n)
        if 0 < q < R:
            out.append(q)
    return out


def eig_shell(d, xi, N, K):
    """Hypotheses of `heat_eig_rate_shell` for the first shell (r = 1), with the parameters of
    `heat_kernel_rate_explicit`, H = half of the nonzero frequencies with |n|^2 < R, and eta such
    that the Gram term of the probability is 1/N^3.  Returns the best bound for |s_j - alpha|/alpha
    over the steps k = j' + 1 < K and R, or None."""
    sigma = xi ** 2
    if sigma > 1 or K * sigma > 1:
        return None
    c = 2 * PI ** 2 * sigma
    M = heatM(d, c)
    Lip = 2 * PI * (2 / c) * (1 + math.sqrt(2 * PI / c)) ** d
    L = math.log(4 * K * N ** 5)
    g = 1
    for _ in range(200):
        T = math.log((2 + 4 * K) * 2 * g ** d * N ** 3)
        g_new = max(1, math.ceil(2 * N * Lip / (3 * math.sqrt(N * M * T))))
        if g_new <= g:
            break
        g = g_new
    T = math.log((2 + 4 * K) * 2 * g ** d * N ** 3)
    if 2 * N * Lip / g > 3 * math.sqrt(N * M * T) or 6 * math.sqrt(N * M * T) > N / 8:
        return None
    delta = 6 * math.sqrt(N * M * T) / N
    kb = (pre(sigma) * ((math.sqrt(4 * PI) + 1) * math.sqrt(3))) ** d
    theta = (2 * L + 2) * (kb + M) * math.sqrt(K) / N
    cv = 4 / PI * (1 + math.sqrt(12 * PI)) * math.sqrt(12 * PI) * math.sqrt(2 * PI)
    r = math.sqrt(d * cv * (2 * math.sqrt(6)) * (12 * (1 + math.sqrt(2 * PI))) ** (d - 1))
    r2 = math.sqrt(d * cv * math.sqrt(6) ** (d - 1))
    S = math.sqrt(N * M * L) / N
    a = 3 * (1 + delta) * ((1 + 2 * delta) * (theta + 2 * S * r) + 2 * delta * r)
    b = 3 * ((1 + 2 * delta) * (theta + 2 * S * r2) + 2 * delta * r2)
    Wc = 2 * 2 ** d * max(2 * a, b)
    if 4 * delta + (1 + 4 * delta) * Wc * math.sqrt(K) > 1:
        return None
    best = None
    for R in (4, 6, 8, 12, 16, 24, 32):
        norms = lattice(d, R)
        F = 1 + len(norms)
        eta = math.sqrt(8 * math.log(2 * F ** 2 * N ** 3) / N)
        for k in range(1, K):
            cp = (k + 1) * c
            mu1 = heatM(d, cp)
            Dk = (4 * delta + (1 + 4 * delta) * Wc * math.sqrt(k)) * mu1
            t = math.exp(-cp * R / 2) * (1 + math.sqrt(2 * PI / cp)) ** d
            eps = 3 * delta * (mu1 + Dk) + Dk + t
            Ssum = 1 + sum(math.exp(-cp * q / 2) for q in norms)
            err = eps + eta * Ssum
            alphak = math.exp(-cp)
            if 2 * err <= alphak:
                bound = 2 * err / ((k + 1) * alphak)
                if best is None or bound < best[0]:
                    best = (bound, k, R)
    return best


def rate_cfin(d):
    """The constant `rateCfin d` of `heat_kernel_rate_paper`."""
    cK = ((math.sqrt(4 * PI) + 1) * math.sqrt(3)) ** d
    cv = 4 / PI * (1 + math.sqrt(12 * PI)) * math.sqrt(12 * PI) * math.sqrt(2 * PI)
    rA = math.sqrt(d * cv * (2 * math.sqrt(6)) * (12 * (1 + math.sqrt(2 * PI))) ** (d - 1))
    rB = math.sqrt(d * cv * math.sqrt(6) ** (d - 1))
    A = math.sqrt(d + 5)
    CA = 3 * (9 / 8) * ((5 / 4) * (16 * (cK + 1) + 2 * math.sqrt(7) * rA) + 12 * A * rA)
    CB = 3 * ((5 / 4) * (16 * (cK + 1) + 2 * math.sqrt(7) * rB) + 12 * A * rB)
    return 48 * A + 3 * 2 ** d * max(2 * CA, CB)


def rate_cfin3(d):
    """The constant `rateCfin3 d` of `heat_kernel_rate_paper_g3` (grid N^3, all times)."""
    cK = ((math.sqrt(4 * PI) + 1) * math.sqrt(3)) ** d
    cv = 4 / PI * (1 + math.sqrt(12 * PI)) * math.sqrt(12 * PI) * math.sqrt(2 * PI)
    rA = math.sqrt(d * cv * (2 * math.sqrt(6)) * (12 * (1 + math.sqrt(2 * PI))) ** (d - 1))
    A = math.sqrt(3 * d + 5)
    CA = 3 * (9 / 8) * ((5 / 4) * (16 * (cK + 1) + 2 * math.sqrt(7) * rA) + 12 * A * rA)
    CB = 3 * ((5 / 4) * (16 * (cK + 1) + 2 * math.sqrt(7) * rA) + 12 * A * rA)
    return 48 * A + 3 * 2 ** d * max(2 * CA, CB)


def kernel_c1(d):
    """The constant `kernelC1 d` of `kernel_theorem_G28`."""
    return rate_cfin3(d) * ((1 + math.sqrt(2 * PI)) ** d) ** 2


def eig_c4(d):
    """The constant `eigC4 d` of `eig_theorem_G38`."""
    cp = (36 * math.sqrt(3 * d + 5) + rate_cfin3(d) + 1
          + math.sqrt(8 * (3 + 2 * (3 * d + 1))) * (1 + 2 * 2 ** d))
    return 16 * cp * (1 + math.sqrt(2 * PI)) ** d


def p_zero(d, xi):
    """The periodised Gaussian kernel of variance xi^2 at the origin, M = p(0)."""
    t = xi ** 2
    return (sum(math.exp(-n * n / (2 * t)) for n in range(-50, 51)) / math.sqrt(2 * PI * t)) ** d


def g28_holds(d, xi, N, K):
    """Hypothesis of `kernel_theorem_G28`: kernelC1(d) delta' sqrt(K) <= 1 with M = p(0)."""
    dprime = math.sqrt(p_zero(d, xi) * math.log(N) / N)
    return xi <= 1 and N >= 2 and kernel_c1(d) * dprime * math.sqrt(K) <= 1


def g38_holds(d, xi, N, r):
    """Hypotheses of `eig_theorem_G38` for the shell |n|^2 = r."""
    dprime = math.sqrt(p_zero(d, xi) * math.log(N) / N)
    return (xi <= 1 and N >= 2 and 2 * PI ** 2 * xi ** 2 * r <= 0.5
            and eig_c4(d) * dprime / xi * (2 * PI * math.sqrt(r)) ** (d - 1) <= 1)


def paper_form(d, xi, N, K):
    """Hypotheses of `heat_kernel_rate_paper`: N >= 12, K <= N, K sigma <= 1, sigma <= 1,
    2 Lip <= 3 sqrt(N M log N), rateCfin(d) delta' sqrt(K) <= 1."""
    sigma = xi ** 2
    c = 2 * PI ** 2 * sigma
    M = heatM(d, c)
    Lip = 2 * PI * (2 / c) * (1 + math.sqrt(2 * PI / c)) ** d
    dprime = math.sqrt(M * math.log(N) / N)
    return (N >= 12 and K <= N and K * sigma <= 1 and sigma <= 1
            and 2 * Lip <= 3 * math.sqrt(N * M * math.log(N))
            and rate_cfin(d) * dprime * math.sqrt(K) <= 1)


def main():
    print("smallest N (power of ten) for which the numerical hypotheses hold; failure probability 0.1")
    print("d   xi    K   variant   N        delta     rel. bound at k=K   W/(delta' sqrt K)")
    for d in (1, 2, 3):
        for xi in (0.3, 0.2, 0.1):
            sigma = xi ** 2
            for K in (4, 16, int(round(1 / sigma))):
                for variant in ("mean", "min"):
                    found = None
                    for e in range(3, 41):
                        r = evaluate(d, xi, 10 ** e, K, variant)
                        if r is not None:
                            found = (e, r)
                            break
                    if found is None:
                        print(f"{d}  {xi:4.2f} {K:4d}   {variant:5s}   none up to 1e40")
                    else:
                        e, (delta, rel, ratio) = found
                        print(f"{d}  {xi:4.2f} {K:4d}   {variant:5s}   1e{e:<3d}   {delta:8.2e}  {rel:8.3f}"
                              f"            {ratio:10.1f}")
    print()
    print("closed form (hypotheses of heat_kernel_rate_sample), K sigma <= 1")
    print("d   xi    K   N        delta     rel. bound at k=K   W/(delta' sqrt K)")
    for d in (1, 2, 3):
        for xi in (0.3, 0.2, 0.1):
            sigma = xi ** 2
            for K in (4, 16, int(1 / sigma)):
                found = None
                for e in range(3, 61):
                    r = closed_form(d, xi, 10 ** e, K)
                    if r is not None:
                        found = (e, r)
                        break
                if found is None:
                    print(f"{d}  {xi:4.2f} {K:4d}   none up to 1e60")
                else:
                    e, (delta, rel, ratio) = found
                    print(f"{d}  {xi:4.2f} {K:4d}   1e{e:<3d}   {delta:8.2e}  {rel:8.3f}            {ratio:10.1f}")
    print()
    print("all parameters explicit (hypotheses of heat_kernel_rate_explicit), failure probability 2/N^3")
    print("d   xi    K   N        delta/delta'  rel. bound at k=K   W/(delta' sqrt K)")
    for d in (1, 2, 3):
        for xi in (0.3, 0.2, 0.1):
            sigma = xi ** 2
            for K in (4, 16, int(1 / sigma)):
                found = None
                for e in range(3, 61):
                    r = explicit_form(d, xi, 10 ** e, K)
                    if r is not None:
                        found = (e, r)
                        break
                if found is None:
                    print(f"{d}  {xi:4.2f} {K:4d}   none up to 1e60")
                else:
                    e, (dr, rel, ratio) = found
                    print(f"{d}  {xi:4.2f} {K:4d}   1e{e:<3d}   {dr:8.2f}      {rel:8.3f}            {ratio:10.1f}")
    print()
    print("first shell of eigenvalues (hypotheses of heat_eig_rate_shell, r = 1), K = floor(1/sigma)")
    print("d   xi    N       best bound for |s_j - alpha|   at k   R     (alpha = exp(-2 pi^2 xi^2))")
    for d in (1, 2):
        for xi in (0.3, 0.2):
            sigma = xi ** 2
            K = int(1 / sigma)
            first = None
            for e in range(3, 41):
                r = eig_shell(d, xi, 10 ** e, K)
                if r is not None:
                    first = e
                    break
            if first is None:
                print(f"{d}  {xi:4.2f}   none up to 1e40")
                continue
            for e in (first, first + 2, first + 4):
                bound, k, R = eig_shell(d, xi, 10 ** e, K)
                print(f"{d}  {xi:4.2f}   1e{e:<3d}   {bound:10.3e}                  {k:4d}  {R:3d}")
    print()
    print("form D_k <= C delta' sqrt(k) mu_k (hypotheses of heat_kernel_rate_paper)")
    for d in (1, 2, 3):
        print(f"rateCfin({d}) = {rate_cfin(d):.4g}")
    print("d   xi    K   smallest N (power of ten)")
    for d in (1, 2, 3):
        for xi in (0.3, 0.2, 0.1):
            sigma = xi ** 2
            for K in (4, int(1 / sigma)):
                found = None
                for e in range(2, 61):
                    if paper_form(d, xi, 10 ** e, K):
                        found = e
                        break
                print(f"{d}  {xi:4.2f} {K:4d}   " + ("none up to 1e60" if found is None else f"1e{found}"))
    print()
    print("statements in the form of the appendix (kernel_theorem_G28, eig_theorem_G38)")
    for d in (1, 2, 3):
        print(f"kernelC1({d}) = {kernel_c1(d):.4g}   eigC4({d}) = {eig_c4(d):.4g}")
    print("d   xi    K   smallest N (power of ten) with kernelC1 delta' sqrt(K) <= 1")
    for d in (1, 2, 3):
        for xi in (1.0, 0.3, 0.1):
            for K in (1, max(1, int(1 / xi ** 2))):
                found = None
                for e in range(2, 81):
                    if g28_holds(d, xi, 10 ** e, K):
                        found = e
                        break
                print(f"{d}  {xi:4.2f} {K:4d}   " + ("none up to 1e80" if found is None else f"1e{found}"))
    print("d   xi   smallest N (power of ten) with the condition of eig_theorem_G38 for the first shell")
    for d in (1, 2, 3):
        for xi in (0.15, 0.1, 0.05):
            found = None
            for e in range(2, 81):
                if g38_holds(d, xi, 10 ** e, 1):
                    found = e
                    break
            print(f"{d}  {xi:4.2f}   " + ("none up to 1e80" if found is None else f"1e{found}"))


if __name__ == "__main__":
    main()
