#!/usr/bin/env python3
"""A151: linear response of the node energy to a non-uniform node density on a FLAT slice (population level).

Checks every number of the fragment .tools/scratch/A151_density_response.tex.  Deterministic, no random numbers.

Setting.  Gaussian kernel g(x) = exp(-|x|^2/(2 xi^2)), density n(x), q = g*n, W(x,y) = g(x-y)/(q(x)q(y)),
D(x) = int W(x,y) n(y) dy, s(x,y) = W(x,y)/sqrt(D(x)D(y)) acting on L^2(n dy).  On L^2(dy) this is
T = A G A  (G = convolution by g, A = multiplication by sqrt(n)/(q sqrt(D))), and the return density per volume
r_j(x) = n(x) s^{(j)}(x,x) = T^j(x,x).  Energy per volume  u = -(omega_inf/2) sum_j c_j r_j,  omega_inf = sqrt2/xi.

Derived in the fragment (first order in phi = ln(n/n0), phi = eps e^{iax}):
  (i)   A = A0 (1 + alpha(a) phi),   alpha(a) = (1 - gamma)^2/2,   gamma = e^{-xi^2 a^2/2};
  (ii)  delta r_j = alpha * Int dk/(2pi)^D (t_k + t_{k+a}) (t_{k+a}^j - t_k^j)/(t_{k+a} - t_k) * phi,  t_k = e^{-xi^2 k^2/2};
  (iii) sum over j with c_j:  divided difference of F(s) = 1 - sqrt(1-s) is 1/(w_k + w_{k+a}), w = sqrt(1-t);
  (iv)  u = rho_eff + c(a) Laplace(phi),   c(a) = alpha(a) I(a) / (sqrt2 xi a^2),
        I(a) = Int dk/(2pi)^D (t_k + t_{k+a})/(w_k + w_{k+a});
  (v)   c(a)/b_R -> 3 (a xi)^2 as a -> 0 for every D >= 2 (b_R = zeta_{D/2-1} xi /(12 sqrt2 (2 pi xi^2)^{D/2})),
        D = 3: c/b_R = 3x [1 - x ln(1/x)/(24 sqrt(pi) zeta_{1/2}) + O(x)],  x = (a xi)^2.

Sections: [1] alpha in D = 1 by quadrature; [2] r_j and F in D = 1; [3] D = 3: continuum and torus formula,
direct reduced computation, comparison with scripts/density_response_flat.py (0.280, 0.935, 1.609);
[4] small-x expansion in D = 3 (mpmath); [5] second order in eps of the TOTAL energy, direct against a derived formula;
[6] gamma predicted from c(a) with b_int taken from the paper note.
Memory < 200 MB, run time about two minutes.

Usage: .tools/venv/bin/python .tools/scratch/a151_check.py
"""
import numpy as np
import mpmath as mp

SQ2 = np.sqrt(2.0)


def cj(J):
    j = np.arange(1, J + 1, dtype=float)
    c = np.empty(J)
    c[0] = 0.5
    c[1:] = 0.5 * np.cumprod((2 * j[:-1] - 1) / (2 * j[:-1] + 2))
    return c


def zeta(s, J=400000):
    j = np.arange(1, J + 1, dtype=float)
    c = cj(J)
    return float(np.sum(c * j ** (-s)) + c[-1] * J ** 1.5 * J ** (-(0.5 + s)) / (0.5 + s))


def F(s):
    return 1.0 - np.sqrt(np.clip(1.0 - s, 0.0, None))


def Phi(l):
    """Phi(l) = sum_j c_j l^j / j = int_0^l F(s)/s ds (closed form)."""
    w = np.sqrt(np.clip(1.0 - l, 0.0, None))
    return 2 * np.log((1 + w) / 2) + 2 * (1 - w)


# ---------------------------------------------------------------- [1], [2]: D = 1, quadrature on the unit circle
def pop1d(M, xi, eps, q):
    """Population operator on the unit circle, grid of M points, density n = 1 + eps cos(2 pi q x).
    Returns x, A_i = sqrt(n)/(q sqrt(D)), and Ttil = w^{1/2} s w^{1/2} with r_j(x_i) = M (Ttil^j)_ii."""
    x = np.arange(M) / M
    n = 1 + eps * np.cos(2 * np.pi * q * x)
    w = n / M
    d = x[None, :] - x[:, None]
    g = sum(np.exp(-(d + m) ** 2 / (2 * xi ** 2)) for m in (-2, -1, 0, 1, 2))
    qq = g @ w
    Wk = g / np.outer(qq, qq)
    Dd = Wk @ w
    s = Wk / np.sqrt(np.outer(Dd, Dd))
    A = np.sqrt(n) / (qq * np.sqrt(Dd))
    Tt = np.sqrt(w)[:, None] * s * np.sqrt(w)[None, :]
    return x, A, Tt


def cos_coeff(f, x, q):
    return 2 * np.mean(f * np.cos(2 * np.pi * q * x))


def section12():
    print("[1] alpha(a) = (1-gamma)^2/2 in D = 1 (M = 400, xi = 0.05, eps = +-1e-3; first-order cos coefficient of A/A0 - 1)")
    M, xi, eps = 400, 0.05, 1e-3
    _, A0, _ = pop1d(M, xi, 0.0, 1)
    A0 = A0.mean()
    for q in (1, 2, 3, 5):
        a = 2 * np.pi * q
        x, Ap, _ = pop1d(M, xi, eps, q)
        _, Am, _ = pop1d(M, xi, -eps, q)
        meas = cos_coeff((Ap - Am) / (2 * eps * A0), x, q)
        al = (1 - np.exp(-(a * xi) ** 2 / 2)) ** 2 / 2
        print(f"    q={q}  (a xi)^2={(a*xi)**2:.4f}  measured {meas:.10e}   formula {al:.10e}   ratio {meas/al:.8f}")
    print("[2] response of r_j (j = 1..4) and of sum_j c_j r_j = diag F(T) in D = 1 vs formula (ii)/(iii), torus sum over k in 2 pi Z")
    for q in (1, 3):
        a = 2 * np.pi * q
        x, _, Tp = pop1d(M, xi, eps, q)
        _, _, Tm = pop1d(M, xi, -eps, q)
        k = 2 * np.pi * np.arange(-400, 401)
        t = np.exp(-xi ** 2 * k ** 2 / 2)
        ta = np.exp(-xi ** 2 * (k + a) ** 2 / 2)
        al = (1 - np.exp(-(a * xi) ** 2 / 2)) ** 2 / 2
        Pp, Pm = np.eye(M), np.eye(M)
        for j in range(1, 5):
            Pp, Pm = Pp @ Tp, Pm @ Tm
            meas = cos_coeff(M * (np.diag(Pp) - np.diag(Pm)) / (2 * eps), x, q)
            form = al * np.sum((t + ta) * sum(ta ** m * t ** (j - 1 - m) for m in range(j)))
            print(f"    q={q} j={j}: measured {meas:.10e}   formula {form:.10e}   ratio {meas/form:.8f}")
        ev, U = np.linalg.eigh(Tp)
        fp = M * (U ** 2 @ F(ev))
        ev, U = np.linalg.eigh(Tm)
        fm = M * (U ** 2 @ F(ev))
        meas = cos_coeff((fp - fm) / (2 * eps), x, q)
        wk, wa = np.sqrt(1 - t), np.sqrt(1 - ta)
        form = al * np.sum((t + ta) / (wk + wa))
        print(f"    q={q} F  : measured {meas:.10e}   formula {form:.10e}   ratio {meas/form:.8f}")


# ---------------------------------------------------------------- [3]: D = 3
def I3_continuum(a, xi, N=400001, L=40.0):
    """I(a) in D = 3, a along x; transverse integral done exactly: (1/(2 pi xi^2)) Int dk/(2pi) (u+v)(Phi(v)-Phi(u))/(v-u)."""
    k = np.linspace(-L / xi, L / xi, N)
    dk = k[1] - k[0]
    u = np.exp(-xi ** 2 * k ** 2 / 2)
    v = np.exp(-xi ** 2 * (k + a) ** 2 / 2)
    big = np.abs(v - u) > 1e-12
    dd = np.where(big, (Phi(v) - Phi(u)) / np.where(big, v - u, 1.0), F(u) / np.maximum(u, 1e-300))
    return np.sum((u + v) * dd) * dk / (2 * np.pi) / (2 * np.pi * xi ** 2)


def I3_torus(a, xi, mmax=30):
    """I(a) on the unit 3-torus: sum over k in 2 pi Z^3 of (t_k + t_{k+a})/(w_k + w_{k+a})."""
    m = np.arange(-mmax, mmax + 1)
    kt2 = ((2 * np.pi) ** 2 * (m[:, None] ** 2 + m[None, :] ** 2)).ravel()
    k1 = 2 * np.pi * m
    t = np.exp(-xi ** 2 * (k1[:, None] ** 2 + kt2[None, :]) / 2)
    ta = np.exp(-xi ** 2 * ((k1[:, None] + a) ** 2 + kt2[None, :]) / 2)
    tot = np.sum((t + ta) / (np.sqrt(1 - t) + np.sqrt(1 - ta)))
    rho = -(SQ2 / xi / 2) * np.sum(F(t))
    return tot, rho


def u3_reduced(N, xi, eps, q, mmax=40):
    """Direct computation, same setting as scripts/density_response_flat.py: nodes x_l = l/N + (eps/a) sin(a l/N)
    in direction 1, transverse directions uniform on the unit 2-torus (sum over transverse momenta).
    Returns the node energy minus omega_inf/2, times the mean node density (the normalisation of that script)."""
    a = 2 * np.pi * q
    lab = np.arange(N) / N
    x = lab + (eps / a) * np.sin(a * lab)
    d = x[None, :] - x[:, None]
    K = sum(np.exp(-(d + mm) ** 2 / (2 * xi ** 2)) for mm in (-2, -1, 0, 1, 2))
    qn = K.sum(1)
    W = K / np.outer(qn, qn)
    Dd = W.sum(1)
    S = W / np.sqrt(np.outer(Dd, Dd))
    lam, U = np.linalg.eigh(S)
    m = np.arange(-mmax, mmax + 1)
    tau = np.exp(-xi ** 2 * (2 * np.pi) ** 2 * (m[:, None] ** 2 + m[None, :] ** 2) / 2).ravel()
    G = F(np.clip(np.outer(lam, tau), 0, 1)).sum(1)
    return -(SQ2 / xi / 2) * N * (U ** 2 @ G), lab


def section3():
    xi = 0.05
    bR = zeta(0.5) * xi / (12 * SQ2 * (2 * np.pi * xi ** 2) ** 1.5)
    rho_eff = -zeta(1.5) / (SQ2 * xi * (2 * np.pi * xi ** 2) ** 1.5)
    print(f"[3] D = 3, xi = {xi}: rho_eff = {rho_eff:.6f}, b_R = {bR:.6f}")
    u0, _ = u3_reduced(64, xi, 0.0, 1)
    _, rho_T = I3_torus(2 * np.pi, xi)
    print(f"    flat torus: direct reduced {u0.mean():.4f}, torus mode sum {rho_T:.4f}  (difference to rho_eff = finite size of the unit torus)")
    meas_script = {1: 0.280, 2: 0.935, 3: 1.609}
    print("    q   x=(a xi)^2   continuum c/b_R   torus c/b_R   direct eps=0.02   direct eps=0.005   script (paper note)")
    for q in (1, 2, 3):
        a = 2 * np.pi * q
        x = (a * xi) ** 2
        al = (1 - np.exp(-x / 2)) ** 2 / 2
        cc = al * I3_continuum(a, xi) / (SQ2 * xi * a ** 2) / bR
        IT, _ = I3_torus(a, xi)
        ct = al * IT / (SQ2 * xi * a ** 2) / bR
        dr = []
        for eps in (0.02, 0.005):
            up, lab = u3_reduced(64, xi, eps, q)
            um, _ = u3_reduced(64, xi, -eps, q)
            cq = cos_coeff((up - um) / (2 * eps), lab, q)
            dr.append((cq - u0.mean()) / a ** 2 / bR)
        print(f"    {q}   {x:.4f}       {cc:.5f}          {ct:.5f}       {dr[0]:.5f}          {dr[1]:.5f}            {meas_script[q]:.3f}")


# ---------------------------------------------------------------- [4]: small-x expansion, D = 3 (xi = 1, scale free)
def section4():
    mp.mp.dps = 25
    z = mp.nsum(lambda j: mp.fabs(mp.binomial(mp.mpf(1) / 2, j)) * j ** mp.mpf(-0.5), [1, mp.inf])

    def Phim(l):
        w = mp.sqrt(1 - l)
        return 2 * mp.log((1 + w) / 2) + 2 * (1 - w)

    def dd(u, v):
        if abs(v - u) < mp.mpf(10) ** -12:
            return (1 - mp.sqrt(1 - u)) / u
        return (Phim(v) - Phim(u)) / (v - u)

    def I(a):
        f = lambda k: (mp.exp(-k ** 2 / 2) + mp.exp(-(k + a) ** 2 / 2)) * dd(mp.exp(-k ** 2 / 2), mp.exp(-(k + a) ** 2 / 2))
        return mp.quad(f, [-mp.inf, -a - 1, -a, -a / 2, 0, 1, mp.inf]) / (2 * mp.pi) ** 2

    I0 = 2 * (2 * mp.pi) ** mp.mpf(-1.5) * z
    Apred = 1 / (24 * mp.sqrt(mp.pi) * z)
    print(f"[4] D = 3 small x: zeta_1/2 = {mp.nstr(z, 12)}, I(0) = 2 (2 pi)^(-3/2) zeta_1/2 = {mp.nstr(I0, 12)}")
    print(f"    predicted coefficient of x ln(1/x) in I(a)/I(0) - 1:  -1/(24 sqrt(pi) zeta_1/2) = {mp.nstr(-Apred, 10)}")
    rows = []
    for xs in ("1e-6", "1e-5", "1e-4", "1e-3", "1e-2"):
        x = mp.mpf(xs)
        a = mp.sqrt(x)
        r = I(a) / I0 - 1
        al = (1 - mp.exp(-x / 2)) ** 2 / 2
        kap = al * I(a) / (mp.sqrt(2) * x) * 12 * mp.sqrt(2) * (2 * mp.pi) ** mp.mpf(1.5) / z / x
        rows.append((x, r))
        print(f"    x = {xs}: c/(b_R x) = {mp.nstr(kap, 12)},  I/I0 - 1 = {mp.nstr(r, 9)},  (I/I0 - 1)/(x ln 1/x) = {mp.nstr(r / (x * mp.log(1 / x)), 8)}")
    (x1, r1), (x2, r2) = rows[0], rows[1]
    L1, L2 = mp.log(1 / x1), mp.log(1 / x2)
    # r = -A x L + B x  ->  r/x = -A L + B
    A = -((r1 / x1) - (r2 / x2)) / (L1 - L2)
    B = r1 / x1 + A * L1
    print(f"    fit from x = 1e-6, 1e-5:  A = {mp.nstr(A, 8)} (predicted {mp.nstr(Apred, 8)}),  B = {mp.nstr(B, 6)}")
    print(f"    hence c/(b_R x) = 3 - {mp.nstr(3 * Apred, 6)} x ln(1/x) - {mp.nstr(mp.mpf(3) / 2 - 3 * B, 6)} x + o(x)")


# ---------------------------------------------------------------- [5]: total energy at second order
def E2_formula(a, xi, N=600001, L=30.0):
    """Second order in phi of the total energy per volume (continuum), phi = -eps cos(a x_1), per eps^2:
    E2 = -(omega_inf/2) { J0 [2<a2> + 2<a1^2>]/eps^2 + (1/4)(1-gamma)^4 K },  J0 = Int t F'(t) = I(0)/2,
    2<a2>/eps^2 = -(1/4)(1-gamma)^2(1-gamma^2),  2<a1^2>/eps^2 = (1/4)(1-gamma)^4,
    K = Int dk t_k t_{k+a} (F'(t_{k+a}) - F'(t_k))/(t_{k+a} - t_k)   (transverse integrals done exactly).
    Returns (leading term, full formula)."""
    k = np.linspace(-L / xi, L / xi, N)
    dk = k[1] - k[0]
    u = np.exp(-xi ** 2 * k ** 2 / 2)
    v = np.exp(-xi ** 2 * (k + a) ** 2 / 2)
    J0 = np.sum(F(u)) * dk / (2 * np.pi) / (2 * np.pi * xi ** 2)
    big = np.abs(v - u) > 1e-10
    dd = np.where(big, (F(v) / v - F(u) / u) / np.where(big, v - u, 1.0), 0.0)
    K = np.sum(u * v * dd) * dk / (2 * np.pi) / (2 * np.pi * xi ** 2)
    g = np.exp(-(a * xi) ** 2 / 2)
    om2 = SQ2 / xi / 2
    lead = -om2 * J0 * (-0.25 * (1 - g) ** 2 * (1 - g ** 2))
    full = lead - om2 * (J0 * 0.25 * (1 - g) ** 4 + 0.25 * (1 - g) ** 4 * K)
    return lead, full


def section5():
    print("[5] second order in eps of the TOTAL energy per volume, flat torus, D = 3: direct (Richardson in eps = 0.02, 0.04)"
          " against the formula; leading term -> (3/2) b_R xi^4 Int |grad Laplace phi|^2, i.e. E2/(b_R (a^2/2) x^2) -> 3/2")
    for xi in (0.05, 0.025, 0.0125):
        N = int(round(3.3 / xi))
        bR = zeta(0.5) * xi / (12 * SQ2 * (2 * np.pi * xi ** 2) ** 1.5)
        E0 = u3_reduced(N, xi, 0.0, 1)[0].mean()
        for q in ((1, 2) if xi < 0.05 else (1, 2, 3)):
            a = 2 * np.pi * q
            x = (a * xi) ** 2
            Es = {e: 0.5 * (u3_reduced(N, xi, e, q)[0].mean() + u3_reduced(N, xi, -e, q)[0].mean()) - E0 for e in (0.02, 0.04)}
            E2 = (4 * Es[0.02] / 0.02 ** 2 - Es[0.04] / 0.04 ** 2) / 3
            lead, full = E2_formula(a, xi)
            nrm = bR * a * a / 2 * x * x
            print(f"    xi = {xi:<7} q = {q}  x = {x:.5f}:  direct E2/b_R = {E2/bR:.6g}   formula {full/bR:.6g}   ratio {full/E2:.5f}"
                  f"   direct E2/(b_R (a^2/2) x^2) = {E2/nrm:.4f}   leading-term formula {lead/nrm:.4f}")


# ---------------------------------------------------------------- [6]: predicted gamma (uses b_int from the paper note)
def section6():
    print("[6] gamma = 1 - (3/4) c/b_int with c from (iv) (continuum, depends on x only) and b_int/b_R = 1.83"
          " (value in the paper note, from scripts/static_response_gamma.py, not recomputed here)")
    xi = 1.0
    bR = zeta(0.5) * xi / (12 * SQ2 * (2 * np.pi * xi ** 2) ** 1.5)
    for x, gm in ((0.021, 0.982), (0.031, 0.961), (0.048, 0.934), (0.084, 0.887), (0.099, 0.880), (0.124, 0.852), (0.193, 0.815)):
        a = np.sqrt(x)
        al = (1 - np.exp(-x / 2)) ** 2 / 2
        c = al * I3_continuum(a, xi) / (SQ2 * xi * a * a) / bR
        print(f"    x = {x:.3f}:  c/b_R = {c:.4f}   gamma predicted {1 - 0.75 * c / 1.83:.4f}   gamma in the paper note {gm:.3f}")


if __name__ == "__main__":
    section12()
    section3()
    section4()
    section5()
    section6()
