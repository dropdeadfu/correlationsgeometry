#!/usr/bin/env python3
"""Entanglement equilibrium (geometric part of principle (P2)) for the oscillators on the kernel graph:
entanglement entropy of a geodesic ball on a round sphere against a flat ball of the same volume.

Model (population level = infinite node density, uniform density, units xi = 1): kernel K = exp(-d^2/2) in the
geodesic distance, S = D^{-1/2} W D^{-1/2} (on a homogeneous space W = K/q^2 and S is the population walk),
L = 2(1 - S), H = (1/2) sum p^2 + (1/2) x^T (L + m^2) x, ground state X = (L+m^2)^{-1/2}/2, P = (L+m^2)^{1/2}/2.
X = f0 + F, P = g0 + G with f0 = f(s=0), g0 = g(0) the ultralocal parts (symplectic eigenvalue 1/2, no entropy)
and F, G smooth kernels of width ~ xi; X_A P_A - 1/4 = -F_AB G_BA is trace class, so the entropy has a finite
limit as the node density tends to infinity (checked: flat D = 3 value equals the grid value of
scripts/area_law_vs_curvature.py).

Rotational symmetry about the axis of the ball: sector mu (S^2, azimuthal number, multiplicity 2 for mu > 0)
resp. j (S^3, angular momentum on the 2-sphere around the pole, multiplicity 2j+1); in each sector the kernels
are sums over the eigenvalues s_l of the population walk (Proposition "sphere" of the paper for S^2; for S^3
s_l = E[sin((l+1)t)/((l+1) sin t)] with density exp(-rho^2 t^2/2) sin^2 t), with normalised associated Legendre
functions resp. sin^j(chi) times orthonormal Gegenbauer polynomials; flat disk/ball: Hankel transform with
J_mu resp. spherical Bessel j_j.  Radial direction: composite Gauss-Legendre (Nystrom), 8 nodes per xi.
Flat area-law coefficient eta: strip [0, X] (two cuts, X >> 1/m) with the transverse momentum integrated.

Comparison: cap of geodesic radius r on the sphere of radius rho, flat ball of the same volume
(D = 2: R_f = 2 rho sin(r/2rho); D = 3: (4/3) pi R_f^3 = pi rho^3 (2 chi - sin 2 chi), chi = r/rho).
Prediction of (P2): Delta S = eta Delta A.  Local expansion S = int_dA (eta + gamma k^2 + delta R + ...)
(no odd terms: S(A) = S(complement) for a pure state): gamma from the flat balls, delta from the caps.

Usage: entanglement_equilibrium_sphere.py      deterministic (quadrature only), no arguments; runtime about 13 minutes
(2 cores), peak memory below 0.5 GB.
"""
import sys
import time
from math import lgamma
import numpy as np

def fg(s, m):
    om = np.sqrt(2.0 * (1.0 - s) + m * m)
    return 0.5 / om, 0.5 * om


def entropy_from(FA, GA, m):
    f0, g0 = fg(0.0, m)
    n = FA.shape[0]
    XA = f0 * np.eye(n) + FA
    PA = g0 * np.eye(n) + GA
    Lc = np.linalg.cholesky(PA)
    ev = np.linalg.eigvalsh(Lc.T @ XA @ Lc)
    nu = np.sqrt(np.clip(ev, 0.25, None))
    nu = nu[nu > 0.5 + 1e-14]
    return float(np.sum((nu + 0.5) * np.log(nu + 0.5) - (nu - 0.5) * np.log(nu - 0.5)))


def gl(a, b, n):
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * x + 0.5 * (b + a), 0.5 * (b - a) * w




def panels(a, b, npx=8, ppanel=16):
    npan = max(1, int(np.ceil((b - a) * npx / ppanel)))
    e = np.linspace(a, b, npan + 1)
    xs, ws = zip(*[gl(e[i], e[i + 1], ppanel) for i in range(npan)])
    return np.concatenate(xs), np.concatenate(ws)


# ---------------------------------------------------------------- sphere of radius rho (xi = 1)
def sphere_sl(rho, lmax, nq=6000):
    tmax = min(np.pi, 14.0 / rho)
    e = np.linspace(0.0, tmax, nq // 32 + 1)
    th, w = (np.concatenate(a) for a in zip(*[gl(e[i], e[i + 1], 32) for i in range(len(e) - 1)]))
    dens = np.exp(-(rho * th) ** 2 / 2) * np.sin(th) * w
    dens /= dens.sum()
    x = np.cos(th)
    s = np.empty(lmax + 1)
    p0 = np.ones_like(x); p1 = x.copy()
    s[0] = 1.0; s[1] = dens @ p1
    for l in range(1, lmax):
        p0, p1 = p1, ((2 * l + 1) * x * p1 - l * p0) / (l + 1)
        s[l + 1] = dens @ p1
    return s


def assoc_legendre_block(mu, lmax, u, st):
    """Lambda_{l mu}(u), l = mu..lmax, normalised: int_{-1}^1 Lambda^2 du = 1.  st = sin(theta) >= 0."""
    k = np.arange(1, mu + 1)
    logc = 0.5 * (np.log((2 * mu + 1) / 2.0) + np.sum(np.log((2 * k - 1) / (2.0 * k))))
    with np.errstate(divide='ignore'):
        lg = logc + mu * np.log(st)
    p_mm = np.where(lg > -700, np.exp(np.maximum(lg, -700)), 0.0)
    out = np.zeros((lmax - mu + 1, len(u)))
    out[0] = p_mm
    if lmax == mu:
        return out
    out[1] = np.sqrt(2 * mu + 3) * u * p_mm
    a_prev = np.sqrt(2 * mu + 3.0)
    for l in range(mu + 2, lmax + 1):
        a = np.sqrt((4.0 * l * l - 1) / (l * l - mu * mu))
        out[l - mu] = a * (u * out[l - mu - 1] - out[l - mu - 2] / a_prev)
        a_prev = a
    return out


def cap_entropy(rho, r, m, npx=8, lfac=10.0, kperp_max=10.0, verbose=False):
    """Entropy of the geodesic cap of radius r on the sphere of radius rho; returns (S, per-sector list)."""
    lmax = int(np.ceil(lfac * rho))
    s = sphere_sl(rho, lmax)
    f, g = fg(s, m); f0, g0 = fg(0.0, m)
    df, dg = f - f0, g - g0
    th0 = r / rho
    x, w = panels(0.0, r, npx)                     # physical arc length from the pole
    th = x / rho
    u, st = np.cos(th), np.sin(th)
    sq = np.sqrt(w / rho * st)                      # Nystrom weights for the measure du = sin(theta) dtheta
    mumax = min(lmax, int(np.ceil(kperp_max * rho * np.sin(min(th0, np.pi / 2)))) + 10)
    S = 0.0; per = []
    for mu in range(0, mumax + 1):
        B = assoc_legendre_block(mu, lmax, u, st) * sq[None, :]
        F = B.T @ (df[mu:, None] * B)
        G = B.T @ (dg[mu:, None] * B)
        e = entropy_from(F, G, m)
        S += e if mu == 0 else 2 * e
        per.append(e)
    return S, per


# ---------------------------------------------------------------- flat plane (xi = 1)
def bessel_orders(xv, nmax, lo=0):
    """J_n(x), n = 0..nmax, by Miller's backward recurrence, vectorised over x (x >= 0)."""
    xv = np.asarray(xv, float)
    xm = max(1.0, xv.max())
    M = int(max(nmax, xm) + 30 + 4 * np.sqrt(max(nmax, xm)))
    M += M % 2
    J = np.zeros((nmax + 1 - lo, xv.size))
    xs = np.where(xv == 0, 1.0, xv)
    jp1 = np.zeros_like(xv); jc = np.full_like(xv, 1e-30); norm = np.zeros_like(xv)
    for n in range(M, 0, -1):
        jm1 = 2 * n / xs * jc - jp1
        jp1, jc = jc, jm1                           # jc = J_{n-1}
        if lo <= n - 1 <= nmax:
            J[n - 1 - lo] = jc
        if (n - 1) % 2 == 0:
            norm += (2.0 if n - 1 > 0 else 1.0) * jc
        big = np.abs(jc) > 1e200
        if big.any():
            jc[big] *= 1e-200; jp1[big] *= 1e-200; norm[big] *= 1e-200
            if n - 1 <= nmax:
                J[max(n - 1 - lo, 0):, big] *= 1e-200
    J /= norm[None, :]
    J[:, xv == 0] = 0.0
    if lo == 0:
        J[0, xv == 0] = 1.0
    return J


def disk_entropy(R, m, npx=8, kmax=10.0, nk=None, kperp_max=10.0, batch=48):
    x, w = panels(0.0, R, npx)
    if nk is None:
        nk = int(60 + 12 * R)
    k, wk = gl(0.0, kmax, nk)
    s = np.exp(-k * k / 2)
    f, g = fg(s, m); f0, g0 = fg(0.0, m)
    df, dg = (f - f0) * k * wk, (g - g0) * k * wk
    mumax = int(np.ceil(kperp_max * R)) + 10
    arg = (k[:, None] * x[None, :]).ravel()
    sq = np.sqrt(w * x)
    S = 0.0; per = []
    for lo in range(0, mumax + 1, batch):
        hi = min(mumax, lo + batch - 1)
        J = bessel_orders(arg, hi, lo)
        for mu in range(lo, hi + 1):
            B = J[mu - lo].reshape(nk, len(x)) * sq[None, :]
            F = B.T @ (df[:, None] * B); G = B.T @ (dg[:, None] * B)
            e = entropy_from(F, G, m)
            S += e if mu == 0 else 2 * e
            per.append(e)
        del J
    return S, per


def s3_sl(rho, lmax, nq=6000):
    tmax = min(np.pi, 14.0 / rho)
    e = np.linspace(0.0, tmax, nq // 32 + 1)
    th, w = (np.concatenate(a) for a in zip(*[gl(e[i], e[i + 1], 32) for i in range(len(e) - 1)]))
    dens = np.exp(-(rho * th) ** 2 / 2) * np.sin(th) ** 2 * w
    dens /= dens.sum()
    st = np.sin(th)
    # U_l(cos th) = sin((l+1)th)/sin th by recursion U_{l+1} = 2x U_l - U_{l-1}
    x = np.cos(th)
    s = np.empty(lmax + 1)
    u0 = np.ones_like(x); u1 = 2 * x
    s[0] = 1.0; s[1] = dens @ u1 / 2
    for l in range(1, lmax):
        u0, u1 = u1, 2 * x * u1 - u0
        s[l + 1] = dens @ u1 / (l + 2)
    return s


def radial_block(j, lmax, x, st):
    """R_{lj}(chi) = sin^j chi p_{l-j}(cos chi), l = j..lmax, orthonormal for sin^2 chi dchi on [0, pi];
    p_n orthonormal Gegenbauer polynomials for the weight (1-x^2)^{lambda-1/2}, lambda = j+1."""
    lam = j + 1.0
    lognorm0 = -0.5 * (0.5 * np.log(np.pi) + lgamma(lam + 0.5) - lgamma(lam + 1))
    with np.errstate(divide='ignore'):
        lg = lognorm0 + j * np.log(st)
    p0 = np.where(lg > -700, np.exp(np.maximum(lg, -700)), 0.0)
    out = np.zeros((lmax - j + 1, len(x)))
    out[0] = p0
    a = lambda n: 0.5 * np.sqrt(n * (n + 2 * lam - 1) / ((n + lam) * (n + lam - 1)))
    if lmax > j:
        out[1] = x * p0 / a(1)
    for n in range(2, lmax - j + 1):
        out[n] = (x * out[n - 1] - a(n - 1) * out[n - 2]) / a(n)
    return out


def cap3_entropy(rho, r, m, npx=8, lfac=10.0, kperp_max=10.0):
    lmax = int(np.ceil(lfac * rho))
    s = s3_sl(rho, lmax)
    f, g = fg(s, m); f0, g0 = fg(0.0, m)
    df, dg = f - f0, g - g0
    xx, w = panels(0.0, r, npx)
    ch = xx / rho
    x, st = np.cos(ch), np.sin(ch)
    sq = np.sqrt(w / rho * st ** 2)
    jmax = min(lmax, int(np.ceil(kperp_max * rho * np.sin(min(r / rho, np.pi / 2)))) + 10)
    S = 0.0; per = []
    for j in range(jmax + 1):
        B = radial_block(j, lmax, x, st) * sq[None, :]
        F = B.T @ (df[j:, None] * B); G = B.T @ (dg[j:, None] * B)
        e = entropy_from(F, G, m)
        S += (2 * j + 1) * e; per.append(e)
    return S, per


def sph_bessel_orders(xv, nmax, lo=0):
    """j_n(x), n = lo..nmax, backward recurrence normalised by sum (2n+1) j_n^2 = 1."""
    xv = np.asarray(xv, float)
    xm = max(1.0, xv.max())
    M = int(max(nmax, xm) + 30 + 4 * np.sqrt(max(nmax, xm)))
    J = np.zeros((nmax + 1 - lo, xv.size))
    xs = np.where(xv == 0, 1.0, xv)
    jp1 = np.zeros_like(xv); jc = np.full_like(xv, 1e-30); norm = np.zeros_like(xv)
    norm += (2 * M + 1) * jc ** 2
    for n in range(M, 0, -1):
        jm1 = (2 * n + 1) / xs * jc - jp1
        jp1, jc = jc, jm1
        if lo <= n - 1 <= nmax:
            J[n - 1 - lo] = jc
        norm += (2 * n - 1) * jc ** 2
        big = np.abs(jc) > 1e100
        if big.any():
            jc[big] *= 1e-100; jp1[big] *= 1e-100; norm[big] *= 1e-200
            if n - 1 <= nmax:
                J[max(n - 1 - lo, 0):, big] *= 1e-100
    j0t = np.where(xv == 0, 1.0, np.sin(xs) / xs)
    j1t = np.where(xv == 0, 0.0, np.sin(xs) / xs ** 2 - np.cos(xs) / xs)
    sgn = np.sign(jc * j0t + jp1 * j1t)
    J *= (sgn / np.sqrt(norm))[None, :]
    J[:, xv == 0] = 0.0
    if lo == 0:
        J[0, xv == 0] = 1.0
    return J, None, None


def ball_entropy(R, m, npx=8, kmax=10.0, nk=None, kperp_max=10.0, batch=48):
    x, w = panels(0.0, R, npx)
    if nk is None:
        nk = int(60 + 12 * R)
    k, wk = gl(0.0, kmax, nk)
    s = np.exp(-k * k / 2)
    f, g = fg(s, m); f0, g0 = fg(0.0, m)
    df, dg = (f - f0) * k * k * wk * 2 / np.pi, (g - g0) * k * k * wk * 2 / np.pi
    jmax = int(np.ceil(kperp_max * R)) + 10
    arg = (k[:, None] * x[None, :]).ravel()
    sq = np.sqrt(w) * x
    S = 0.0; per = []
    for lo in range(0, jmax + 1, batch):
        hi = min(jmax, lo + batch - 1)
        J, _, _ = sph_bessel_orders(arg, hi, lo)
        for j in range(lo, hi + 1):
            B = J[j - lo].reshape(nk, len(x)) * sq[None, :]   # sign per x irrelevant? see note
            F = B.T @ (df[:, None] * B); G = B.T @ (dg[:, None] * B)
            e = entropy_from(F, G, m)
            S += (2 * j + 1) * e; per.append(e)
        del J
    return S, per

def strip_entropy(k, X, m, npx=8, qmax=10.0, nq=400):
    x, w = panels(0.0, X, npx)
    q, wq = gl(0.0, qmax, nq)
    s = np.exp(-(q*q + k*k)/2)
    f, g = fg(s, m); f0, g0 = fg(0.0, m)
    d = x[:, None] - x[None, :]
    if True:
        F = np.zeros_like(d); G = np.zeros_like(d)
        for qq, ww, ff, gg in zip(q, wq, f - f0, g - g0):
            c = np.cos(qq*d); F += ww*ff*c; G += ww*gg*c
    F /= np.pi; G /= np.pi
    sw = np.sqrt(w)
    return entropy_from(sw[:,None]*F*sw[None,:], sw[:,None]*G*sw[None,:], m)

def eta(D, m, X, npx=8, kmax=9.0, nk=60):
    k, wk = gl(0.0, kmax, nk)
    s = np.array([strip_entropy(kk, X, m, npx) for kk in k])
    if D == 2: return float(np.sum(wk*s)/np.pi/2), s
    return float(np.sum(wk*k*s)/(2*np.pi)/2), s


# ======================================================================================== driver
def flat_radius(D, rho, r):
    chi = r / rho
    if D == 2:
        return 2 * rho * np.sin(chi / 2)
    return (0.75 * rho ** 3 * (2 * chi - np.sin(2 * chi))) ** (1 / 3)


def area(D, R):
    return 2 * np.pi * R if D == 2 else 4 * np.pi * R * R


def cap_area(D, rho, r):
    return 2 * np.pi * rho * np.sin(r / rho) if D == 2 else 4 * np.pi * (rho * np.sin(r / rho)) ** 2


def flat_entropy(D, R, m, **kw):
    return (disk_entropy if D == 2 else ball_entropy)(R, m, **kw)[0]


def sphere_entropy(D, rho, r, m, **kw):
    return (cap_entropy if D == 2 else cap3_entropy)(rho, r, m, **kw)[0]


def main():
    sys.stdout.reconfigure(line_buffering=True)
    t0 = time.time()
    T = lambda: f"[{time.time() - t0:5.0f}s]"
    print("Part 1. Flat area-law coefficient eta (strip [0,X], two cuts, transverse momenta integrated), xi = 1")
    e3v = eta(3, 0.05, 16.0)[0]
    print(f"  validation D=3, m=0.05: eta xi^2 = {e3v:.5f}  (grid value of scripts/area_law_vs_curvature.py at"
          f" m xi = 0.05: 0.00824 (n xi = 3.2), 0.00830 (n xi = 6.4))  {T()}")
    ms = {2: [0.15, 0.3, 1.0], 3: [0.3, 1.0]}
    etas = {}
    for D in (2, 3):
        for m in ms[D]:
            X = max(20.0, 8.0 / m)
            e, e2 = eta(D, m, X)[0], eta(D, m, X + 10)[0]
            etas[D, m] = e2
            print(f"  D={D} m={m:4.2f}: eta = {e2:.7f}  (X={X + 10:.0f}; with X={X:.0f}: {e:.7f})  {T()}")

    print("\nPart 2. Flat balls: S - eta*A against R; fit S - eta A = c0 + c1/R (D=2) resp. c0 + c2/R^2 (D=3)")
    coef = {}
    for D in (2, 3):
        Rs = [10.0, 20.0, 40.0] if D == 2 else [5.0, 10.0, 20.0]
        for m in ms[D]:
            res = np.array([flat_entropy(D, R, m) - etas[D, m] * area(D, R) for R in Rs])
            p = -1 if D == 2 else -2
            A = np.vstack([np.ones(3), np.array(Rs) ** p]).T
            c = np.linalg.lstsq(A, res, rcond=None)[0]
            coef[D, m] = c
            print(f"  D={D} m={m:4.2f}: R = {Rs}: S - eta A = " + ", ".join(f"{x:+.5f}" for x in res)
                  + f";  c0 = {c[0]:+.5f}, c{-p} = {c[1]:+.5f}  {T()}")

    print("\nPart 3. Caps on the sphere of radius rho against flat balls of the same volume")
    print("  local expansion: D=2: S = eta A + gamma int k^2 + delta int R + ...;  gamma = c1/(2 pi) from Part 2;")
    print("  delta_fit = (Delta S - eta Delta A - gamma Delta int k^2) / (2 A_cap / rho^2)")
    print("  D=3: the extrinsic (k^2) and intrinsic (R, Ric_nn) terms are both dimensionless and proportional to"
          " sin^2 chi for caps;\n  c_fit = (Delta S - eta Delta A) / sin^2 chi")
    rows = []
    for D in (2, 3):
        rhos = [10.0, 20.0, 40.0] if D == 2 else [10.0, 20.0]
        print(f"\n  D={D}:   m     rho     r    r/rho     R_f      S_cap        S_flat       Delta S     eta Delta A"
              f"   ratio     residual   " + ("delta_fit" if D == 2 else "c_fit"))
        for m in ms[D]:
            for rho in rhos:
                for chi in (0.5, 1.0, 1.5):
                    r = chi * rho
                    Rf = flat_radius(D, rho, r)
                    Sc = sphere_entropy(D, rho, r, m)
                    Sf = flat_entropy(D, Rf, m)
                    dS = Sc - Sf
                    edA = etas[D, m] * (cap_area(D, rho, r) - area(D, Rf))
                    resid = dS - edA
                    if D == 2:
                        gam = coef[D, m][1] / (2 * np.pi)
                        dk2 = 2 * np.pi * np.cos(chi) ** 2 / (rho * np.sin(chi)) - 2 * np.pi / Rf
                        fit = (resid - gam * dk2) / (2 * cap_area(D, rho, r) / rho ** 2)
                    else:
                        fit = resid / np.sin(chi) ** 2
                    rows.append((D, m, rho, r, dS, edA))
                    print(f"        {m:4.2f} {rho:6.1f} {r:6.1f} {chi:6.2f} {Rf:9.4f} {Sc:12.6f} {Sf:12.6f}"
                          f" {dS:+12.6f} {edA:+12.6f} {dS / edA:8.5f} {resid:+11.6f} {fit:+10.5f}  {T()}",
                          flush=True)

    print("\nPart 4. Convergence in the discretisation (rho = 20, r = 20, m = 0.3): Delta S for changed parameters")
    for D in (2, 3):
        rho, r, m = 20.0, 20.0, 0.3
        Rf = flat_radius(D, rho, r)
        base = sphere_entropy(D, rho, r, m) - flat_entropy(D, Rf, m)
        out = []
        for name, kc, kf in [("npx=12", dict(npx=12), dict(npx=12)), ("lfac=13/nk*1.5", dict(lfac=13.0),
                             dict(nk=int(1.5 * (60 + 12 * Rf)))), ("kperp_max=13", dict(kperp_max=13.0),
                             dict(kperp_max=13.0)), ("kmax=13", dict(), dict(kmax=13.0))]:
            v = sphere_entropy(D, rho, r, m, **kc) - flat_entropy(D, Rf, m, **kf)
            out.append(f"{name}: {v - base:+.1e}")
        print(f"  D={D}: Delta S = {base:+.10f};  changes: " + "; ".join(out) + f"  {T()}")
    print(f"\ntotal runtime {time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
