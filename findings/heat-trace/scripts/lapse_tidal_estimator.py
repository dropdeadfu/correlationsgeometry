"""Draft B1 (paper/drafts/time_and_dynamics.tex): the curvature -Omega''/Omega from cross-ratios, D = 1.

Model: a chain with lattice spacing a on [x_lo, x_hi] (Dirichlet ends far from the points used),
  A = -Laplace_lattice + mbar^2 Omega(x)^2,   X = (1/2) A^(-1/2)   (ground-state correlator),
with Omega(x) = 1 + eps sin(x). Reconstructed arc length s(x) = int Omega dx, D = mbar s.

Estimator. For four nodes a < b < c < d with reconstructed distances r_xy = s_y - s_x,
  rho  = ( Z_ad Z_bc / (Z_ac Z_bd) )^2,   Z_xy = X_xy / K_0(mbar r_xy)        (node factors cancel),
  Khat = 6 (rho - 1) / (r_ad^2 + r_bc^2 - r_ac^2 - r_bd^2),
to be compared with the curvature K = -(d^2 Omega/ds^2)/Omega of the metric Omega^2 dtau^2 + ds^2 at the
centre. For equally spaced nodes (spacing l) the denominator is 2 l^2.

The exponentially small correlators are computed with high relative accuracy: X = (1/pi) int_0^infty
(A + w^2)^(-1) dw, and the entries of the inverse of the tridiagonal matrix A + w^2 are products of
positive ratios (no cancellation); everything is kept in logarithms.

Single deterministic runs; the table shows the form of the error, it is not a proof of a rate.
Usage: python lapse_tidal_estimator.py
"""
import numpy as np


def k0e(z):
    """exp(z) K_0(z) = int_0^infty exp(-z (cosh t - 1)) dt, by the trapezoidal rule (numpy only)."""
    t = np.linspace(0.0, 12.0, 24001)
    f = np.exp(-z * (np.cosh(t) - 1.0))
    return float((f.sum() - 0.5 * (f[0] + f[-1])) * (t[1] - t[0]))


def logsumexp(v):
    m = v.max()
    return float(m + np.log(np.exp(v - m).sum()))

EPS = 0.25
X_LO, X_HI = -3.0, 9.0


def omega(x):
    return 1.0 + EPS * np.sin(x)


def arc(x):
    """s(x) = int_0^x Omega."""
    return x - EPS * (np.cos(x) - 1.0)


def curvature(x):
    """K = -(d^2 Omega/ds^2)/Omega with d/ds = Omega^(-1) d/dx."""
    om = omega(x)
    d1 = EPS * np.cos(x)
    d2 = -EPS * np.sin(x)
    # d/ds (Omega_x / Omega) = (Omega_xx Omega - Omega_x^2) / Omega^3
    return -((d2 * om - d1 ** 2) / om ** 3) / om


def log_correlators(mbar, a, idx):
    """log X(x_i, x_j) for all pairs i < j of the sorted site indices idx."""
    x = np.arange(X_LO, X_HI + a / 2, a)
    n = len(x)
    c = 1.0 / a ** 2
    diag0 = 2.0 * c + (mbar * omega(x)) ** 2
    # quadrature in w = mbar sinh(u)
    u = np.linspace(0.0, 7.0, 281)
    du = u[1] - u[0]
    w = mbar * np.sinh(u)
    wt = mbar * np.cosh(u) * du
    wt[0] *= 0.5
    wt[-1] *= 0.5
    d = diag0[:, None] + (w ** 2)[None, :]          # n x nw
    fwd = np.empty_like(d)                           # forward Schur complements
    bwd = np.empty_like(d)                           # backward Schur complements
    fwd[0] = d[0]
    for i in range(1, n):
        fwd[i] = d[i] - c * c / fwd[i - 1]
    bwd[n - 1] = d[n - 1]
    for i in range(n - 2, -1, -1):
        bwd[i] = d[i] - c * c / bwd[i + 1]
    logstep = np.log(c) - np.log(bwd)                # log of G(i,l)/G(i,l-1) for l > i
    cum = np.cumsum(logstep, axis=0)
    out = {}
    for p, i in enumerate(idx):
        logdiag = -np.log(fwd[i] + bwd[i] - d[i])    # log G(i,i)
        for j in idx[p + 1:]:
            logg = logdiag + cum[j] - cum[i]
            out[(i, j)] = logsumexp(logg + np.log(wt)) - np.log(np.pi) - np.log(a)
    return x, out


def estimate(mbar, ell, x0, a):
    xs = np.arange(X_LO, X_HI + a / 2, a)
    s = arc(xs)
    s0 = arc(x0)
    targets = s0 + ell * np.array([-1.5, -0.5, 0.5, 1.5])
    idx = [int(np.argmin(np.abs(s - t))) for t in targets]
    x, logx = log_correlators(mbar, a, idx)
    sa, sb, sc, sd = (s[i] for i in idx)

    def logz(i, j):
        r = s[j] - s[i]
        # Z = X / K_0(mbar r); K_0(z) = k0e(z) exp(-z)
        return logx[(i, j)] + mbar * r - np.log(k0e(mbar * r))

    ia, ib, ic, id_ = idx
    rho = np.exp(2.0 * (logz(ia, id_) + logz(ib, ic) - logz(ia, ic) - logz(ib, id_)))
    den = (sd - sa) ** 2 + (sc - sb) ** 2 - (sc - sa) ** 2 - (sd - sb) ** 2
    khat = 6.0 * (rho - 1.0) / den
    centre = 0.5 * (x[ib] + x[ic])
    return khat, curvature(centre), rho


def main():
    print("Omega(x) = 1 + %.2f sin x; lattice spacing a = 0.05/mbar; four nodes with spacing l in s" % EPS)
    print("mbar    l      x0    Khat      K_true    Khat-K_true   l^2      1/(mbar l)")
    for x0 in (1.0, 2.5, 4.5):
        for mbar in (20.0, 40.0, 80.0, 160.0):
            ell = mbar ** (-1.0 / 3.0)
            a = 0.05 / mbar
            khat, ktrue, rho = estimate(mbar, ell, x0, a)
            print("%5.0f  %5.3f  %4.1f  %8.4f  %8.4f  %+9.4f     %6.4f   %6.4f"
                  % (mbar, ell, x0, khat, ktrue, khat - ktrue, ell ** 2, 1.0 / (mbar * ell)))
    print()
    print("fixed mbar = 80, x0 = 2.5, varying l")
    for ell in (0.1, 0.15, 0.2, 0.3, 0.4, 0.6):
        khat, ktrue, rho = estimate(80.0, ell, 2.5, 0.05 / 80.0)
        print("l = %4.2f  Khat = %8.4f  K_true = %8.4f  error = %+8.4f   l^2 = %6.4f  1/(mbar l) = %6.4f"
              % (ell, khat, ktrue, khat - ktrue, ell ** 2, 1.0 / (80.0 * ell)))


if __name__ == "__main__":
    main()
