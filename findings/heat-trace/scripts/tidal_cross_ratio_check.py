"""Check of Proposition "four nodes in general position" (Appendix H).

Flat reconstructed metric in D = 2 (so that normal coordinates are Cartesian and u_0 = 1),
lapse Omega(x, y) = 1 + 0.2 sin x + 0.1 cos y + 0.15 x y.  For four random points in the ball of
radius ell about o the leading-order cross-ratio rho_Theta = Theta_ad Theta_bc / (Theta_ac Theta_bd),
Theta(x, y) = r / (Omega(x) Omega(y) T(x, y)), T = int along the segment of Omega^-2, is compared
with E_o(p_b - p_a, p_d - p_c) / 3, E = -Hess Omega / Omega.  Deterministic quadrature, fixed seed.
The model error of Theorem vargap(b) is NOT part of this check.
"""
import numpy as np

def Om(p):
    x, y = p[..., 0], p[..., 1]
    return 1 + 0.2 * np.sin(x) + 0.1 * np.cos(y) + 0.15 * x * y

def E_at(o):
    x, y = o
    H = np.array([[-0.2 * np.sin(x), 0.15], [0.15, -0.1 * np.cos(y)]])
    return -H / Om(np.array(o))

xg, wg = np.polynomial.legendre.leggauss(40)
xg = 0.5 * (xg + 1); wg = 0.5 * wg

def Theta(p, q):
    r = np.linalg.norm(q - p)
    pts = p[None, :] + xg[:, None] * (q - p)[None, :]
    T = r * np.sum(wg / Om(pts) ** 2)
    return r / (Om(p) * Om(q) * T)

rng = np.random.default_rng(7)
o = np.array([0.4, -0.3]); E = E_at(o)
print("E_o =", np.round(E, 6).tolist())
for ell in [0.4, 0.2, 0.1, 0.05, 0.025]:
    errs = []; sizes = []
    for _ in range(200):
        P = o + ell * rng.uniform(-1, 1, size=(4, 2)) / np.sqrt(2)
        a, b, c, d = P
        lr = np.log(Theta(a, d) * Theta(b, c) / (Theta(a, c) * Theta(b, d)))
        pred = (b - a) @ E @ (d - c) / 3
        errs.append(abs(lr - pred)); sizes.append(abs(pred))
    print(f"ell={ell:6.3f}  max|log rho - E(b-a,d-c)/3| = {max(errs):.3e}"
          f"  (/ell^3 = {max(errs)/ell**3:.3f})   median |E(b-a,d-c)/3| = {np.median(sizes):.3e}")
