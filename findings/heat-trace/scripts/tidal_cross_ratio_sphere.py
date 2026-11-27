"""Check of the step "Normal coordinates" in Proposition "four nodes in general position"
(Appendix H) on a CURVED reconstructed metric: the unit sphere S^2.

Lapse: restriction of f(x) = 1 + 0.2 x1 + 0.1 x2 x3 + 0.15 x1 x2 to the sphere.
E = -Hess f / f with the Hessian of the sphere, Hess(u, w) = D^2 f(u, w) - (grad f . x) <u, w>
for tangent u, w at x.  Positions p_x = exp_o^{-1}(x).  Second length T along great-circle arcs
by Gauss quadrature.  Compared: log(Theta_ad Theta_bc / (Theta_ac Theta_bd)) with
E_o(p_b - p_a, p_d - p_c) / 3.  Deterministic, fixed seed.  The model error of Theorem vargap(b)
and the Van Vleck factor are NOT part of this check.
"""
import numpy as np

def f(x):
    return 1 + 0.2 * x[..., 0] + 0.1 * x[..., 1] * x[..., 2] + 0.15 * x[..., 0] * x[..., 1]

def grad(x):
    return np.array([0.2 + 0.15 * x[1], 0.1 * x[2] + 0.15 * x[0], 0.1 * x[1]])

D2 = np.array([[0, 0.15, 0], [0.15, 0, 0.1], [0, 0.1, 0]])

o = np.array([0.3, -0.5, 0.0]); o[2] = np.sqrt(1 - o @ o)
e1 = np.cross(o, [0, 0, 1.0]); e1 /= np.linalg.norm(e1); e2 = np.cross(o, e1)
B = np.stack([e1, e2])                      # orthonormal frame of T_o
E = -(B @ D2 @ B.T - (grad(o) @ o) * np.eye(2)) / f(o)

xg, wg = np.polynomial.legendre.leggauss(40); xg = 0.5 * (xg + 1); wg = 0.5 * wg

def expo(p):                                # exp_o of tangent vector with frame components p
    v = p @ B; t = np.linalg.norm(v)
    return np.cos(t) * o + np.sin(t) * v / t

def Theta(x, y):
    r = np.arccos(np.clip(x @ y, -1, 1))
    s = xg * r
    pts = (np.sin(r - s)[:, None] * x[None, :] + np.sin(s)[:, None] * y[None, :]) / np.sin(r)
    T = r * np.sum(wg / f(pts) ** 2)
    return r / (f(x) * f(y) * T)

rng = np.random.default_rng(11)
print("E_o =", np.round(E, 6).tolist())
for ell in [0.4, 0.2, 0.1, 0.05, 0.025]:
    errs = []; sizes = []
    for _ in range(200):
        P = ell * rng.uniform(-1, 1, size=(4, 2)) / np.sqrt(2)
        a, b, c, d = (expo(p) for p in P)
        lr = np.log(Theta(a, d) * Theta(b, c) / (Theta(a, c) * Theta(b, d)))
        pred = (P[1] - P[0]) @ E @ (P[3] - P[2]) / 3
        errs.append(abs(lr - pred)); sizes.append(abs(pred))
    print(f"ell={ell:6.3f}  max|log rho - E(b-a,d-c)/3| = {max(errs):.3e}"
          f"  (/ell^3 = {max(errs)/ell**3:.3f})   median |E(b-a,d-c)/3| = {np.median(sizes):.3e}")
