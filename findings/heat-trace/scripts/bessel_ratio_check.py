"""z (K_1(z)/K_0(z) - 1) for the constant c_0 of Proposition "Stability of the estimator under
errors of the distances" (Appendix H).  K_nu(z) = int_0^inf exp(-z cosh t) cosh(nu t) dt, by the
trapezoidal rule on a fine grid (the integrand is smooth and decays doubly exponentially).
Expected: values between 0 and 1/2, increasing to 1/2 (K_1/K_0 = 1 + 1/(2z) - 1/(8z^2) + ...).
"""
import numpy as np

def K(nu, z):
    tmax = np.arccosh(1 + 60.0 / z)
    t = np.linspace(0.0, tmax, 400001)
    y = np.exp(-z * np.cosh(t)) * np.cosh(nu * t)
    return (t[1] - t[0]) * (y.sum() - 0.5 * (y[0] + y[-1]))

zs = [0.01, 0.05, 0.25, 0.5, 1, 2, 5, 20, 100]
vals = [z * (K(1, z) / K(0, z) - 1) for z in zs]
for z, v in zip(zs, vals):
    print(f"z={z:7.2f}   z (K1/K0 - 1) = {v:.4f}")
grid = np.exp(np.linspace(np.log(0.01), np.log(100), 400))
g = np.array([z * (K(1, z) / K(0, z) - 1) for z in grid])
print(f"on 400 log-spaced points in [0.01, 100]: min = {g.min():.4f}, max = {g.max():.4f}, "
      f"increasing: {bool(np.all(np.diff(g) > 0))}")
