"""Population side of the sharp rate on the flat torus R^d/Z^d (Theorem `thm:rate`, eq. (rateexact)).

Checks the size of the term called O(sigma) after eq. (rateexact):
    T_sigma(t)/Theta(t) - 1 = (sigma/2t) * t^2 Theta''(t)/Theta(t) + O((sigma/t)^2) + ...
with Theta(t) = sum_n exp(-t 4 pi^2 |n|^2), T_sigma(t) = sum_n [exp(-tau(1-exp(-sigma lam_n))) - exp(-tau)],
tau = t/sigma.  The leading coefficient d(d+2)/8 * sigma/t is the small-t value of
(sigma/2t) * t^2 Theta''/Theta; for t of order one on the unit torus t^2 Theta''/Theta tends to 0.
Deterministic (no sampling).  Output: a table for d = 1, 2.
"""
import itertools
import numpy as np

def lam_list(d, nmax):
    r = np.arange(-nmax, nmax + 1)
    g = np.array(list(itertools.product(r, repeat=d)), dtype=float)
    return 4 * np.pi ** 2 * (g ** 2).sum(axis=1)

def theta(lam, t):
    return np.exp(-t * lam).sum()

def theta2(lam, t):
    return (lam ** 2 * np.exp(-t * lam)).sum()

def T_sigma(lam, sigma, t):
    tau = t / sigma
    # exp(-tau(1-a)) - exp(-tau) computed stably
    a = np.exp(-sigma * lam)
    return (np.exp(-tau) * np.expm1(tau * a)).sum()

for d, nmax in ((1, 4000), (2, 250)):
    lam = lam_list(d, nmax)
    lead = d * (d + 2) / 4
    print(f"d = {d}:  d(d+2)/4 = {lead}")
    print("     t     t^2 Theta''/Theta   sigma    T_sigma/Theta - 1    d(d+2)/(8 tau)")
    for t in (0.003125, 0.0125, 0.05, 0.1, 0.2, 0.5, 1.0):
        sigma = t / 200.0
        th = theta(lam, t)
        ratio = t ** 2 * theta2(lam, t) / th
        dev = T_sigma(lam, sigma, t) / th - 1
        print(f"  {t:8.6f}   {ratio:12.6f}   {sigma:9.3e}   {dev:14.6e}   {lead / 2 * sigma / t:12.6e}")
