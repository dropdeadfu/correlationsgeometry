#!/usr/bin/env python3
"""Entropic principle (P2) read as a CONSISTENCY of two reconstructions from the data, tested on an excited state
of the free node model (oscillators on the kernel graph).

Model (regular grid of nodes, spacing 1 = one node per unit volume, periodic box of n^D nodes, population-level
kernel): S(k) = prod_a theta(k_a) (periodised Gaussian of width xi, normalised to 1 at k = 0), L = (2/xi^2)(1 - S),
H = (1/2) sum p^2 + (1/2) x^T (L + m^2) x, omega(k)^2 = (2/xi^2)(1 - S(k)) + m^2 (long-wave speed 1).
Ground state: X0 = Omega^{-1}/2, P0 = Omega/2, Omega = (L + m^2)^{1/2}, all circulant (FFT).

Excitation (pure, Gaussian): squeeze of the localised mode b(w) = sum_i w_i (Omega^{1/2} phi + i Omega^{-1/2} pi)_i
/ sqrt2, w a normalised Gaussian bump of width ell centred at the origin; [b, b^+] = 1 and b|0> = 0.  With
g = Omega^{-1/2} w, f = Omega^{1/2} w the squeezed state U(s)|0>, U = exp(i s {phi(g'),pi(g')}/2-type generator)
has EXACTLY  X(s) = X0 + (e^{2s}-1)/2 g g^T,  P(s) = P0 + (e^{-2s}-1)/2 f f^T,  Y = 0;
to first order delta X = s g g^T, delta P = -s f f^T; total energy change (cosh 2s - 1)/2 <w,Omega w> (second order).
Second excitation (mixed, Gaussian): incoherent ("thermal") occupation n of the same mode b(w), exactly
X = X0 + n g g^T, P = P0 + n f f^T, Y = 0; energy change n <w,Omega w> > 0 at FIRST order.  Its global entropy
grows like n log(1/n), but the entropy of the ball is linear in n for n <~ 1e-4 (checked: dS/n at n = 1e-6 equals
dK to 1e-5).  Control: coherent displacement of b(w) (covariances unchanged: delta S = 0 and delta C_ij = 0 exactly,
delta<K> of second order = relative entropy, compared with Bisognano-Wichmann).  Robustness of the sign: thermal
occupation of a packet with a carrier wave, w = Gaussian(ell) * cos(k0 x_1), k0 = 3/ell (D = 2).

Quantities for a ball B = {|x| <= R} around the excitation (nodes of the grid):
  dS      = d/ds S(B) at s = 0 (exact entropies, central difference, s = 1e-3);
  dK      = d/ds <K_B> = (1/2) Tr(M_x dX) + (1/2) Tr(M_p dP), K_B = (1/2) x^T M_x x + (1/2) p^T M_p p the modular
            Hamiltonian of the reduced Gaussian state (first law: dS = dK);
  J       = 2 pi sum_{i in B} beta_i de_i, beta = (R^2 - r^2)/(2R) (Bisognano-Wichmann / Hislop-Longo weight),
            de_i = d/ds of the node energy density 1/2 p_i^2 + 1/2 m^2 x_i^2 + (1/2 xi^2) sum_j S_ij (x_i - x_j)^2
            (each bond split equally), plus the improvement term of the conformally coupled scalar
            -xi_c Laplacian <phi^2>, xi_c = (D-1)/(4D), integrated by parts: + 2 pi xi_c (D/R) sum_B d<x_i^2>
            (boundary terms of the integration by parts neglected).  J = dK would be the Jacobson/BW prediction.
  eta     = area-law coefficient of the same lattice model: entropy of half of the periodic box (two flat cuts),
            exact sum over the transverse grid momenta, divided by twice the cross-section.
Reconstruction (simplified version of the pipeline of the paper, stated exactly):
  data C_ij = mutual information of the single-node modes i, j (exact two-mode Gaussian formula, phi-pi
  correlations zero); vacuum profile F(r) = radial fit of ln C0 over all grid vectors with 1 <= |Delta| <= rfit
  (degree-4 polynomial in r); reconstructed distance d_rec = F^{-1}(C), so to first order
  delta d_ij = - dC_ij / F'(|Delta|), F' = C0(Delta) * (d ln F/dr)(|Delta|)   (profile inversion at fixed profile,
  the step "Assumption isotropic profile -> distances" of the paper; the diffusion-map pipeline itself is NOT run).
  Local conformal reading: psi_i(r0) = mean over pairs (i, i+Delta), |Delta| in [r0-1/2, r0+1/2), of delta d/d
  (the direction average of delta d/d equals (1/2D) tr delta g for any metric perturbation; the trace is all that
  volume and the area of a round sphere need at first order).  delta V_rec = D sum_{i in B} psi_i,
  delta A_rec = (D-1) A0 <psi>_{boundary shell |r - R| < 1/2}, A0 = 2 pi R (D = 2), 4 pi R^2 (D = 3);
  delta A_rec|_V = delta A_rec - ((D-1)/R) delta V_rec (area at fixed reconstructed volume).
  The same with the correlator profile X0(r) in place of the mutual information (d_rec from <phi_i phi_j>).
Two readings of the consistency:
 (Jacobson) entanglement equilibrium delta S(B)|_{V_rec} = eta delta A_rec|_V + delta S_exc = 0 with delta S_exc = dK
   (the excitation's entropy by the first law):  viol = (dK + eta dA_rec|_V)/dK  (0 = equilibrium, 1 = no geometric
   response); effective Newton constant G_eff := -dA_rec|_V/(4 dK), compared with G_ent = 1/(4 eta):
   G_eff/G_ent = -eta dA_rec|_V/dK = 1 - viol.  Einstein-like means: positive and independent of R.
 (naive) A_S := S(B)/eta equals A_rec at fixed V_rec:  c_naive = (dS - eta dA_rec|_V)/dS = 1 + G_eff/G_ent
   (dS = dK).  This reading is NOT the Jacobson condition (it demands that the geometry absorb the excitation's own
   entropy, with the opposite sign); printed for comparison.

Usage: entanglement_consistency_excitation.py        deterministic, no arguments; runtime about 1-2 minutes on 2
cores, peak memory below 1 GB (largest dense matrix about 2600 x 2600).
"""
import sys
import time
import numpy as np

S_FD = 1e-3          # central-difference step for dS/ds
H_CS = 1e-30         # complex-step size


def theta1(n, xi):
    j = (np.arange(n) + n // 2) % n - n // 2
    g = np.zeros(n)
    for w in range(-3, 4):
        g += np.exp(-(j + w * n) ** 2 / (2 * xi ** 2))
    th = np.fft.fft(g).real
    return th / th[0]


def fent(nu):
    nu = np.clip(nu, 0.5 + 1e-15, None)
    return (nu + 0.5) * np.log(nu + 0.5) - (nu - 0.5) * np.log(nu - 0.5)


def fent_c(nu):          # complex version for the complex step
    return (nu + 0.5) * np.log(nu + 0.5) - (nu - 0.5) * np.log(nu - 0.5)


def entropy(X, P):
    Lc = np.linalg.cholesky(P)
    ev = np.linalg.eigvalsh(Lc.T @ X @ Lc)
    return float(np.sum(fent(np.sqrt(np.clip(ev, 0.25, None)))))


def modular(X, P):
    """K = (1/2) x^T Mx x + (1/2) p^T Mp p for the Gaussian state (X, P, Y = 0)."""
    ex, Ux = np.linalg.eigh(X)
    Xh = (Ux * np.sqrt(ex)) @ Ux.T
    Xmh = (Ux / np.sqrt(ex)) @ Ux.T
    c, V = np.linalg.eigh(Xh @ P @ Xh)
    nu = np.sqrt(np.clip(c, 0.25 + 1e-16, None))
    eps = np.log((nu + 0.5) / (nu - 0.5))
    A = Xmh @ V
    B = Xh @ V
    return (A * (nu * eps)) @ A.T, (B * (eps / nu)) @ B.T


def coords(n, D):
    c1 = (np.arange(n) + n // 2) % n - n // 2
    return np.meshgrid(*([c1] * D), indexing='ij')


def setup(D, n, xi, m):
    th = theta1(n, xi)
    Sk = np.ones((n,) * D)
    for a in range(D):
        sh = [1] * D; sh[a] = n
        Sk = Sk * th.reshape(sh)
    om = np.sqrt((2 / xi ** 2) * (1 - Sk) + m * m)
    return om, Sk, np.fft.ifftn(0.5 / om).real, np.fft.ifftn(0.5 * om).real


def block(c, idx, n, D):
    lin = np.zeros((len(idx), len(idx)), dtype=np.int64)
    for a in range(D):
        lin = lin * n + (idx[:, a][:, None] - idx[:, a][None, :]) % n
    return c.reshape(-1)[lin]


def mi2(xi_, xj_, pi_, pj_, x, p, cplx=False):
    """Mutual information of two modes, covariances [[xi,x],[x,xj]], [[pi,p],[p,pj]], no phi-pi correlation."""
    t = xi_ * pi_ + 2 * x * p + xj_ * pj_
    d = (xi_ * xj_ - x * x) * (pi_ * pj_ - p * p)
    sq = np.sqrt(t * t - 4 * d)
    fe = fent_c if cplx else fent
    return fe(np.sqrt(xi_ * pi_)) + fe(np.sqrt(xj_ * pj_)) - fe(np.sqrt((t + sq) / 2)) - fe(np.sqrt((t - sq) / 2))


def eta_lattice(D, n, xi, m):
    th = theta1(n, xi)
    idx = np.arange(n)
    phase = np.exp(2j * np.pi * np.outer(idx, idx) / n)
    half = n // 2
    if D == 2:
        perp = [(th[k], 1) for k in range(n)]
    else:
        perp = [(th[k2] * th[k3], 1 if k3 == k2 else 2) for k2 in range(n) for k3 in range(k2, n)]
    S = 0.0
    cache = {}
    for tp, mult in perp:
        key = round(float(tp), 14)
        if key not in cache:
            om = np.sqrt((2 / xi ** 2) * (1 - th * tp) + m * m)
            X = ((phase * (0.5 / om)[None, :]) @ phase.conj().T / n).real[:half, :half]
            Pm = ((phase * (0.5 * om)[None, :]) @ phase.conj().T / n).real[:half, :half]
            cache[key] = entropy(X, Pm)
        S += mult * cache[key]
    return S / (2 * n ** (D - 1))


class Model:
    def __init__(self, D, n, xi, m, ell, k0=0.0):
        self.D, self.n, self.xi, self.m, self.ell = D, n, xi, m, ell
        self.om, self.Sk, self.cx, self.cp = setup(D, n, xi, m)
        C = coords(n, D)
        self.C = C
        self.r2 = sum(ci.astype(float) ** 2 for ci in C)
        w = np.exp(-self.r2 / (2 * ell ** 2)) * np.cos(k0 * C[0])
        w /= np.sqrt(np.sum(w ** 2))
        wh = np.fft.fftn(w)
        self.w = w
        self.g = np.fft.ifftn(wh / np.sqrt(self.om)).real
        self.f = np.fft.ifftn(wh * np.sqrt(self.om)).real
        self.wOw = float(np.sum(np.abs(wh) ** 2 * self.om) / n ** D)
        conv = lambda a: np.fft.ifftn(np.fft.fftn(a) * self.Sk).real
        self.conv = conv
        self.c0x, self.c0p = self.cx.reshape(-1)[0], self.cp.reshape(-1)[0]
        self._profile()

    def eL(self, a):
        """bond energy density of a classical configuration / rank-one covariance a a^T (per unit amplitude^2)"""
        return (1 / (2 * self.xi ** 2)) * (a * a - 2 * a * self.conv(a) + self.conv(a * a)) + 0.5 * self.m ** 2 * a * a

    def _profile(self, rfit=9.0):
        D, n = self.D, self.n
        rng = np.arange(-int(rfit) - 1, int(rfit) + 2)
        vecs = np.array(np.meshgrid(*([rng] * D), indexing='ij')).reshape(D, -1).T
        r = np.sqrt((vecs ** 2).sum(1))
        sel = (r >= 1) & (r <= rfit)
        vecs, r = vecs[sel], r[sel]
        lin = np.zeros(len(vecs), dtype=np.int64)
        for a in range(D):
            lin = lin * n + vecs[:, a] % n
        x = self.cx.reshape(-1)[lin]; p = self.cp.reshape(-1)[lin]
        C0 = mi2(self.c0x, self.c0x, self.c0p, self.c0p, x, p)
        self.pC = np.polyfit(r, np.log(C0), 4)
        self.pX = np.polyfit(r, np.log(x), 4)
        resC = np.log(C0) - np.polyval(self.pC, r)
        self.anisoC = float(np.max(np.abs(resC)))
        self.vec_all, self.r_all, self.lin_all, self.C0_all, self.x_all, self.p_all = vecs, r, lin, C0, x, p

    def response(self, R, sp, r0s):
        """psi_i for the MI and correlator profiles for delta X = g g^T, delta P = sp f f^T (per unit parameter);
        returns dV, dA, dA|_V, psi(0) for each r0."""
        D, n = self.D, self.n
        out = {}
        sel_nodes = self.r2 <= (R + 1.0) ** 2
        nodes = np.stack([ci[sel_nodes] for ci in self.C], 1)
        rn = np.sqrt(self.r2[sel_nodes])
        gi = self.g[sel_nodes]; fi = self.f[sel_nodes]
        for r0 in r0s:
            sh = (self.r_all >= r0 - 0.5) & (self.r_all < r0 + 0.5)
            vecs, rr = self.vec_all[sh], self.r_all[sh]
            x0 = self.x_all[sh]; p0 = self.p_all[sh]; C0 = self.C0_all[sh]
            dlnF = np.polyval(np.polyder(self.pC), rr)
            dlnX = np.polyval(np.polyder(self.pX), rr)
            psiC = np.zeros(len(nodes)); psiX = np.zeros(len(nodes))
            for k in range(len(nodes)):
                jj = (nodes[k][None, :] + vecs) % n
                lin = np.zeros(len(vecs), dtype=np.int64)
                for a in range(D):
                    lin = lin * n + jj[:, a]
                gj = self.g.reshape(-1)[lin]; fj = self.f.reshape(-1)[lin]
                h = 1j * H_CS
                Cc = mi2(self.c0x + h * gi[k] ** 2, self.c0x + h * gj ** 2, self.c0p + sp * h * fi[k] ** 2,
                         self.c0p + sp * h * fj ** 2, x0 + h * gi[k] * gj, p0 + sp * h * fi[k] * fj, cplx=True)
                dC = Cc.imag / H_CS
                dd = dC / (C0 * dlnF)              # F(d + dd) = C + dC
                psiC[k] = np.mean(dd / rr)
                ddx = (gi[k] * gj) / (x0 * dlnX)
                psiX[k] = np.mean(ddx / rr)
            inB = rn <= R
            shell = np.abs(rn - R) < 0.5
            A0 = 2 * np.pi * R if D == 2 else 4 * np.pi * R * R
            res = {}
            for name, psi in (('MI', psiC), ('X', psiX)):
                dV = D * np.sum(psi[inB])
                dA = (D - 1) * A0 * np.mean(psi[shell])
                res[name] = (dV, dA, dA - (D - 1) / R * dV, float(psi[rn < 0.5][0]) if np.any(rn < 0.5) else np.nan)
            out[r0] = res
        return out

    def ball(self, R):
        D, n = self.D, self.n
        inB = self.r2 <= R * R
        idx = np.stack([ci[inB] % n for ci in self.C], 1)
        XA = block(self.cx, idx, n, D); PA = block(self.cp, idx, n, D)
        gA, fA = self.g[inB], self.f[inB]
        S0 = entropy(XA, PA)
        Mx, Mp = modular(XA, PA)
        Kx = 0.5 * gA @ Mx @ gA; Kp = 0.5 * fA @ Mp @ fA
        beta = (R * R - self.r2[inB]) / (2 * R)
        xic = (D - 1) / (4 * D)
        Jx = 2 * np.pi * np.sum(beta * self.eL(self.g)[inB]) + 2 * np.pi * xic * (D / R) * np.sum(gA ** 2)
        Jp = 2 * np.pi * np.sum(beta * 0.5 * fA ** 2)
        # squeeze (pure): exact covariances, central difference
        sq = lambda s: entropy(XA + 0.5 * np.expm1(2 * s) * np.outer(gA, gA), PA + 0.5 * np.expm1(-2 * s) * np.outer(fA, fA))
        dS_sq = (sq(S_FD) - sq(-S_FD)) / (2 * S_FD)
        # incoherent occupation n (mixed): exact covariances X0 + n g g^T, P0 + n f f^T
        mix = lambda nn: (entropy(XA + nn * np.outer(gA, gA), PA + nn * np.outer(fA, fA)) - S0) / nn
        dS_mix = {nn: mix(nn) for nn in (1e-2, 1e-4, 1e-6)}
        return dict(nA=int(inB.sum()), S0=S0, Kx=Kx, Kp=Kp, Jx=Jx, Jp=Jp, dS_sq=dS_sq, dS_mix=dS_mix,
                    Mx=Mx, Mp=Mp, gA=gA, fA=fA, beta=beta, inB=inB)


EXC = (('squeeze', -1.0), ('thermal', +1.0))


def run_config(D, n, xi, m, ell, radii, r0fac=(4 / 3, 2.0, 8 / 3), controls=True, k0=0.0, exc=None):
    t0 = time.time()
    M = Model(D, n, xi, m, ell, k0)
    eta = eta_lattice(D, n, xi, m)
    r0s = tuple(round(c * xi * 2) / 2 for c in r0fac)
    print(f"=== D = {D}: grid {n}^{D}, xi = {xi}, m = {m}, ell = {ell} (ell/xi = {ell / xi:.2f}), carrier k0 = {k0:.4f}; eta = {eta:.6f} "
          f"(eta xi^{D - 1} = {eta * xi ** (D - 1):.5f}); <w,Omega w> = {M.wOw:.5f}; pair distances r0 = {r0s}; "
          f"max |ln C0 - radial fit| (1<=r<=9) = {M.anisoC:.3f}", flush=True)
    rows = []
    for R in radii:
        t1 = time.time()
        b = M.ball(R)
        A0 = 2 * np.pi * R if D == 2 else 4 * np.pi * R * R
        print(f"  R = {R:5.2f} (R/ell = {R / ell:.2f}, R/xi = {R / xi:.1f}, {b['nA']} nodes): S0 = {b['S0']:.4f}, "
              f"S0/(eta A0) = {b['S0'] / (eta * A0):.3f}", flush=True)
        for name, sp in (exc or EXC):
            dK = b['Kx'] + sp * b['Kp']
            J = b['Jx'] + sp * b['Jp']
            if name == 'squeeze':
                fl = f"dS/ds = {b['dS_sq']:+.6e}, dK = {dK:+.6e}, ratio {b['dS_sq'] / dK:.6f}"
            else:
                fl = ("dS/n = " + ", ".join(f"{v:.6f} (n={k:.0e})" for k, v in b['dS_mix'].items())
                      + f", dK = {dK:.6f}, ratio(n=1e-6) {b['dS_mix'][1e-6] / dK:.6f}; dE/n = {M.wOw:.5f}")
            print(f"    [{name}] first law: {fl}", flush=True)
            print(f"    [{name}] BW: J = {J:+.5e}, J/dK = {J / dK:.4f} (parts K_x/J_x = {b['Kx'] / b['Jx']:.4f}, "
                  f"K_p/J_p = {b['Kp'] / b['Jp']:.4f})", flush=True)
            resp = M.response(R, sp, r0s)
            for r0, res in resp.items():
                for dn in ('MI', 'X'):
                    dV, dA, dAV, psi0 = res[dn]
                    G = -eta * dAV / dK
                    print(f"    [{name}] data {dn:2s} r0 = {r0:4.1f}: psi(0) = {psi0:+.4e}, dV_rec = {dV:+.5e}, "
                          f"dA_rec = {dA:+.5e}, dA_rec|_V = {dAV:+.5e}, viol = {1 - G:+.4f}, c_naive = {1 + G:+.4f}, "
                          f"G_eff/G_ent = {G:+.4f} (with J: {-eta * dAV / J:+.4f})", flush=True)
                    rows.append((D, xi, ell, R, name, dn, r0, dK, J, dAV, G))
        print(f"    [{time.time() - t1:.0f} s]", flush=True)
    if controls:
        R = radii[len(radii) // 2]
        b = M.ball(R)
        # coherent displacement of b(w): alpha real: <phi> = sqrt2 alpha g; alpha imaginary: <pi> = sqrt2 |alpha| f
        dKc_x = b['gA'] @ b['Mx'] @ b['gA']; dKc_p = b['fA'] @ b['Mp'] @ b['fA']
        print(f"  control coherent b(w), R = {R}: delta S = 0 and delta C_ij = 0 exactly (covariances unchanged), hence "
              f"dA_rec = 0 and viol = 1; per |alpha|^2: delta<K> = {dKc_x:.5f} (real alpha), {dKc_p:.5f} (imag. alpha); "
              f"BW 2pi int beta delta T00 = {2 * b['Jx']:.5f}, {2 * b['Jp']:.5f}; total energy {M.wOw:.5f}", flush=True)
    print(f"  [D = {D} config done, {time.time() - t0:.0f} s]\n", flush=True)
    return rows, eta


def main():
    t00 = time.time()
    print(__doc__.split('\n')[0])
    print("units: grid spacing 1, one node per unit volume; all deltas per unit excitation parameter (s or n)\n")
    allrows = []
    for cfg in [
        (2, 128, 1.5, 0.02, 8.0, [4.0, 6.0, 8.0, 10.0, 12.0, 16.0, 20.0, 28.0]),
        (2, 192, 2.25, 0.0133, 12.0, [12.0]),          # denser nodes, same ell/xi (finite-density check)
        (2, 192, 1.5, 0.0133, 12.0, [12.0]),           # larger ell/xi (continuum check)
        (3, 48, 1.2, 0.04, 4.0, [3.0, 4.0, 5.0, 6.0, 8.5]),
        (3, 48, 1.2, 0.04, 6.0, [6.0]),                # larger ell/xi
    ]:
        rows, _ = run_config(*cfg, controls=(cfg[5] != [12.0] and cfg[5] != [6.0]))
        allrows += rows
    rows, _ = run_config(2, 128, 1.5, 0.02, 8.0, [8.0, 12.0], controls=False, k0=3 / 8.0, exc=(('thermal', +1.0),))
    allrows += [r[:4] + ('thermal k0',) + r[5:] for r in rows]
    print("summary (MI data, middle pair distance r0): D  xi  ell  R  R/ell  excitation  dK  J  dA_rec|_V  G_eff/G_ent")
    for D, xi, ell, R, name, dn, r0, dK, J, dAV, G in allrows:
        if dn == 'MI' and abs(r0 - round(2 * xi * 2) / 2) < 1e-9:
            print(f"  {D}  {xi:4.2f}  {ell:4.1f}  {R:5.2f}  {R / ell:4.2f}  {name:8s}  {dK:+.4e}  {J:+.4e}  {dAV:+.4e}  {G:+.4f}")
    print(f"total runtime {time.time() - t00:.0f} s")


if __name__ == '__main__':
    main()
