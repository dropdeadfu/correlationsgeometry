"""Variance of Tr P^k for the walk with the estimated normalisation, flat d-torus, Gaussian kernel.

Compares N times the sample standard deviation of Tr P^k (graph with self-loops) with sqrt(v_k) from
Proposition "The variance of the normalised walk at a fixed kernel scale":
    v_k = 1/2 sum_{n != 0} Ghat_k(n)^2,   Ghat_k(n) = k (1-a_n)^4 Gammahat_k(n) - 2 k mu_k a_n (1-a_n)^3,
    a_n = exp(-sigma lambda_n),   Gammahat_k(n) = sum_{l=1}^{k-1} (a^l * a^(k-l))(n)   (convolution on Z^d).
The number in brackets after the observed value is its statistical error, sd/sqrt(2 samples).
Fixed seed; the constants of the proposition are not uniform in k and M, and the observed values exceed
sqrt(v_k) by an amount that grows with M/N.
"""
import numpy as np
def heat0(t,d,cut=60):
    n=np.arange(-cut,cut+1); return (np.exp(-4*np.pi**2*n**2*t).sum())**d
def vk(k,sig,d,loops):
    w=4*np.pi**2*sig; cut=int(np.sqrt(45.0/w))+2; n=np.arange(-cut,cut+1)
    if d==1: a=np.exp(-w*n**2)
    elif d==2: a=np.exp(-w*(n[:,None]**2+n[None,:]**2))
    else: a=np.exp(-w*(n[:,None,None]**2+n[None,:,None]**2+n[None,None,:]**2))
    # Gamma-hat(n) = sum_l (a^l conv a^(k-l))(n): convolution on Z^d via FFT (zero-padded)
    shape=[2*len(n)]*d
    F=lambda x: np.fft.fftn(x,shape)
    G=np.zeros(shape)
    for l in range(1,k):
        G+=np.real(np.fft.ifftn(F(a**l)*F(a**(k-l))))
    # indices of full convolution: n1+n2 ranges -2cut..2cut at offsets 0..4cut ; pad a to same grid
    A=np.zeros(shape); sl=tuple(slice(cut,cut+len(n)) for _ in range(d)); A[sl]=a
    mu=heat0(k*sig,d) if k>=2 else (heat0(sig,d) if loops else 0.0)
    Gh=k*(1-A)**4*G-2*k*mu*A*(1-A)**3
    zero=tuple([2*cut]*d)
    # outside the support of the padded grid a_n ~ 0 and Gamma-hat ~ 0, fine
    tot=(Gh**2).sum()-Gh[zero]**2
    return 0.5*tot, Gh[zero]
def mc(d,N,xi,reps,ks,loops,rng):
    out=[]
    for _ in range(reps):
        X=rng.random((N,d)); K=np.ones((N,N))
        for c in range(d):
            dx=X[:,None,c]-X[None,:,c]; K*=sum(np.exp(-(dx+a)**2/(2*xi**2)) for a in (-1,0,1))
        if not loops: np.fill_diagonal(K,0)
        q=K.sum(1)/N; W=K/np.outer(q,q); D=W.sum(1); s=np.linalg.eigvalsh(W/np.sqrt(np.outer(D,D)))
        out.append([(s**k).sum() for k in ks])
    return np.array(out)
ks = [1, 2, 4, 8, 16]
for d, xi, N, reps in [(2, 0.15, 800, 600), (2, 0.15, 1600, 300), (2, 0.08, 500, 400), (2, 0.08, 1000, 200), (1, 0.03, 600, 800)]:
    sig = xi**2 / 2
    tr = mc(d, N, xi, reps, ks, True, np.random.default_rng(41))
    print(f"d={d} xi={xi} N={N} M/N={heat0(sig, d)/N:.5f} samples={reps}")
    for j, k in enumerate(ks):
        v, g0 = vk(k, sig, d, True)
        sd = tr[:, j].std(ddof=1)
        print(f"   k={k:2d}  N*sd observed {N*sd:8.3f} ({N*sd/np.sqrt(2*reps):.3f})   sqrt(v_k) = {np.sqrt(v):8.3f}")

print("c_k = v_k / (M m_k^2), d=2 (flat regime k sigma << 1):")
for xi in (0.05, 0.025):
    sig = xi**2 / 2
    M = heat0(sig, 2)
    print(f"   xi={xi}: " + "  ".join(f"k={k}: {vk(k, sig, 2, True)[0] / (M * heat0(k*sig, 2)**2):.3f}" for k in ks))
