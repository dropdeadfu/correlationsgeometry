"""Subtracted heat trace of the sampled graph with and without self-loops, flat 2-torus, Gaussian kernel.

For the same samples the subtracted trace Tr e^{-tL} - N e^{-tau} is computed once with the diagonal of the
kernel kept and once with the diagonal removed, and compared with the population value T_sigma. The
difference is compared with the first-order prediction from Proposition "The bias of the normalised walk
at a fixed kernel scale", sum_k w_k (beta_k - beta_k^{rho=0})/N plus the term w_1 m_1 of order one, and
with the time rescaling -(M/N) tau dT_sigma/dtau. Fixed seed, twelve samples; not evidence for a rate.
"""
import numpy as np
from math import lgamma, log, exp
def heat0(t,d=2,cut=60):
    n=np.arange(-cut,cut+1); return (np.exp(-4*np.pi**2*n**2*t).sum())**d
rng=np.random.default_rng(31)
N=1500; xi=0.05; sig=xi**2/2; reps=12; taus=[5,10,20,40,80]
M=heat0(sig); m=lambda k: heat0(k*sig)
obs={t:[] for t in taus}
for _ in range(reps):
    X=rng.random((N,2)); K=np.ones((N,N))
    for c in range(2):
        dx=X[:,None,c]-X[None,:,c]; K*=sum(np.exp(-(dx+a)**2/(2*xi**2)) for a in (-1,0,1))
    sp=[]
    for loops in (True,False):
        Kc=K.copy()
        if not loops: np.fill_diagonal(Kc,0)
        q=Kc.sum(1)/N; W=Kc/np.outer(q,q); D=W.sum(1); sp.append(np.linalg.eigvalsh(W/np.sqrt(np.outer(D,D))))
    for t in taus:
        f=lambda s: np.exp(-t*(1-s)).sum()-N*np.exp(-t)
        obs[t].append((f(sp[0]),f(sp[1])))
lam=4*np.pi**2*np.add.outer(np.arange(-80,81)**2,np.arange(-80,81)**2).ravel(); s=np.exp(-sig*lam)
print(f"N={N} xi={xi} M={M:.2f} M/N={M/N:.5f} samples={reps}")
for t in taus:
    a=np.array(obs[t]); diff=a[:,0]-a[:,1]
    T=(np.exp(-t*(1-s))-np.exp(-t)).sum(); dT=(-(1-s)*np.exp(-t*(1-s))+np.exp(-t)).sum()
    w=lambda k: exp(-t+k*log(t)-lgamma(k+1))
    # exact first-order prediction from beta_k - beta_k^{rho=0}, plus the order-one term k=1
    pred=w(1)*M + (w(2)*(M*M-2*M*m(2)) + sum(w(k)*k*M*(m(k-1)-m(k)) for k in range(3,int(t+12*np.sqrt(t)+20))))/N
    resc=-(M/N)*t*dT
    th=np.exp(-lam*t*sig).sum()
    print(f" tau={t:3d}: T_sigma={T:8.3f} | with loops {a[:,0].mean():8.3f}, without {a[:,1].mean():8.3f} | difference {diff.mean():+.4f} ({diff.std()/np.sqrt(reps):.4f}) | predicted {pred:+.4f} | time rescaling -(M/N) tau dT/dtau = {resc:+.4f} | rel. dev. from T_sigma: with {a[:,0].mean()/T-1:+.4f}, without {a[:,1].mean()/T-1:+.4f}")
