"""L1 form of the kernel bound and the remainder of the reduction, for one sample on the flat torus.

Usage: python l1_kernel_check.py d xi N K seed   (e.g. 3 0.2 1500 24 1)
Prints, for k = 1..K: the entrywise error of P^k divided by delta' sqrt(k) m_k, the largest column and row
mean of |N P^k - p_k| divided by delta' sqrt(k) (Lemma lem:kernel-l1 in second-session/l1_kernel_lemma.tex),
the relative trace error, Pi_k, and the remainder of Proposition prop:reduction divided by delta'^2 k m_(k+1).
Needs numpy. Single runs; not evidence for a rate.
"""
import sys, numpy as np
d=int(sys.argv[1]); xi=float(sys.argv[2]); N=int(sys.argv[3]); K=int(sys.argv[4]); seed=int(sys.argv[5])
rng=np.random.default_rng(seed)
x=rng.random((N,d))
def p1(w,t):
    n=np.arange(-6,7)
    return sum(np.exp(-(w+k)**2/(2*t)) for k in n)/np.sqrt(2*np.pi*t)
def Q(m):
    t=m*xi*xi
    out=np.ones((N,N))
    for c in range(d):
        w=x[:,c][:,None]-x[:,c][None,:]
        w=w-np.round(w)
        out*=p1(w,t)
    return out
def m0(m):
    return float(p1(np.array(0.0),m*xi*xi))**d
M=m0(1); dp=np.sqrt(M*np.log(N)/N)
Qs={m:Q(m) for m in range(1,K+2)}
Pt=Qs[1]/N
eps=Pt.sum(1)-1; u=1/(1+eps); r=Pt@u
P=Pt*u[None,:]/r[:,None]
delta=np.abs(eps).max()
print(f"d={d} xi={xi} N={N} M={M:.3f} delta'={dp:.4f} delta={delta:.4f}")
th1=-eps[None,:]-eps[:,None]+(Pt@eps)[:,None]   # [b,i]
rh=Pt@(1-eps)
hh={m:(Pt*(1-eps)[None,:])@Qs[m]-rh[:,None]*Qs[m+1] for m in range(1,K+1)}  # [b,i]
Pk=np.eye(N)
for k in range(1,K+1):
    Pk=Pk@P   # P^k
    Dk=np.abs(N*Pk-Qs[k]).max()/m0(k)
    L1=np.abs(N*Pk-Qs[k]).mean(0).max()   # column: mean over a, max over i
    L1r=np.abs(N*Pk-Qs[k]).mean(1).max()
    tr=np.trace(Pk@P)                      # Tr P^{k+1}
    Pi=(Qs[k]*Qs[1].T*th1.T).sum()/N**2    # sum_{i,b} Q_k[i,b] Q_1[b,i] th1[b,i]
    for m in range(1,k):
        Pi+=(Qs[k-m]*hh[m].T).sum()/N**2
    Pi+=np.trace(hh[k])/N
    rem=tr-m0(k+1)-Pi
    print(f"k={k:2d} D_k/(dp sqrt k m_k)={Dk/(dp*np.sqrt(k)):.3f}  L1col/(dp sqrt k)={L1/(dp*np.sqrt(k)):.3f} L1row={L1r/(dp*np.sqrt(k)):.3f}  (TrP^(k+1)-m)/m={ (tr-m0(k+1))/m0(k+1):+.5f} Pi/m={Pi/m0(k+1):+.5f} rem/(dp^2 k m_(k+1))={rem/(dp*dp*k*m0(k+1)):+.4f}")
