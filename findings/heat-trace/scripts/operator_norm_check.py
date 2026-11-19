"""Operator norm of S^k - Q_k for one sample on the flat torus, against delta' sqrt(k) and delta' sqrt(k) m_k.

Usage: python operator_norm_check.py d xi N seed   (e.g. 2 0.1 2500 3)
See the second consequence in second-session/l1_kernel_lemma.tex. Needs numpy. Single runs; not evidence
for a rate.
"""
import sys, numpy as np
d=int(sys.argv[1]); xi=float(sys.argv[2]); N=int(sys.argv[3]); seed=int(sys.argv[4])
rng=np.random.default_rng(seed); x=rng.random((N,d)); sig=xi*xi/2
def p1(w,t):
    return sum(np.exp(-(w+k)**2/(2*t)) for k in range(-6,7))/np.sqrt(2*np.pi*t)
def Q(m):
    out=np.ones((N,N))
    for c in range(d):
        w=x[:,c][:,None]-x[:,c][None,:]; w=w-np.round(w); out*=p1(w,m*xi*xi)
    return out
def m0(m): return float(p1(np.array(0.0),m*xi*xi))**d
K=Q(1); M=m0(1); dp=np.sqrt(M*np.log(N)/N)
dd=K.sum(1); W=K/np.outer(dd,dd)*N; D=W.sum(1); S=W/np.sqrt(np.outer(D,D))
s,V=np.linalg.eigh(S); s=s[::-1]; V=V[:,::-1]
# population eigenvalues of -Laplace on the torus, ascending with multiplicity
R=12; g=np.arange(-R,R+1); grid=np.stack(np.meshgrid(*([g]*d),indexing='ij'),-1).reshape(-1,d)
lam=np.sort(4*np.pi**2*(grid**2).sum(1))[:N]
print(f"d={d} xi={xi} N={N} M={M:.2f} delta'={dp:.3f} delta'/xi={dp/xi:.2f} min s={s.min():.2e}")
for k in (1,2,4,8,16,32,64):
    Sk=(V*s**k)@V.T; E=Sk-Q(k)/N
    op=np.abs(np.linalg.eigvalsh(E)).max(); rs=np.abs(E).sum(0).max()
    n=min(200,N); err=np.abs(s[:n]**k-np.exp(-k*sig*lam[:n])).max()
    print(f"k={k:3d} m_k={m0(k):7.2f} ||S^k-Q_k||={op:.4f} maxcolsum={rs:.4f} delta'sqrt(k)={dp*np.sqrt(k):.3f} delta'sqrt(k)m_k={dp*np.sqrt(k)*m0(k):.2f}  max_j<=200|s_j^k-e^(-k sig lam_j)|={err:.4f}  sqrt(logN/N)m_k={np.sqrt(np.log(N)/N)*m0(k):.3f}")
