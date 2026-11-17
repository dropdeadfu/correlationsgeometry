"""Check of the quartic coefficient of the population walk on S^2 (Remark after Corollary "sphere").

Gaussian kernel in the geodesic distance. Compares Tr P_infty^k / Tr e^{k sigma_xi Delta} - 1 with the
leading term (beta_xi - 1)/k of Theorem "profile"(ii) and with -xi^4/15; fits the coefficients of lambda
and lambda^2 of s_l from l = 1..4. Written by a reviewing session on 17 November 2026 (numpy only).
"""
import numpy as np
from math import pi
def sl(xi,L):
    b=min(pi,14*xi)
    x,w=np.polynomial.legendre.leggauss(3000)
    th=0.5*b*(x+1); w=0.5*b*w
    dens=np.exp(-th**2/(2*xi**2))*np.sin(th)*w
    Z=dens.sum(); dens/=Z
    c=np.cos(th)
    s=np.empty(L+1); p0=np.ones_like(c); p1=c.copy()
    s[0]=1.0; s[1]=(dens*p1).sum()
    for l in range(1,L):
        p2=((2*l+1)*c*p1-l*p0)/(l+1); p0,p1=p1,p2
        s[l+1]=(dens*p1).sum()
    mom=lambda n:(dens*th**n).sum()
    return s,mom(2),mom(4),mom(6),Z
def Theta(t,L=3000):
    l=np.arange(L+1); return ((2*l+1)*np.exp(-l*(l+1)*t)).sum()
if __name__=="__main__":
  for xi in [0.3,0.2,0.15,0.1,0.064,0.05,0.025]:
      L=int(14/xi)+50
      s,m2,m4,m6,Z=sl(xi,L)
      l=np.arange(L+1); lam=l*(l+1.0)
      sig=m2/4+m4/96; sigma=xi**2/2
      beta=m4/(32*sig**2); c3=m6/(720*sig**3)
      u=sig*lam
      resid=np.abs(s-1+sig*lam-m4/64*lam**2); bound=m6/720*lam**3
      okF1=np.all(resid<=bound+1e-13)
      lo=u<=0.5; hi=~lo
      g1=np.all(s[lo]>=0.4) and np.all(s[lo]<=1-0.6*u[lo]+1e-14)
      print(f"xi={xi}: sig/sigma={sig/sigma:.5f} (1-xi^2/6={1-xi**2/6:.5f}) beta={beta:.4f} (1-xi^2/3={1-xi**2/3:.4f}) c3={c3:.4f} F1ok={okF1} lowok={g1} max|s|hi={np.abs(s[hi]).max():.4f} min s lo={s[lo].min():.4f} sig<=xi^2/2:{sig<=sigma}")
      hs=((2*l+1)*s**2).sum(); print(f"    sum(2l+1)s^2*xi^2={hs*xi**2:.5f}  m1*xi^2/2={ (2/Z)*xi**2/2:.5f}  Szego bound at first hi l: {0.8222/np.sqrt(l[hi][0]*xi)/(1-xi**2/2):.4f}")
      if xi==0.025:
          for k in [20,50,100,200]:
              tr=((2*l+1)*s**k).sum()
              tau=k
              sub=((2*l+1)*(np.exp(-tau*(1-s))-np.exp(-tau))).sum()
              print(f"    k={k}: TrP^k/Theta(k sigma)-1 = {(tr/Theta(k*sigma)-1)/xi**2:.4f} xi^2 ; TrP^k/Theta(k sig_xi)-1={tr/Theta(k*sig)-1:.2e}; sub/Theta(k sig_xi)-1={sub/Theta(k*sig)-1:.4f}; sub/Theta(k sigma)-1={sub/Theta(k*sigma)-1:.4f}")
for xi in [0.1,0.05,0.025]:
    L=int(14/xi)+50
    s,m2,m4,m6,Z=sl(xi,L); l=np.arange(L+1); lam=l*(l+1.0)
    sig=m2/4+m4/96; sigma=xi**2/2; sig2=sig+m6/1440
    beta=m4/(32*sig**2)
    # true quartic coefficient from small l: fit s_l = 1 - a lam + b lam^2 - c lam^3 using l=1..3 exact solve
    A=np.array([[lam[i],lam[i]**2,lam[i]**3,lam[i]**4] for i in (1,2,3,4)]); co=np.linalg.solve(A,s[1:5]-1)
    print(f"xi={xi}: beta_paper-1={beta-1:.3e}; fitted: sigma_fit/sig-1={-co[0]/sig-1:.3e} (xi^4/15={xi**4/15:.3e}), beta_fit-1={2*co[1]/co[0]**2-1:.3e}")
    for k in [20,50,100,200]:
        if k*sigma>1: continue
        tr=((2*l+1)*s**k).sum(); sub=((2*l+1)*(np.exp(-k*(1-s))-np.exp(-k))).sum()
        print(f"   k={k}: TrP^k/Th(k sig_xi)-1={tr/Theta(k*sig)-1:+.3e}  predicted (beta_xi-1)/k={(beta-1)/k:+.3e}; with sig+m6/1440: {tr/Theta(k*sig2)-1:+.2e}; sub/Th(k sigma)-1={sub/Theta(k*sigma)-1:.5f}")
