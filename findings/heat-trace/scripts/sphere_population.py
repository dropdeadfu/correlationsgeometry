import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import eval_legendre
def run(xi,Lmax=None):
    sig=xi**2/2
    Lmax=Lmax or int(12/xi)
    # quadrature in theta on [0, min(pi, 12 xi)]
    th_max=min(np.pi,14*xi); x,w=leggauss(4000); th=(x+1)/2*th_max; w=w*th_max/2
    k=np.exp(-th**2/(2*xi**2)); den=(w*k*np.sin(th)).sum()
    l=np.arange(0,Lmax+1)
    s=np.array([(w*k*np.sin(th)*eval_legendre(li,np.cos(th))).sum()/den for li in l])
    lam=l*(l+1.0); mult=2*l+1
    out=[]
    for tau in [20,50,100,200]:
        t=tau*sig; Th=(mult*np.exp(-lam*t)).sum()
        Tc=(mult*(np.exp(-tau*(1-s))-np.exp(-tau))).sum(); Td=(mult*s**tau).sum()
        out.append((tau,Tc/Th-1,Td/Th-1))
    # effective sigma from low modes: -ln s_l / lam_l
    se=-np.log(s[1:6])/lam[1:6]
    return out,se/sig-1
for xi in [0.1,0.05,0.025]:
    out,se=run(xi)
    print(f"xi={xi}: sigma_eff/sigma-1 (l=1..5) = {np.round(se,6)}  ; /xi^2 = {np.round(se/xi**2,4)}")
    for tau,c,d in out: print(f"    tau={tau:4d}: continuous {c:+.5f} (1/tau={1/tau:.5f})   discrete {d:+.6f}   discrete/xi^2={d/xi**2:+.4f}")
