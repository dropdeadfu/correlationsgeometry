import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import eval_legendre, gamma
c=2**-0.25*gamma(0.75); print("2^(-1/4) Gamma(3/4) =",c," sqrt(2/pi)*that =",np.sqrt(2/np.pi)*c)
for xi in [0.1,0.05,0.025]:
    th_max=min(np.pi,14*xi); x,w=leggauss(6000); th=(x+1)/2*th_max; w=w*th_max/2
    k=np.exp(-th**2/(2*xi**2)); den=(w*k*np.sin(th)).sum()
    m2=(w*k*np.sin(th)*th**2).sum()/den; m4=(w*k*np.sin(th)*th**4).sum()/den; m6=(w*k*np.sin(th)*th**6).sum()/den
    sx=m2/4+m4/96; beta=m4/(32*sx**2); c3=m6/(720*sx**3)
    L=int(30/xi); l=np.arange(0,L+1)
    s=np.array([(w*k*np.sin(th)*eval_legendre(li,np.cos(th))).sum()/den for li in l])
    u=sx*l*(l+1)
    hi=u>=0.5
    bound=np.sqrt(2/np.pi)*c/np.sqrt(np.maximum(l,1)*xi)/(1-xi**2/3)
    f1=np.abs(s-(1-u+beta*u**2/2))<=c3*u**3+1e-12
    print(f"xi={xi}: sigma_xi/sigma={sx/(xi**2/2):.6f} beta={beta:.5f} c3={c3:.4f}  F1 holds for all l: {f1.all()}  max|s_l| on u>=0.5: {np.abs(s[hi]).max():.4f}  Szego bound ok: {(np.abs(s[hi])<=bound[hi]).all()}  bound at first high mode: {bound[hi][0]:.4f}  max s on u in [0.05,0.5]: {s[(u>=0.05)&(u<0.5)].max():.4f}")
