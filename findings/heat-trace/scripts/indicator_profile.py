import numpy as np
from scipy.special import j1
# flat 2-torus, indicator profile of the unit disk (radius xi): kappa-hat(z)=2 J1(z)/z
def run(xi,M):
    sig=xi**2/8; beta=2/3
    n=np.arange(-M,M+1); r2=(n[:,None]**2+n[None,:]**2).astype(float)
    lam=4*np.pi**2*r2
    z=2*np.pi*xi*np.sqrt(r2); s=np.where(z>0,2*j1(np.where(z>0,z,1))/np.where(z>0,z,1),1.0)
    m1=1/(np.pi*xi**2)                     # Tr P = k(x,x)/q = 1/(pi xi^2)
    res=[]
    for tau in [20,50,100]:
        t=tau*sig; lamc=lam[lam*t<60]; Th=np.exp(-lamc*t).sum()
        Th2=(lamc**2*np.exp(-lamc*t)).sum(); lead=sig*t/2*Th2/Th
        Tc=np.exp(-tau)*(tau*m1+(np.exp(tau*s)-1-tau*s).sum())
        Td=(s**tau).sum()
        res.append((tau,Tc/Th-1,beta*lead,Td/Th-1,(beta-1)*lead))
    return res,(s**2).sum(),1/(np.pi*xi**2)
for xi,M in [(0.05,1500),(0.05,3000)]:
    res,hs,par=run(xi,M)
    print(f"xi={xi}, M={M}: sum s^2 = {hs:.3f} (Parseval {par:.3f})")
    for r in res: print("   tau=%d: continuous %+.5f (pred %+.5f)   discrete %+.5f (pred %+.5f)"%r)
