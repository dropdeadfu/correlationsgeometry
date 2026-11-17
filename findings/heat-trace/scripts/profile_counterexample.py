"""Counterexample to Theorem "Other profiles" without the second part of (F2).

F(u) = 1 - u + 5u^2 - 4.5u^3 on [0,1], F(u) = (1/2)(2/(1+u))^2 for u >= 1 satisfies (F1) with beta = 10,
c_3 = 4.5, u_0 = 1, the first part of (F2) with delta = 1/2 and (F3) with p = 2, but exceeds 1 inside (0,1);
on the flat circle T^F then grows exponentially in tau. Found by a reviewing session on 17 November 2026.
"""
import numpy as np
def F(u):
    return np.where(u<=1, 1-u+5*u**2-4.5*u**3, 0.5*(2/(1+u))**2)
u=np.linspace(0,1,100001); print("max F on [0,1]:",F(u).max(),"at u=",u[F(u).argmax()], " F(1)=",F(np.array([1.0]))[0], " sup|F| on u>=1:",np.abs(F(np.linspace(1,1e4,10**6))).max())
n=np.arange(-20000,20001); lam=4*np.pi**2*n**2.0
for sigma in [1e-3,1e-4]:
  for tau in [20,100]:
    t=tau*sigma; s=F(sigma*lam)
    T=np.sum(np.exp(-tau*(1-s))-np.exp(-tau)); Th=np.sum(np.exp(-t*lam)); Th2=np.sum(lam**2*np.exp(-t*lam))
    print(f"sigma={sigma} tau={tau} t={t}: T^F={T:.4e} Theta={Th:.4f} beta*sigma*t/2*Theta''={10*sigma*t/2*Th2:.4f}  #modes with s>1: {(s>1).sum()}")
