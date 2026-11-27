import numpy as np
xi=0.05; M=140
n=np.arange(-M,M+1); lam=(4*np.pi**2*(n[:,None]**2+n[None,:]**2)).ravel()
Th=lambda t,der=0: ((-lam)**der*np.exp(-lam*t)).sum()
# --- mode-wise check of the bounds used in the proofs
x=np.linspace(0,1,2001)[1:]
ok=True
for tau in [1,2,5,20,100,1000]:
    xx=x*tau; u=xx/tau; z=tau*(1-np.exp(-u)); a=np.exp(-z); b=np.exp(-xx)
    e2=np.abs(a-b-b*xx**2/(2*tau)); bd2=np.exp(-xx/2)*(xx**4/8+xx**3/6)/tau**2
    ec=np.abs(a*(1-z**2/(2*tau))-b); bdc=np.exp(-xx/2)*(xx**3/2+xx**4/4)/tau**2
    ok&=bool((e2<=bd2*(1+1e-9)+1e-18).all() and (ec<=bdc*(1+1e-9)+1e-18).all())
    s=np.linspace(0,np.exp(-1),500)
    hc=np.abs(np.exp(-tau)*(np.exp(tau*s)*(1-tau*(1-s)**2/2)-1+tau/2)); hb=tau*s*(2+tau/2)*np.exp(-tau*(1-np.exp(-1)))
    ok&=bool((hc<=hb*(1+1e-9)+1e-18).all())
print("mode-wise bounds (second order, corrected, corrected high):",ok)
# --- general profile: mixture of two Gaussians, variances a,b (in units xi^2)
A,B=0.5,1.5; m2=(A+B)/2; beta=2*(A*A+B*B)/(A+B)**2; sig=m2*xi**2/2
F=lambda lam_: 0.5*np.exp(-A*xi**2*lam_/2)+0.5*np.exp(-B*xi**2*lam_/2)
s=F(lam)
print(f"mixture profile: beta={beta}")
for tau in [10,30,100]:
    t=tau*sig; th=Th(t); lead=sig*t/2*Th(t,2)/th
    Tc=(np.exp(-tau*(1-s))-np.exp(-tau)).sum(); Td=(s**tau).sum()
    print(f"  tau={tau}: continuous {Tc/th-1:+.5f} (pred beta*lead={beta*lead:+.5f});  discrete {Td/th-1:+.5f} (pred (beta-1)*lead={(beta-1)*lead:+.5f})")
# --- fixed xi, N -> infinity (Gaussian profile): sample vs solvable case
sig=xi**2/2; sp=np.exp(-sig*lam)
Tpop=lambda tau:(np.exp(-tau*(1-sp))-np.exp(-tau)).sum()
rng=np.random.default_rng(11)
for N in [1000,2500,6000]:
    X=rng.random((N,2)); d=np.abs(X[:,None,:]-X[None,:,:]); d=np.minimum(d,1-d); r2=(d**2).sum(-1)
    K=np.exp(-r2/(2*xi**2)); q=K.sum(1)/N; W=K/np.outer(q,q); D=W.sum(1)
    sg=np.clip(np.linalg.eigvalsh(W/np.sqrt(np.outer(D,D))),0,1)
    out=[]
    for tau in [10,30]:
        Tg=(np.exp(-tau*(1-sg))-np.exp(-tau)).sum()
        out.append(f"tau={tau}: T_N/T_sigma-1={Tg/Tpop(tau)-1:+.4f}, TrP^k/Theta-1={(sg**tau).sum()/Th(tau*sig)-1:+.4f}")
    print(f"  N={N}: "+"; ".join(out))
