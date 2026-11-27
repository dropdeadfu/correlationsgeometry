import numpy as np
xi=0.05; sig=xi**2/2; M=120
n=np.arange(-M,M+1); lam=(4*np.pi**2*(n[:,None]**2+n[None,:]**2)).ravel()
Theta=lambda t: np.exp(-lam*t).sum()
rng=np.random.default_rng(7)
for N in [1500,5000]:
    X=rng.random((N,2)); d=np.abs(X[:,None,:]-X[None,:,:]); d=np.minimum(d,1-d); r2=(d**2).sum(-1)
    K=np.exp(-r2/(2*xi**2)); q=K.sum(1)/N; W=K/np.outer(q,q); D=W.sum(1)
    sg=np.linalg.eigvalsh(W/np.sqrt(np.outer(D,D)))
    print(f"N={N}: min s={sg.min():.3e}, #neg={(sg<0).sum()}")
    for k in [2,10,30,100]:
        mk=(sg**k).sum(); th=Theta(k*sig)
        Tg=(np.exp(-k*(1-sg))-np.exp(-k)).sum()
        print(f"   k={k:4d}: Tr P^k={mk:9.4f}  Theta(k sigma)={th:9.4f}  rel.dev {mk/th-1:+.4f}   (continuous-time subtracted: {Tg/th-1:+.4f})")
