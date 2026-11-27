import numpy as np
xi=0.05; sig=xi**2/2; M=120
n=np.arange(-M,M+1); lam=(4*np.pi**2*(n[:,None]**2+n[None,:]**2)).ravel(); s=np.exp(-sig*lam)
Th=lambda t,der=0: ((-lam)**der*np.exp(-lam*t)).sum()
T=lambda t: (np.exp(-(t/sig)*(1-s))-np.exp(-t/sig)).sum()
Tpp=lambda t: (((1-s)/sig)**2*np.exp(-(t/sig)*(1-s))-np.exp(-t/sig)/sig**2).sum()
taus=[5,7,10,15,20,30,50,70,100,150]
rng=np.random.default_rng(7); N=5000
X=rng.random((N,2)); d=np.abs(X[:,None,:]-X[None,:,:]); d=np.minimum(d,1-d); r2=(d**2).sum(-1)
K=np.exp(-r2/(2*xi**2)); q=K.sum(1)/N; W=K/np.outer(q,q); D=W.sum(1)
sg=np.linalg.eigvalsh(W/np.sqrt(np.outer(D,D))); sg=np.clip(sg,0,1)
rows={k:[] for k in ['pop','lead','corr','gc','gd']}
for tau in taus:
    t=tau*sig; th=Th(t)
    rows['pop'].append((tau,(T(t)-th)/th)); rows['lead'].append((tau,sig*t/2*Th(t,2)/th))
    rows['corr'].append((tau,abs(T(t)-sig*t/2*Tpp(t)-th)/th))
    rows['gc'].append((tau,((np.exp(-tau*(1-sg))-np.exp(-tau)).sum()-th)/th))
    rows['gd'].append((tau,abs((sg**tau).sum()-th)/th))
for k,v in rows.items(): print(k,' '.join(f'({a},{b:.5f})' for a,b in v))
