import numpy as np
rng=np.random.default_rng(1)
def run(N,xi,loops=True):
    X=rng.random((N,2))                      # flat torus, d=2
    d=np.abs(X[:,None,:]-X[None,:,:]); d=np.minimum(d,1-d); r=np.sqrt((d**2).sum(-1))
    K=np.exp(-r**2/(2*xi**2))
    if not loops: np.fill_diagonal(K,0)
    q=K.sum(1)/N; W=K/np.outer(q,q); D=W.sum(1)
    P=W/D[:,None]; S=W/np.sqrt(np.outer(D,D)); s=np.linalg.eigvalsh(S)
    return P,s
N=1500; xi=0.05
P,s=run(N,xi)
m1=np.trace(P); m2=(s**2).sum(); pii=np.diag(P)
print("m1,m2,N,max Pii",m1,m2,N,pii.max(), "trP2 check",np.trace(P@P))
ok=True
for tau in [0.3,1,3,10,30,100]:
    T=np.exp(-tau*(1-s)).sum()
    chain=[N*np.exp(-tau), N*np.exp(-tau*(1-m1/N)), np.exp(-tau*(1-pii)).sum(), T]
    T2=T-np.exp(-tau)*(N+tau*m1)
    lo=0.5*tau**2*np.exp(-2*tau)*m2; hi=0.5*tau**2*m2
    d=0.2*tau; lc=T**2<=np.exp(-(tau-d)*(1-s)).sum()*np.exp(-(tau+d)*(1-s)).sum()*(1+1e-12)
    cont=sum(np.exp(-(4*np.pi**2*(a*a+b*b))*tau*xi**2/2) for a in range(-40,41) for b in range(-40,41))
    stay=chain[2]
    print(f"tau={tau:6}: chain ok {all(chain[i]<=chain[i+1]*(1+1e-12) for i in range(3))}  T2 in [lo,hi] {lo<=T2<=hi}  logconvex {lc}  | T-Ne^-tau={T-chain[0]:.3f}  T-stay={T-stay:.3f}  T2={T2:.3f} continuum={cont:.3f}")
