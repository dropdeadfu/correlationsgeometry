import numpy as np
rng=np.random.default_rng(3)
def heat0(t,d=2,M=60):
    n=np.arange(-M,M+1); return (np.exp(-4*np.pi**2*n**2*t).sum())**d
def run(N,xi,ks,reps):
    sig=xi**2/2
    out={k:[] for k in ks}; outP={k:[] for k in ks}
    for r in range(reps):
        X=rng.random((N,2)); d=X[:,None,:]-X[None,:,:]
        # periodised Gaussian = heat kernel at time sigma (sum over images -1,0,1 suffices for xi<=0.1)
        K=np.zeros((N,N))
        for a in (-1,0,1):
            for b in (-1,0,1):
                K+=np.exp(-((d[...,0]+a)**2+(d[...,1]+b)**2)/(2*xi**2))
        p=K/(2*np.pi*xi**2); Pt=p/N
        q=K.sum(1)/N; W=K/np.outer(q,q); P=W/W.sum(1)[:,None]
        ev=np.linalg.eigvalsh(Pt); evP=np.linalg.eigvals(P).real
        for k in ks:
            out[k].append((ev**k).sum()); outP[k].append((evP**k).sum())
    M=1/(2*np.pi*xi**2)
    print(f"N={N} xi={xi} M={M:.1f}")
    for k in ks:
        mk=heat0(k*sig); a=np.mean(out[k]); s=np.std(out[k]); aP=np.mean(outP[k])
        lo=mk*(1-k*k/(2*N))*(1+k*M/N); hi=mk+k*k*M*M/N
        print(f"  k={k:3d}: m_k={mk:8.3f}  E Tr Pt^k={a:8.3f} (sd {s:.3f})  bounds [{lo:.3f}, {hi:.3f}]  rel.bias oracle {a/mk-1:+.4f}  kM/N={k*M/N:.4f}   estimated-normalisation rel.dev {aP/mk-1:+.4f}")
run(1500,0.08,[2,4,8,16],12)
