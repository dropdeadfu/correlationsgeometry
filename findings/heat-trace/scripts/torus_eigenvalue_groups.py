"""Group means of the eigenvalues of the graph Laplacian on the flat 2-torus: 1/N or 1/sqrt(N)?

For groups of equal eigenvalues of -Delta the script prints, over independent samples, the average and
the standard deviation of the mean relative deviation of the graph eigenvalues from the population
value (1 - exp(-sigma lambda))/sigma, and the standard deviation of the lowest eigenvalue of the group.
Test of a prediction: if the splitting of a group is, to first order, given by a block of G - 1 with
zero trace, the group mean has no term of the order N^(-1/2). Gaussian kernel with self-loops,
xi = 0.1; fixed seed.
"""
import numpy as np
def theta(dx,var): return sum(np.exp(-(dx+a)**2/(2*var)) for a in range(-6,7))/np.sqrt(2*np.pi*var)
xi=0.1; sig=xi**2/2
n=np.arange(-12,13); lam=np.sort((4*np.pi**2*(n[:,None]**2+n[None,:]**2)).ravel()); pop=(1-np.exp(-sig*lam))/sig
clusters=[(1,5),(5,9),(9,13)]
res={}
for N,reps in ((400,120),(800,80),(1600,40)):
    rng=np.random.default_rng(11); means={c:[] for c in clusters}; singles={c:[] for c in clusters}
    for _ in range(reps):
        X=rng.random((N,2)); dx=X[:,None,0]-X[None,:,0]; dy=X[:,None,1]-X[None,:,1]
        K=theta(dx,xi**2)*theta(dy,xi**2); M=K[0,0]
        q=K.sum(1)/N; W=K/np.outer(q,q); D=W.sum(1)
        s=np.sort(np.linalg.eigvalsh(W/np.sqrt(np.outer(D,D))))[::-1]; lamN=(1-s)/sig
        for c in clusters:
            rel=(lamN[c[0]:c[1]]-pop[c[0]:c[1]])/pop[c[0]:c[1]]
            means[c].append(rel.mean()); singles[c].append(rel[0])
    res[N]=(means,singles,M)
    print(f"N={N} samples={reps} M/N={M/N:.4f}")
    for c in clusters:
        m=np.array(means[c]); s1=np.array(singles[c])
        print(f"   lambda={lam[c[0]]:6.1f}: group mean: average {m.mean():+.5f} ({m.mean()/(M/N):+.2f} M/N), sd over samples {m.std():.5f} -> sd*N = {m.std()*N:.2f}, sd*sqrt(N) = {m.std()*np.sqrt(N):.3f} | lowest eigenvalue of the group: sd {s1.std():.5f} -> sd*sqrt(N) = {s1.std()*np.sqrt(N):.3f}")
