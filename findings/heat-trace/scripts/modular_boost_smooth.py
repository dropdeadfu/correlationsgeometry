#!/usr/bin/env python3
"""Modular Hamiltonian of a half space on smooth test functions: node model against a relativistic control.

Companion of modular_boost_check.py (same setting, transverse momentum 0, mass 1, chain of n sites of length 1,
region = sites 0..n/2-1).  For the kinetic part N of the modular Hamiltonian the script prints
   f^T N f / (2 pi sum_i x_i f_i^2)
for Gaussian bumps f of width 0 (a single node), 1, 2, 3 xi centred at x0, for (a) the oscillators on the kernel
graph and (b) the nearest-neighbour chain with the same long-wave speed.  The Bisognano-Wichmann form gives 1
near the cut; the second cut at x = 1/2 lowers the value in the same way for both models, so the control (b)
is the reference.  High precision arithmetic (mpmath).  Deterministic.

Usage: modular_boost_smooth.py n xi      (numbers in the paper: 128 0.02)
"""
import sys
import mpmath as mp
import modular_boost_check as mb
mp.mp.dps=110
def modN(n, om):
    half=n//2
    cx=[sum(mp.cos(2*mp.pi*k*d/n)/(2*om[k]) for k in range(n))/n for d in range(half)]
    cp=[sum(mp.cos(2*mp.pi*k*d/n)*om[k]/2 for k in range(n))/n for d in range(half)]
    X=mp.matrix(half,half); P=mp.matrix(half,half)
    for i in range(half):
        for j in range(half):
            X[i,j]=cx[abs(i-j)]; P[i,j]=cp[abs(i-j)]
    ep,Up=mp.eigsy(P)
    Ph=Up*mp.diag([mp.sqrt(e) for e in ep])*Up.T; Pmh=Up*mp.diag([1/mp.sqrt(e) for e in ep])*Up.T
    nu2,U=mp.eigsy(Ph*X*Ph)
    w=[mp.log((mp.sqrt(v)+mp.mpf(1)/2)/(mp.sqrt(v)-mp.mpf(1)/2))*mp.sqrt(v) for v in nu2]
    return Pmh*U*mp.diag(w)*U.T*Pmh
n=int(sys.argv[1]); xi=mp.mpf(sys.argv[2]); half=n//2
th=mb.theta(n,xi)
for name,om in [('node model', [mp.sqrt((2/xi**2)*(1-th[k])+1) for k in range(n)]),
                ('NN chain  ', [mp.sqrt(4*n**2*mp.sin(mp.pi*k/n)**2+1) for k in range(n)])]:
    N=modN(n,om)
    xs=[(i+mp.mpf(1)/2)/n for i in range(half)]
    print(name,' n',n,' xi',mp.nstr(xi,3))
    for x0 in (mp.mpf('0.06'),mp.mpf('0.10'),mp.mpf('0.14')):
        row=[]
        for wxi in (0,1,2,3):
            if wxi==0:
                i0=min(range(half),key=lambda i:abs(xs[i]-x0)); row.append(mp.re(N[i0,i0]/(2*mp.pi*xs[i0])))
            else:
                w=wxi*xi
                f=[mp.exp(-(x-x0)**2/(2*w**2)) for x in xs]
                num=sum(f[i]*N[i,j]*f[j] for i in range(half) for j in range(half))
                den=2*mp.pi*sum(xs[i]*f[i]**2 for i in range(half))
                row.append(mp.re(num/den))
        print('   x0=',mp.nstr(x0,3),' ratio for bump width 0 (single node), 1, 2, 3 xi: ',[mp.nstr(r,5) for r in row],flush=True)
