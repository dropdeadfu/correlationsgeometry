"""Constants and regime of the statements of the third Lean file (lean/CorrelationsToGeometryReal2.lean).

Evaluates the explicit constants of the file (kernelC1, eigL1C, kernelQC, eigC9, eigC10; transcribed from the
Lean definitions, the definitions of normC, l1C, h4C and kernelQC compared by hand with the file) and, for
`eig_G44_ii` (part (ii) of Theorem thm:eigtorus-l1 in shell form), the smallest power of ten N for which the
size condition  eigC9 [ (delta'/xi) lambda^(-1/2) + sqrt(log N/N) lambda^(d/2) ] <= 1  holds for at least one
shell |n|^2 = r >= 1 with lambda = 4 pi^2 r <= xi^(-2); printed there: the number of admissible shells, the
right-hand side eigC10 [ (delta'/xi) lambda^(1/2) + sqrt(log N/N) lambda^((d+2)/2) ] for the lowest admissible
shell, the target (1 - exp(-tau lambda))/tau and the bias tau lambda^2/2 (tau = xi^2/2).
Here delta' = sqrt(M log N/N), M = p(0) for the periodised Gaussian of variance xi^2 (Fourier series).
Only powers of ten are tried for N, so the thresholds are upper bounds. No sampling; pure arithmetic.
Written by a reviewing session of the AI system on 20 November 2026; the last table (constant of
`torus_reduction_paper`, transcribed from the Lean definitions h5cD, h5cA, h5Ca, h5Cb) added by the author-side
session on the same day.
Usage: python lean_third_file_constants.py
"""
import numpy as np
from math import sqrt, pi, log, exp, floor
def cvConst(): return 4/pi*(1+sqrt(12*pi))*sqrt(12*pi)*sqrt(2*pi)
def rateCK(d): return ((sqrt(4*pi)+1)*sqrt(3))**d
def rateRA(d): return sqrt(d*cvConst()*(2*sqrt(6))*(12*(1+sqrt(2*pi)))**(d-1))
def rateCfin3(d):
    q=sqrt(3*d+5)
    inner=(5/4)*(16*(rateCK(d)+1)+2*sqrt(7)*rateRA(d))+12*q*rateRA(d)
    return 48*q+3*2**d*max(2*(3*(9/8)*inner),3*inner)
A=lambda d:(1+sqrt(2*pi))**d
def kernelC1(d): return rateCfin3(d)*A(d)**2
def normC(d): return 6*sqrt(3*d+5)*A(d)
def l1C(d):
    q=sqrt(3*d+5)
    return 9/7*(27*q+2*(3*(9/8)*((5/4)*(16*(rateCK(d)+1)+2*sqrt(7)*rateRA(d))+12*q*rateRA(d))))
def h4C(d): return l1C(d)*A(d)
def eigL1C(d): return 6*normC(d)+h4C(d)
def kernelQC(d): return (2+sqrt(8*(3+2*(3*d+1)))*(1+2*sqrt(2)**d))*A(d)
def eigC9(d): return 8*(kernelC1(d)+eigL1C(d)+kernelQC(d))
def eigC10(d): return 16*(eigL1C(d)+kernelQC(d))
def M(d,sig):
    n=np.arange(-2000,2001); return float(np.sum(np.exp(-2*pi**2*sig*n**2)))**d

# --- constants of H5.torus_reduction_paper (reduction without remaining hypothesis) ---
def _inner(d): return (5/4)*(16*(rateCK(d)+1)+2*sqrt(7)*rateRA(d))+12*sqrt(3*d+5)*rateRA(d)
def h5cD(d): return 6*sqrt(3*d+5)
def h5cA(d): return 3*(9/8)*_inner(d)
def h5Ca(d): return h5cD(d)*h5cA(d)*A(d)**3*sqrt(6)**d
def h5Cb(d): return h5cA(d)*A(d)**2*sqrt(6)**d
def redC(d):
    """Constant C of |Tr P^(k+1) - m_(k+1) - Pi_k| <= C delta'^2 k m_(k+1) in `torus_reduction_paper`."""
    s2=sqrt(2)**d
    return s2*(2*(4*normC(d))*kernelC1(d)+2*(14*normC(d)**2)+h5Ca(d)
               +2*(2*s2*h5Ca(d)+h5Ca(d)+s2*kernelC1(d)*h5Cb(d)+h4C(d)*h5Cb(d)))
def reduction_table():
    print()
    print("torus_reduction_paper: constant C, and the comparison of C delta'^2 k (reduction) with")
    print("kernelC1 delta' sqrt(k+1) (first-stage bound from the kernel statement), both relative to m_(k+1);")
    print("xi = 0.1, smallest power of ten N with kernelC1 delta' <= 1 (K = 1) and with C delta'^2 <= 1")
    for d in (1,2,3):
        C=redC(d); Mp=M(d,0.01)
        n1=next(e for e in range(6,80) if kernelC1(d)*sqrt(Mp*log(10.0**e)/10.0**e)<=1)
        n2=next(e for e in range(6,120) if C*Mp*log(10.0**e)/10.0**e<=1)
        n3=next(e for e in range(6,160) if C*Mp*log(10.0**e)/10.0**e<=kernelC1(d)*sqrt(2*Mp*log(10.0**e)/10.0**e))
        print("d=%d  h5Ca %.4g  h5Cb %.4g  C %.4g  C/kernelC1^2 %.4g | kernel condition from N=1e%d, C delta'^2 <= 1 from N=1e%d, reduction below first stage (k=1) from N=1e%d"
              %(d,h5Ca(d),h5Cb(d),C,C/kernelC1(d)**2,n1,n2,n3))
if __name__=="__main__":
    for d in (1,2,3):
        print(d,"kernelC1 %.4g eigL1C %.4g kernelQC %.4g eigC9 %.4g eigC10 %.4g ratio C10/C9 %.4g"%(kernelC1(d),eigL1C(d),kernelQC(d),eigC9(d),eigC10(d),eigC10(d)/eigC9(d)))
    def shells(d,rmax):
        m=int(sqrt(rmax))+1
        import itertools
        s=set()
        for n in itertools.product(range(-m,m+1),repeat=d):
            q=sum(x*x for x in n)
            if 1<=q<=rmax: s.add(q)
        return sorted(s)
    for d in (1,2,3):
        for xi in (0.15,0.1,0.05,0.02,0.01):
            sig=xi*xi; rmax=1/(4*pi**2*sig); sh=shells(d,rmax); Mp=M(d,sig)
            print("d=%d xi=%.3g M=%.4g rmax=%.3g #shells=%d"%(d,xi,Mp,rmax,len(sh)))
            for e in range(8,60):
                N=10.0**e; L=sqrt(log(N)/N); dp=sqrt(Mp*log(N)/N)
                ok=[]
                for r in sh:
                    s=2*pi*sqrt(r)
                    cond=eigC9(d)*(dp/xi/s+L*s**d)
                    if cond<=1: ok.append((r,cond))
                if ok:
                    r,cond=ok[0]; s=2*pi*sqrt(r); lam=s*s; tau=sig/2
                    rhs=eigC10(d)*(dp/xi*s+L*s**(d+2))
                    tgt=(1-exp(-tau*lam))/tau
                    c2=(kernelC1(d)*dp)**2
                    print("   first N=1e%d: shells ok %d/%d (r=%s..%s); r=%g: cond=%.3g rhs=%.4g lam=%.4g target=%.4g bias=%.4g rhs/lam=%.3g; (C1 dp)^2=%.3g K=%d"%(e,len(ok),len(sh),ok[0][0],ok[-1][0],r,cond,rhs,lam,tgt,tau*lam**2/2,rhs/lam,c2,floor(1/c2)))
                    # further N
                    for e2 in (e+2,e+4,e+8):
                        N=10.0**e2; L=sqrt(log(N)/N); dp=sqrt(Mp*log(N)/N)
                        okk=[r for r in sh if eigC9(d)*(dp/xi/(2*pi*sqrt(r))+L*(2*pi*sqrt(r))**d)<=1]
                        r=okk[0]; s=2*pi*sqrt(r)
                        print("      N=1e%d: shells ok %d/%d; r=%g rhs=%.4g; r=%g rhs/lam=%.3g"%(e2,len(okk),len(sh),r,eigC10(d)*(dp/xi*s+L*s**(d+2)),okk[-1],eigC10(d)*(dp/xi*(2*pi*sqrt(okk[-1]))+L*(2*pi*sqrt(okk[-1]))**(d+2))/(4*pi**2*okk[-1])))
                    break
    reduction_table()
