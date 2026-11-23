
import sys, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc
n=8
E=[(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]
def f(x): return any((x>>u)&1 and (x>>v)&1 for u,v in E)
def run(s):
    cnt=[0]
    def nv(): cnt[0]+=1; return cnt[0]
    cl=[]
    X=range(256)
    val={}
    for w in range(n):
        for x in X: val[w,x]=None  # constants
    G=[]
    for k in range(s):
        w=n+k
        for x in X: val[w,x]=nv()
    sel={}
    for k in range(s):
        w=n+k
        t=nv()
        A={i:nv() for i in range(w)}
        B={i:nv() for i in range(w)}
        sel[k]=(t,A,B)
        for S in (A,B):
            cl.append(list(S.values()))
            for i,j in itertools.combinations(S,2): cl.append([-S[i],-S[j]])
        # a index < b index
        for i in range(w):
            for j in range(i+1):
                cl.append([-A[i],-B[j]])
        for x in X:
            ia=nv(); ib=nv()
            for S,y in ((A,ia),(B,ib)):
                for i in range(w):
                    if i<n:
                        c=(x>>i)&1
                        cl.append([-S[i], y if c else -y])
                    else:
                        v=val[i,x]
                        cl.append([-S[i],-y,v]); cl.append([-S[i],y,-v])
            o=val[w,x]
            # t: and ; -t: or
            cl.append([-t,-ia,-ib,o]); cl.append([-t,ia,-o]); cl.append([-t,ib,-o])
            cl.append([t,ia,-o if False else o*0 or -o,ib]) if False else None
            cl.append([t,-ia,o]); cl.append([t,-ib,o]); cl.append([t,ia,ib,-o])
    for k in range(s-1):
        w=n+k
        t1,A1,B1=sel[k]; t2,A2,B2=sel[k+1]
        P1=[(a,b) for b in range(w) for a in range(b)]
        P2=[(a,b) for b in range(w+1) for a in range(b)]
        for (a,b) in P1:
            for (c,d) in P2:
                if (d,c) < (b,a) and c!=w and d!=w:
                    cl.append([A2[w],B2[w],-A1[a],-B1[b],-A2[c],-B2[d]])
    for k in range(s):
        for m in range(k+1,s):
            tk,Ak,Bk=sel[k]; tm,Am,Bm=sel[m]
            for b in range(n+k):
                for a in range(b):
                    cl.append([-Ak[a],-Bk[b],-Am[a],-Bm[b],tk,tm])
                    cl.append([-Ak[a],-Bk[b],-Am[a],-Bm[b],-tk,-tm])
    for x in X:
        v=val[n+s-1,x]
        cl.append([v] if f(x) else [-v])
    for k in range(s-1):
        w=n+k
        cl.append([sel[m][1][w] for m in range(k+1,s)]+[sel[m][2][w] for m in range(k+1,s)])
    sol=Cadical153(bootstrap_with=cl)
    r=sol.solve()
    out=None
    if r:
        m=set(l for l in sol.get_model() if l>0)
        out=[]
        for k in range(s):
            t,A,B=sel[k]
            out.append(('AND' if t in m else 'OR',[i for i in A if A[i] in m][0],[i for i in B if B[i] in m][0]))
    return r,out
for s in map(int,sys.argv[1:]):
    print(s,run(s),flush=True)
