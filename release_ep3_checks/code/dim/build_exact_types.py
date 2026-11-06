import sys, time, pickle
sys.path.insert(0,'<ROOT>/dim')
from exact_blocks import ExactRelax
k,d=int(sys.argv[1]),int(sys.argv[2])
t0=time.time()
drop={('src','22',(0,2),(st,st,st),2,'std') for st in range(6)}  # anomalous block (dropped)
ER=ExactRelax(k,d,drop=())
print('types',len(ER.types),'time %.1fs'%(time.time()-t0))
tot=sum(t['Vb'].ncols()*(2 if t['kind']=='gram' else 1)+(t['Vb2'].ncols() if t['kind']=='gram2' else 0) for t in ER.types)
print('total V dims',tot)
out=[]
for t in ER.types:
    Vb=t['Vb']
    rec=dict({k_:v for k_,v in t.items() if k_ not in ('Vb','Vb2')}, Vb=[[int(Vb[i,j]) for j in range(Vb.ncols())] for i in range(Vb.nrows())])
    if 'Vb2' in t:
        V2=t['Vb2']; rec['Vb2']=[[int(V2[i,j]) for j in range(V2.ncols())] for i in range(V2.nrows())]
    out.append(rec)
pickle.dump(out,open(sys.argv[3],'wb'))
