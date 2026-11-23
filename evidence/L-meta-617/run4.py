
import s1n, sys
s1n.n=7
s1n.E=[(u,v) for (u,v) in [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)] if v!=7]
for k in map(int,sys.argv[1:]): print('Q3-v plain',k, s1n.run(k), flush=True)
s1n.E=[(0,1),(1,2),(2,3)]
for k in (3,4): print('path plain n7',k, s1n.run(k)[0], flush=True)
