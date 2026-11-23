
import s3, sys
s3.n=7
s3.E=[(u,v) for (u,v) in [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)] if v!=7]
print(s3.E, flush=True)
for k in map(int,sys.argv[1:]): print('Q3-v',k, s3.run(k), flush=True)
