
import s2
s2.E=[(0,1),(1,2),(2,3)]
for k in range(1,7): print(k, s2.run(k), flush=True)
s2.E=[(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]
for k in range(1,10): print('cube',k, s2.run(k)[0], flush=True)
