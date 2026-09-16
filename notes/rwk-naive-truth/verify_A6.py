"""Verify the 6-element algebra A6 = {0 < p < x,y < q < 1} (x,y incomparable) is an
RWK-algebra (bounded integral commutative involutive distributive residuated lattice),
that it is NOT prelinear, and that p is an 'interacting infinitesimal':
n.p <= ~p for all n but (2p) o (2p) != 0."""
E=['0','p','x','y','q','1']
leq={(a,b):False for a in E for b in E}
order=[('0','p'),('p','x'),('p','y'),('x','q'),('y','q'),('q','1')]
for a in E: leq[(a,a)]=True
for a,b in order: leq[(a,b)]=True
changed=True
while changed:
    changed=False
    for a in E:
        for b in E:
            for c in E:
                if leq[(a,b)] and leq[(b,c)] and not leq[(a,c)]: leq[(a,c)]=True; changed=True
def join(a,b): return min([c for c in E if leq[(a,c)] and leq[(b,c)]], key=lambda c: sum(leq[(d,c)] for d in E))
def meet(a,b): return max([c for c in E if leq[(c,a)] and leq[(c,b)]], key=lambda c: sum(leq[(d,c)] for d in E))
neg={'0':'1','1':'0','p':'q','q':'p','x':'y','y':'x'}
JI={'p','x','y','1'}
tab={('p','p'):'0',('p','x'):'0',('p','y'):'0',('x','x'):'x',('x','y'):'0',('y','y'):'p'}
def fus(a,b):
    if a=='1': return b
    if b=='1': return a
    if a=='0' or b=='0': return '0'
    v='0'
    for i in JI:
        if not leq[(i,a)] or i=='1': continue
        for j in JI:
            if not leq[(j,b)] or j=='1': continue
            v=join(v, tab[(i,j)] if (i,j) in tab else tab[(j,i)])
    return v
def imp(a,b): return max([z for z in E if leq[(fus(z,a),b)]], key=lambda c: sum(leq[(d,c)] for d in E))
ok=True
for a in E:
    for b in E:
        assert fus(a,b)==fus(b,a)
        assert leq[(fus(a,b),meet(a,b))]
        assert (fus(a,b)=='0')==leq[(a,neg[b])]
        assert neg[neg[a]]==a and (leq[(a,b)]==leq[(neg[b],neg[a])])
        assert imp(a,'0')==neg[a]
        for c in E:
            assert fus(fus(a,b),c)==fus(a,fus(b,c)), (a,b,c)
            assert (leq[(fus(a,b),c)])==(leq[(a,imp(b,c))])   # residuation
            assert meet(a,join(b,c))==join(meet(a,b),meet(a,c))  # distributivity
print("A6 is a (complete, finite) RWK-algebra: all axioms verified.")
print("prelinearity (x->y) v (y->x) =", join(imp('x','y'),imp('y','x')), " (1 would mean prelinear)")
def fis(a,b): return neg[fus(neg[a],neg[b])]
p='p'; mult=[p]
for n in range(2,6): mult.append(fis(mult[-1],p))
print("multiples p,2p,3p,...:", mult, " all <= ~p =", neg[p], ":", all(leq[(m,neg[p])] for m in mult))
print("(2p) o (2p) =", fus(mult[1],mult[1]), "(nonzero => interacting infinitesimal)")
print("powers of q=~p:", [ 'q', fus('q','q'), fus(fus('q','q'),'q') ])
# drinker principle fails in the completed Chang chain: computed separately in notes
