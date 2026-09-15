"""Numerical check: every axiom of RWK (RW + K), with fusion defined as
A o B := ~(A -> ~B), is valid in the standard Lukasiewicz algebra [0,1].
Also checks that contraction (W) and excluded middle are NOT valid there,
and a few auxiliary inequalities used in the notes."""
import random, itertools

def imp(a,b): return min(1.0, 1.0-a+b)
def neg(a): return 1.0-a
def fus(a,b): return max(0.0, a+b-1.0)
def fis(a,b): return min(1.0, a+b)          # fission = ~(~a o ~b)
def con(a,b): return min(a,b)
def dis(a,b): return max(a,b)

axioms = {
 "A->A":                       lambda a,b,c: imp(a,a),
 "suffixing (A->B)->((B->C)->(A->C))": lambda a,b,c: imp(imp(a,b), imp(imp(b,c), imp(a,c))),
 "prefixing (A->B)->((C->A)->(C->B))": lambda a,b,c: imp(imp(a,b), imp(imp(c,a), imp(c,b))),
 "assertion A->((A->B)->B)":   lambda a,b,c: imp(a, imp(imp(a,b), b)),
 "permutation (A->(B->C))->(B->(A->C))": lambda a,b,c: imp(imp(a,imp(b,c)), imp(b,imp(a,c))),
 "A&B->A":                     lambda a,b,c: imp(con(a,b), a),
 "A&B->B":                     lambda a,b,c: imp(con(a,b), b),
 "((A->B)&(A->C))->(A->(B&C))": lambda a,b,c: imp(con(imp(a,b),imp(a,c)), imp(a,con(b,c))),
 "A->AvB":                     lambda a,b,c: imp(a, dis(a,b)),
 "B->AvB":                     lambda a,b,c: imp(b, dis(a,b)),
 "((A->C)&(B->C))->((AvB)->C)": lambda a,b,c: imp(con(imp(a,c),imp(b,c)), imp(dis(a,b),c)),
 "distribution A&(BvC)->(A&B)vC": lambda a,b,c: imp(con(a,dis(b,c)), dis(con(a,b),c)),
 "contraposition (A->~B)->(B->~A)": lambda a,b,c: imp(imp(a,neg(b)), imp(b,neg(a))),
 "DNE ~~A->A":                 lambda a,b,c: imp(neg(neg(a)), a),
 "K  A->(B->A)":               lambda a,b,c: imp(a, imp(b,a)),
 "fusion residuation (A->(B->C))->((AoB)->C)": lambda a,b,c: imp(imp(a,imp(b,c)), imp(fus(a,b),c)),
 "fusion residuation converse":  lambda a,b,c: imp(imp(fus(a,b),c), imp(a,imp(b,c))),
 "aux: Ao(B+C) -> (AoB)+C":    lambda a,b,c: imp(fus(a,fis(b,c)), fis(fus(a,b),c)),
 "aux: AoB -> A&B (needs K)":  lambda a,b,c: imp(fus(a,b), con(a,b)),
 "aux: A o ~A -> B (multiplicative explosion, needs K)": lambda a,b,c: imp(fus(a,neg(a)), b),
}
non_theorems = {
 "contraction W (A->(A->B))->(A->B)": lambda a,b,c: imp(imp(a,imp(a,b)), imp(a,b)),
 "excluded middle Av~A":       lambda a,b,c: dis(a,neg(a)),
 "A&B -> AoB":                 lambda a,b,c: imp(con(a,b), fus(a,b)),
 "additive explosion A&~A->B": lambda a,b,c: imp(con(a,neg(a)), b),
 "prelinearity (A->B)v(B->A) [valid in L, NOT an RWK axiom]": lambda a,b,c: dis(imp(a,b),imp(b,a)),
}
random.seed(1)
grid = [i/20 for i in range(21)]
pts = list(itertools.product(grid,grid,grid)) + [(random.random(),random.random(),random.random()) for _ in range(20000)]
for name,f in axioms.items():
    m = min(f(*p) for p in pts)
    print(f"{'VALID  ' if m > 1-1e-9 else 'FAILS  '} min={m:.3f}  {name}")
print()
for name,f in non_theorems.items():
    m = min(f(*p) for p in pts)
    print(f"{'VALID  ' if m > 1-1e-9 else 'FAILS  '} min={m:.3f}  {name}")

# The Restall sentence: C <-> exists n ~(C^n).  Value of RHS as a function of c in [0,1]:
print("\nRestall sentence in [0,1]: c -> sup_n (1 - c^n)  (c^n = n-fold fusion)")
for c in [0,0.25,0.5,0.9,0.99,0.999,1.0]:
    powers=[c]; 
    for _ in range(2000): powers.append(fus(powers[-1],c))
    print(f"  c={c:<6} sup_n ~(c^n) = {max(1-x for x in powers):.3f}")
