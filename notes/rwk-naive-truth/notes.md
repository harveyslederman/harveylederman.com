# Working notes: RWK and naive truth

These are the working notes behind `writeup.md`. They record definitions, the
literature I could confirm, the derivations and proofs I checked, the attempts
that failed, and the precise form of what remains open. Everything marked
**[verified]** I checked by hand (and, where it is a finite computation, by the
script `check_rwk_in_L.py`). Everything marked **[reported]** is taken from
abstracts or secondary summaries; I could not open the full papers from this
session (fetching from the journal and preprint sites was blocked), so I flag
where a detail would need to be checked against the source.

---

## 0. Summary of conclusions (details below)

1. RWK is a sublogic of infinite-valued Łukasiewicz logic Ł (propositional and
   first-order, with the constant-domain quantifier axioms). **[verified]**
2. Therefore RWK is compatible with naive truth *as a schema*: the theory
   RWK + PA (T-free induction) + { T⟨A⟩ ↔ A : A a sentence } is non-trivial,
   is negation-consistent, and stays so if one adds the T-rules and
   intersubstitutivity of T⟨A⟩ and A in all contexts. This follows from
   Hájek–Paris–Shepherdson (2000) and (1), and I reconstruct the
   finite-subset argument so the conclusion does not rest on trust. **[verified modulo HPS]**
3. What does *not* follow is the good news: the negative Łukasiewicz results
   (no standard model; ω-inconsistency; inconsistency of compositional truth;
   inconsistency of truth-induction) do not automatically transfer to the weaker
   logic RWK. For the "no standard model" question I prove three partial
   negative results (complete chains, complete prelinear algebras, twist
   products over complete chains), and reduce the general question to a
   concrete algebraic problem (P) in §6. The general case is open.
4. Naive *comprehension* (property theory) over RWK is a different question.
   Its status over Ł is itself open (White's 1979 proof has a flaw found by
   Terui in 2014), Grišin's cut-elimination consistency proof does not cover
   distribution, and I know of no proof either way for RWK. Open.

---

## 1. The logic RWK

**RW** is the relevant logic R without contraction. Axioms (Anderson–Belnap
style), with rules modus ponens and adjunction:

```
A1  A → A
A2  (A → B) → ((B → C) → (A → C))            suffixing
A3  A → ((A → B) → B)                        assertion
A4  (A ∧ B) → A,   (A ∧ B) → B
A5  ((A → B) ∧ (A → C)) → (A → (B ∧ C))
A6  A → (A ∨ B),   B → (A ∨ B)
A7  ((A → C) ∧ (B → C)) → ((A ∨ B) → C)
A8  (A ∧ (B ∨ C)) → ((A ∧ B) ∨ C)            distribution
A9  (A → ¬B) → (B → ¬A)                      contraposition
A10 ¬¬A → A
```
R adds W: (A → (A → B)) → (A → B). **RWK** = RW + K: A → (B → A).

Definable: fusion A ∘ B := ¬(A → ¬B), fission A ⊕ B := ¬A → B,
biconditional A ↔ B := (A → B) ∧ (B → A). Residuation
(A → (B → C)) ↔ ((A ∘ B) → C) holds in RW.

Facts about RWK that matter here **[verified]**:

* t (the Ackermann constant) is the top element: from K, t → (A → t), so ⊢ A → t.
  So RWK-algebras are *integral*: the designated value is the top.
* A ∘ B → A ∧ B (from K via residuation, plus commutativity). The converse
  A ∧ B → A ∘ B is equivalent to contraction and fails.
* Multiplicative explosion: ⊢ (A ∘ ¬A) → B, equivalently ⊢ A → (¬A → B).
  Proof: K gives (A → A) → (¬B → (A → A)); MP with A1 gives ⊢ ¬B → (A → A);
  contrapose: ⊢ ¬(A → A) → B; and ¬(A → A) = A ∘ ¬A.
  So RWK is *not* paraconsistent at the level of rules: ⊢ A and ⊢ ¬A give ⊢ B.
  Additive explosion (A ∧ ¬A) → B is still not a theorem.
* Consequently excluded middle is fatal for naive truth in RWK: with a liar
  L ↔ ¬L, ⊢ L ∨ ¬L yields ⊢ L (from (L ∨ ¬L) → L) and ⊢ ¬L, hence
  everything. (The same holds for any consistent-looking extension of RWK
  that proves an instance of LEM for a liar.)

**Algebraic semantics.** RWK-algebras are bounded, integral, commutative,
involutive (¬¬x = x), distributive residuated lattices. In the fuzzy-logic
literature these are "involutive FL_ew-algebras that are distributive";
adding prelinearity (x → y) ∨ (y → x) = 1 gives IMTL-algebras; adding
divisibility as well gives MV-algebras, the algebras of Ł. So

    RWK  ⊂  IMTL  ⊂  Ł

as logics, with the first inclusion "prelinearity" and the second
"divisibility" (or, over IMTL, Łukasiewicz's axiom ((A→B)→B) → ((B→A)→A)).

**First-order RWK (RWKQ).** Standard quantifier axioms: ∀xA → A(t/x);
∀x(A → B) → (A → ∀xB) (x not free in A); the constant-domain axiom
∀x(A ∨ B) → (A ∨ ∀xB) (x not free in A); dual axioms for ∃; rule of
generalization.

---

## 2. Theorem A: RWK ⊆ Ł  [verified]

The standard Łukasiewicz algebra on [0,1]: ¬x = 1 − x, x → y = min(1, 1 − x + y),
∧ = min, ∨ = max, so x ∘ y = max(0, x + y − 1), x ⊕ y = min(1, x + y).
Quantifiers: ∀ = inf, ∃ = sup (over the domain).

Every axiom A1–A10 and K is valid (takes value 1 identically) in [0,1], and
MP, adjunction and generalization preserve value 1. The script
`check_rwk_in_L.py` checks each axiom on a grid plus 20,000 random points;
all are valid; contraction, excluded middle, A∧B → A∘B and additive
explosion fail (min value 1/2). Conceptually: A1–A3, A9, A10 and residuation
hold in any commutative involutive residuated lattice; A4–A7 in any lattice;
A8 because MV-algebras are distributive lattices; K because MV-algebras are
integral.

For the quantifier axioms: ∀xA → A(t) and ∀x(A→B) → (A → ∀xB) are valid in
every complete residuated lattice with ∀ = inf. The constant-domain axiom
∀x(A ∨ B) → (A ∨ ∀xB) needs inf_i (a ∨ b_i) = a ∨ inf_i b_i, which holds in
every complete *chain*, in particular in [0,1]. (Note for later: in a
non-linear complete RWK-algebra this axiom is *not* automatic; it holds in
completely distributive lattices, e.g. all the twist products of §6.)

So: every theorem of RWKQ is a theorem of Ł∀ (standard semantics), and every
derivation in RWKQ from a set of premises is a derivation in Ł∀ from the same
premises. This is the only thing needed for Theorem B.

Remark. Prelinearity (A → B) ∨ (B → A) is valid in [0,1] but is not an RWK
theorem (RWK has non-linear models such as any Boolean algebra with ∘ = ∧,
or the twist products of §6). This is exactly the gap that matters in §6.

---

## 3. Theorem B: naive truth as a schema is consistent over RWK

### 3.1 What HPS proved [reported, abstract-level]

Hájek, Paris and Shepherdson, "The liar paradox and fuzzy logic", *JSL* 65
(2000) 339–346. Setting: crisp Peano arithmetic PA, a possibly many-valued
predicate Tr(x), the *dequotation schema* φ ≡ Tr(⌜φ⌝) for every sentence φ,
all in Łukasiewicz infinitely valued logic; induction only for Tr-free
formulas ("PAŁTr"). Results as stated in the abstract:

* the resulting theory is **consistent**;
* it has **no standard model**;
* it becomes **inconsistent if Tr is required to commute with the
  propositional connectives**.

Related: Restall, "Arithmetic and truth in Łukasiewicz's infinitely valued
logic", *Logique et Analyse* 140 (1992) 303–312, shows the theory of truth
over Ł with arithmetic is ω-inconsistent [reported]; Bacon, "Curry's paradox
and ω-inconsistency", *Studia Logica* 101 (2013) 1–9, gives a proof-theoretic
analysis and "identifies two natural subsystems of Łukasiewicz logic which
individually, but not jointly, lack the problematic feature" [reported; I
could not confirm which two subsystems, see §7].

### 3.2 A self-contained reconstruction of the consistency argument

I want the positive result not to rest on a citation, so here is the argument
as I reconstruct it. Let 𝒯 be the set of all instances T⟨φ⟩ ↔ φ (φ a sentence
of L_PA + T, possibly with quantifiers and nested T). Claim: every finite
subset F ⊆ 𝒯 has a model with domain the standard naturals and
[0,1]-valued T.

Proof sketch. Let φ_1, …, φ_n be the sentences whose biconditionals are in
F, with codes c_1, …, c_n. Fix T(c) := 0 (any value) for every code c not among
the c_i, and treat the values v = (T(c_1), …, T(c_n)) ∈ [0,1]^n as unknowns.
Every sentence ψ gets a value ‖ψ‖(v) by the Tarski clauses with the
Łukasiewicz truth functions, ∀ = inf, ∃ = sup. Define
F(v) := (‖φ_1‖(v), …, ‖φ_n‖(v)). A fixed point v = F(v) makes every
biconditional in F take value 1.

Continuity of F. Each Łukasiewicz connective is 1-Lipschitz in each argument,
so a quantifier-free formula with k occurrences of the unknown atoms is
k-Lipschitz in v (sup norm). An instance ψ(m) of a quantified subformula
∀xψ(x) contains at most as many atom occurrences as ψ, whichever code the
term evaluates to; so the family {‖ψ(m)‖ : m ∈ ℕ} is *uniformly* Lipschitz,
and inf/sup of a uniformly L-Lipschitz family is L-Lipschitz. By induction on
formula complexity, every ‖ψ‖ is Lipschitz in v, hence continuous. Brouwer's
theorem gives a fixed point. □

Consequences. (i) PAŁTr is consistent (a derivation of 0 = 1 uses finitely many
axioms, and Ł∀ is sound for [0,1]-models; the model has standard ℕ so every
T-free induction instance and every true arithmetical sentence holds).
(ii) The same model witnesses that intersubstitutivity holds for the finitely
many sentences it was built for: T⟨φ_i⟩ and φ_i have the same value, so any
formula and the result of substituting one for the other agree in value.
Hence the *rule* forms of naive truth (T-Intro, T-Elim, intersubstitutivity in
all contexts) are also consistent: a derivation uses finitely many such steps.
(iii) The theory is negation-consistent: ⊢ A and ⊢ ¬A would force a = 1 = 1 − a.

Caveat on what the finite trick does *not* give. It handles biconditionals
*sentence by sentence*. A **uniform** disquotation axiom with a parameter,
∀x (T⟨φ(ẋ)⟩ ↔ φ(x)), constrains infinitely many T-values at once, and the
map v ↦ F(v) is then a map on [0,1]^ℕ whose coordinates involve sups over
infinitely many coordinates; these are not continuous in the product topology,
so Brouwer/Schauder does not apply. This is exactly why naive *comprehension*
(∀x(x ∈ {y:φ} ↔ φ(x)), every instance uniform) is a much harder problem — see §8.

### 3.3 Transfer to RWK  [verified given 3.1/3.2]

By Theorem A, any RWKQ-derivation from finitely many members of 𝒯 (or using
finitely many T-rule/intersubstitutivity steps) is an Ł∀-derivation from the
same. So:

**Theorem B.** RWKQ + PA (T-free induction) + naive truth (schema, T-rules,
intersubstitutivity) is non-trivial and negation-consistent. Every finite
fragment of it has a model with standard ℕ and [0,1]-valued T.

Corollaries.
* No RWK-definable connective ⇒ can be used to run a Curry-style argument to
  triviality from the T-schema: any such derivation would be an Ł-derivation,
  contradicting HPS. So RWK is "robustly contraction free" (Restall 1993's
  notion) at least as far as naive truth is concerned. (Rogerson and Butchart
  2002 show robust contraction-freedom is not *sufficient* for naive
  comprehension in general; that is a different direction.)
* The liar L ↔ ¬L is harmless: value 1/2; the theory proves neither L nor ¬L.
* Every n-Curry sentence K_n ↔ (K_n →_n ⊥) (n antecedents) is harmless: value n/(n+1).

---

## 4. What the theory proves and does not prove about Restall's sentence  [verified]

Fix, by the diagonal lemma plus the recursion theorem, a term τ(x) and a
sentence C such that (with D(n) := T(τ(n̄)) )

```
C  ↔  ∃x ¬T(τ(x))
D(1) ↔ C,     D(n+1) ↔ (C ∘ D(n))          (each n, as schema instances)
```
so that in any model D(n) has the value of the n-fold fusion Cⁿ for standard n.
In the [0,1] semantics with standard domain: ‖∃x¬T(τ(x))‖ = sup_n (1 − cⁿ),
which is 1 if c < 1 and 0 if c = 1 (script output). No fixed point: this is
the HPS/Restall "no standard model" phenomenon.

Derivable in RWKQ + 𝒯 (no arithmetic needed beyond the coding):
* ¬T(τ(n)) → ∃x¬T(τ(x)) → C, so ⊢ ¬D(n) → C and, contraposing,
  ⊢ ¬C → Cⁿ for every n. Uniformly: ⊢ ∀x(¬T(τ(x)) → C), hence
  ⊢ ¬C → ∀x T(τ(x)).
* ⊢ D(n+1) → D(n) (weakening: A ∘ B → A). So Cⁿ⁺¹ → Cⁿ.
* n = 1 gives ⊢ ¬C → C, i.e. ⊢ C ⊕ C.

Not derivable: C itself. Every finite subset of 𝒯 containing
C ↔ ∃x¬T(τ(x)) and the biconditionals for D(1),…,D(N) has a standard
[0,1]-model with c = N/(N+1): put T(τ(k)) := 1 for k > N; then
‖∃x¬T(τ(x))‖ = 1 − c^N = 1 − (Nc − N + 1) and c = N/(N+1) solves c = 1 − c^N.
(Check: c^N = 1/(N+1).) In this model ¬C → Cⁿ has value 1 exactly for n ≤ N,
matching what those N axioms prove. Since derivations are finite and Ł∀ is
sound, RWKQ + 𝒯 ⊬ C, and a fortiori the theory does not prove ⊥.

So the Restall sentence does not produce a *syntactic* ω-inconsistency of the
naive form "⊢ Cⁿ for all n and ⊢ ∃x¬T(τ(x))" from the schema alone. Whatever
Restall's/Bacon's syntactic ω-inconsistency uses (uniform disquotation,
induction on T-formulas, or a cleverer sentence), it is not this. [The precise
hypotheses of those two papers are the main thing I could not check.]

Remark (uniform recursion is not by itself fatal, even over Ł). If one adds
the *uniform* axioms ∀x(D(x+1) ↔ (C ∘ D(x))) and D(1) ↔ C, there is still a
[0,1]-valued model with a nonstandard domain: c = 1, D = 1 on the standard
part, D = 0 on some nonstandard galaxy (galaxies are closed under successor
and predecessor, so the recursion holds everywhere). Then ∃x¬D(x) = 1 = c.
The model thinks a nonstandard power of C is false while every standard power
is true. This is the shape the HPS "no standard model" result forces.

---

## 5. Which Łukasiewicz negatives do and do not transfer to RWK

Because RWK ⊂ Ł, *positive* results about Ł-models transfer downward and
*negative* results about derivability transfer upward, but not the other way:

| Result about Ł + naive truth | Direction | Status for RWK |
|---|---|---|
| Schema consistent (HPS) | models transfer down | **holds** (Thm B) |
| No standard [0,1]-model (HPS, Restall) | about *one* algebra | does not transfer; see §6 |
| ω-inconsistent (Restall; Bacon proof-theoretic) | derivation in Ł | transfers only if the derivation uses only RWK principles — **unknown to me** |
| Inconsistent if Tr commutes with connectives (HPS) | derivation in Ł | same — **unknown** |
| Inconsistent with full induction (HPS/Restall, reported) | derivation in Ł | same — **unknown** |

The obvious suspects for "Ł-only" principles in those derivations are
prelinearity (A→B) ∨ (B→A) and its consequences such as ¬Aⁿ ∨ ¬(¬A)ⁿ
(n ≥ 2), and Łukasiewicz's A ∨ B ↔ ((A→B)→B), which makes
"C ∨ D(n)" equivalent to "D(n+1) → D(n)" for D(n) = ¬Cⁿ. None of these is an
RWK theorem. If Bacon's two "individually harmless" subsystems are
(a) Ł without weakening-type principles and (b) Ł without linearity-type
principles, then RWK sits inside (b) and would inherit its harmlessness; but
I could not confirm the identity of the subsystems.

---

## 6. Standard models over general RWK-algebras: partial results and the crux

Question. Is there a *complete* RWK-algebra 𝔸 and a valuation with standard ℕ
making all of naive truth true? A necessary condition is a fixed point for the
Restall sentence, i.e. an element c with c = sup_n ¬(cⁿ) = ¬ inf_n cⁿ.
Writing q := c and p := ¬q this is

    (P)   p = inf_n qⁿ   (equivalently, by De Morgan,  ¬p = sup_n n·p,
          where n·p is the n-fold fission p ⊕ … ⊕ p).

Everything below is **[verified]** by hand.

**Lemma 6.1 (basic facts about any solution).** In any complete involutive
FL_ew-algebra, if p = inf_n qⁿ with p = ¬q, then:
(a) p ∘ q = 0 and p ∘ p = 0;
(b) the powers strictly decrease: qⁿ > qⁿ⁺¹ for all n (if qⁿ = qⁿ⁺¹ then
    qⁿ = p, so qⁿ⁺¹ = q ∘ p = 0, so p = 0, q = 1, qⁿ = 1 ≠ 0);
(c) n·p ≤ ¬p for all n, and (n·p) ∘ p = 0 ("p is infinitesimal");
(d) (n·p) ∘ (m·p) ≤ (n−1)·p, using x ∘ (y ⊕ z) ≤ (x ∘ y) ⊕ z, which holds in
    every involutive commutative residuated lattice (unfold ⊕ as ¬z → y and
    use modus ponens);
(e) **some (n·p) ∘ (m·p) ≠ 0 with n, m ≥ 2.** Otherwise n·p ≤ ¬(m·p) for all
    n, m, so s := sup n·p ≤ inf_m ¬(m·p) = ¬s, i.e. ¬p ≤ p; with p ≤ ¬p this
    gives p = ¬p, hence 2·p = ¬(p ∘ p) = ¬0 = 1, so ¬p = s = 1, p = 0,
    contradicting p = ¬p.

(e) says: a solution needs an "infinitesimal" p whose multiples nevertheless
interact multiplicatively. That never happens in a chain, which drives the
next results.

**Proposition 6.2 (no solution in a complete chain).** Let 𝔸 be a complete
linearly ordered involutive FL_ew-algebra. Since inf qⁿ = p and 𝔸 is a chain,
every x > p lies above some qᵐ. Take x = ¬(q²) > ¬q = p (by 6.1(b)). Then
qᵐ ≤ ¬(q²) for some m, so qᵐ ∘ q² = 0, so p = inf ≤ qᵐ⁺² = 0, so q = 1 and
qⁿ = 1 ≠ 0 = p. Contradiction. □
(This covers the nonstandard MV-chains used in the general semantics of Ł∀,
which is the setting of Hájek's and Yatabe's ω-inconsistency remarks on CŁ0.)

**Proposition 6.3 (no solution in a complete prelinear algebra).** Let 𝔸 be a
complete IMTL-algebra (in particular any complete MV-algebra). Prelinear
algebras are subdirect products of chains. In each chain quotient the image
of p still satisfies n·p̄ ≤ ¬p̄ for all n, and in a chain two such elements
u ≤ v satisfy u ∘ v ≤ v ∘ v = 0. So (n·p) ∘ (m·p) = 0 in every quotient,
hence in 𝔸, contradicting 6.1(e). □

So: **over every complete chain and every complete prelinear RWK-algebra,
naive truth has no standard model.** The Ł result is not about [0,1]
specifically; it is about linearity. The open case is precisely the
non-prelinear complete RWK-algebras, and the *only* thing that separates them
from IMTL is the axiom (A → B) ∨ (B → A) that RWK lacks.

**A family of non-prelinear complete RWK-algebras: twist products.** For a
complete distributive commutative integral residuated lattice L (not
necessarily involutive) put

    K(L) := { (a, b) ∈ L × L : a ∘ b = 0 },   ordered by (a,b) ≤ (c,d) iff a ≤ c and b ≥ d,
    (a,b) ∘ (c,d) := (a ∘ c, (a → d) ∧ (c → b)),   ¬(a,b) := (b,a),
    top = unit = (1,0), bottom = (0,1).

Checked: closure under ∘, ∧, ∨, ¬ and arbitrary sups/infs (componentwise);
associativity and commutativity; residuation, with
(a,b) → (c,d) = ((a→c) ∧ (d→b), a ∘ d); involutivity (¬ is the residual
negation because b ≤ ¬a on K(L)); distributivity inherited from L;
integrality. So K(L) is a complete RWK-algebra, and it is *not* prelinear
in general (already for L a two-element chain plus a middle point one gets
Nelson-style non-linear algebras). This is the standard twist-product
construction (Kalman; Tsinakis–Wille; Busaniche–Cignoli) restricted to the
"a ∘ b = 0" part so that the unit is the top.

Powers in K(L): for s = (a, b), sⁿ = (aⁿ, aⁿ⁻¹ → b) (induction; the two
components of the second coordinate coincide). So (P) for s becomes a pair of
conditions in L:

    (1)  inf_n aⁿ = b,        (2)  sup_n (aⁿ⁻¹ → b) = a,    with a ∘ b = 0.

**Proposition 6.4 (no solution in K(L) for L a complete chain).** Suppose
(1),(2). If a² = a then b = a and a ∘ b = a, so a = 0 and s = (0,0), whose
powers are (0,1) for n ≥ 2, so inf sⁿ = (0,1) ≠ (0,0) = ¬s. So a² < a. Let
c_n := aⁿ⁻¹ → b; these increase with sup a in the chain L, so some c_k > a².
Then aᵏ⁺¹ = aᵏ⁻¹ ∘ a² ≤ aᵏ⁻¹ ∘ c_k ≤ b, so aᵏ⁺¹ = b, so aᵏ⁺² = a ∘ b = 0,
so b = 0. But then c_j = ¬_L(aʲ⁻¹) = ¬_L 0 = 1 for large j, and c_j ≤ a
forces a = 1, contradicting b = inf aⁿ = 0. □

So the simplest non-prelinear complete RWK-algebras also fail. What is still
open is whether *some* complete distributive involutive FL_ew-algebra solves
(P) — for instance K(L) for a non-linear L, or iterated twists, or something
not of twist form. If none does, then

    "RWK + naive truth has no standard model"

holds in full generality and the Ł "no standard model" result is really a
theorem about *all* of RWK. If one does, then the next question is whether
that algebra supports a *simultaneous* fixed point for all sentences, which
would need a fixed-point theorem replacing Brouwer (the obstacle being that
sups over infinitely many coordinates are not continuous). Either outcome
would be new, as far as I can tell.

Failed attempt worth recording. I tried to build a solution directly as a
countable poset {0, 1, aₖ = qᵏ, bₖ = k·p} with bⱼ ≤ aₖ iff j = 1 or k = 1 or
j + k ≤ N (this is forced up to the choice of the "interaction" relation by
6.1(e) and the sup/inf requirements). The lattice part is fine; the problem
is defining ∘ on the bⱼ's associatively: the natural Ł-style guess
bⱼ ∘ bₖ = b_{j+k−N} conflicts with associativity against aᵢ ∘ b_{i+1} = b₁ and
b₁ ∘ bₖ = 0. Several patches (taking minima with j−1, k−1) also fail
associativity. I do not take this as evidence either way; the search space is
large.

---

## 7. Bacon's "two subsystems" — what I could and could not confirm

Abstract [reported]: "In recent years there has been a revitalised interest in
non-classical solutions to the semantic paradoxes. In this paper I show that a
number of logics are susceptible to a strengthened version of Curry's paradox.
This can be adapted to provide a proof theoretic analysis of the
ω-inconsistency in Łukasiewicz's continuum valued logic, allowing us to better
evaluate which logics are suitable for a naïve truth theory. On this basis I
identify two natural subsystems of Łukasiewicz logic which individually, but
not jointly, lack the problematic feature."

If one of the two subsystems is RWK (or contains it), then RWK's naive truth
theory avoids Bacon's strengthened Curry / ω-inconsistency argument and the
question in the write-up's title has a sharper positive answer than Theorem B.
If instead the strengthened Curry goes through with only RWK principles plus
uniform disquotation, then RWK + uniform naive truth is ω-inconsistent. This
is the single most valuable thing to check against the paper. My own analysis
in §4–§5 suggests the argument must use something beyond the sentence-by-
sentence schema, and that the Ł-specific ingredients are linearity-type
principles, but that is inference, not confirmation.

---

## 8. Naive comprehension / property theory over RWK

Different question, different status.

* Grišin (1974/1982): naive comprehension is consistent over *affine* linear
  logic without exponentials (MALL + weakening), by cut elimination; Cantini
  (2003) proves that theory undecidable and repairs the cut-elimination
  argument. Adding extensionality yields contraction and triviality
  (Grišin's paradox). [reported; well known]
* RWK is *not* covered by Grišin: RWK has distribution A ∧ (B ∨ C) →
  (A ∧ B) ∨ C, which MALL lacks, and the constant-domain axiom. A sequent
  calculus for RWK with cut elimination would be Dunn–Mints style (two
  structural connectives) or a display calculus; whether naive comprehension
  can be added to such a calculus with cut elimination is not something I
  know to have been done.
* Over Ł: White (1979) claimed consistency of the Cantor–Łukasiewicz set
  theory CŁ0 (full comprehension, no extensionality); Hájek's later papers
  (2005, 2013) note the proof was criticised as having a gap, and "in 2014
  Kazushige Terui communicated a serious flaw in White's proof, and the
  problem thus seemingly remains unsettled" [reported]. So the downward
  transfer to RWK that works for naive *truth* is unavailable for naive
  *comprehension*. Hájek (2005) also shows CŁ0 is inconsistent with induction
  on a simple schema for natural numbers, and Yatabe shows nonstandard
  numbers are forced (ω-inconsistency in the general semantics).
* Hanson (JSL, "A metric set theory with a universal set") compares his metric
  set theory MSE with CŁ0 and gives a consistent approximate-comprehension
  theory in continuous logic / Ł∀ [reported].
* Field, Lederman and Øgaard, "Prospects for a naive theory of classes",
  *NDJFL* 58 (2017): consistency of Brady-style and Bacon-style naive class
  theories with weak extensionality, and an impossibility result showing
  modest extensionality demands cannot be jointly met [reported, abstract].
  Nothing there settles the RWK comprehension question either way as far as I
  can tell from the abstract.

Net: naive comprehension over RWK is open, and open in both directions — the
Ł-based route to consistency is currently broken (White), and the
cut-elimination route is not known to survive distribution.

---

## 9. Consolidated open problems

1. **(Standard model)** Does some complete distributive involutive
   FL_ew-algebra solve (P): an element p ≠ 0 with sup_n n·p = ¬p? Negative
   for all complete chains, all complete prelinear algebras, and twist
   products over complete chains (§6). A general negative answer would give:
   RWK + naive truth has no standard model, over any complete RWK-algebra.
2. **(Syntactic ω-consistency)** Is RWKQ + PA (T-free induction) + the naive
   truth schema ω-consistent? The schema-only theory does not prove Restall's
   C (§4). Whether Restall's/Bacon's derivation goes through in RWK depends on
   which principles it uses; check Bacon 2013.
3. **(Uniform / compositional truth)** Is RWK consistent with uniform
   disquotation ∀x(T⟨φ(ẋ)⟩ ↔ φ(x)), or with T commuting with the connectives
   and quantifiers? Over Ł the latter is inconsistent (HPS). Over RWK: unknown.
   Note that some uniform recursions are harmless even over Ł (§4, remark).
4. **(Truth in induction)** Is RWK + naive truth consistent with the full
   induction schema (T allowed)? Over Ł, reportedly not. Over RWK: unknown.
5. **(Comprehension)** Is naive comprehension consistent over RWKQ? Open in
   both directions (§8).
6. **(Classes)** Given the Field–Lederman–Øgaard impossibility result, is there
   any extensionality principle that RWK can add to naive comprehension
   without triviality? Presumably subject to the same impossibility, but the
   result's hypotheses would need to be checked against RWK.

---

## 10. Sources I relied on

Accessible in this session only through search summaries / abstracts (fetching
full texts from journal and preprint sites was blocked):

* P. Hájek, J. Paris, J. Shepherdson, "The liar paradox and fuzzy logic",
  *J. Symbolic Logic* 65 (2000) 339–346.
* G. Restall, "Arithmetic and truth in Łukasiewicz's infinitely valued logic",
  *Logique et Analyse* 140 (1992) 303–312.
* G. Restall, "How to be really contraction free", *Studia Logica* 52 (1993) 381–391.
* A. Bacon, "Curry's paradox and ω-inconsistency", *Studia Logica* 101 (2013) 1–9.
* A. Bacon, "A new conditional for naive truth theory", *NDJFL* 54 (2013) 87–104.
* S. Rogerson, S. Butchart, "Naïve comprehension and contracting implications",
  *Studia Logica* 71 (2002) 119–132.
* J. Slaney, "RWX is not Curry paraconsistent", in Priest–Routley–Norman (eds),
  *Paraconsistent Logic* (1989) 472–480.
* T. F. Øgaard, "Paths to triviality", *J. Philosophical Logic* 45 (2016) 237–276.
* H. Field, H. Lederman, T. F. Øgaard, "Prospects for a naive theory of classes",
  *NDJFL* 58 (2017) 461–506.
* R. White, "The consistency of the axiom of comprehension in the infinite-valued
  predicate logic of Łukasiewicz", *J. Philosophical Logic* 8 (1979).
* P. Hájek, "On arithmetic in the Cantor–Łukasiewicz fuzzy set theory",
  *Arch. Math. Logic* 44 (2005); "Some remarks on Cantor–Łukasiewicz fuzzy set
  theory", *Logic J. IGPL* 21 (2013) 183–186.
* S. Yatabe, "Distinguishing non-standard natural numbers in a set theory within
  Łukasiewicz logic", *Arch. Math. Logic* 46 (2007); "Comprehension contradicts
  to the induction within Łukasiewicz predicate logic", *Arch. Math. Logic* 48 (2009).
* A. Cantini, "The undecidability of Grišin's set theory", *Studia Logica* 74 (2003).
* B. Da Ré, L. Rosenblatt, "Contraction, infinitary quantifiers, and omega
  paradoxes", *J. Philosophical Logic* 47 (2018) 611–629.
* A. Fjellstad, J.-F. Olsen, "IKTω and Łukasiewicz-models", *NDJFL* (2021).
* J. Hanson, "A metric set theory with a universal set", *J. Symbolic Logic* (2023/24).
* G. Restall, *An Introduction to Substructural Logics* (Routledge 2000), for
  the RW/RWK axiomatics and terminology.

---
---

# Part II: ω-consistency (added after the follow-up question)

Notation. NT_Ł := Ł∀ + PA (crisp, induction for T-free formulas) + the
dequotation schema 𝒯 = { T⟨φ⟩ ↔ φ : φ a sentence }. NT_RWK := the same with
RWKQ in place of Ł∀. A theory is ω-inconsistent if for some φ(x) it proves
∃xφ(x) and proves ¬φ(n̄) for every n. Since RWKQ ⊆ Ł∀ (Theorem A),
NT_RWK ⊆ NT_Ł, so **ω-consistency of NT_Ł would imply ω-consistency of
NT_RWK, and ω-inconsistency of NT_RWK would imply ω-inconsistency of NT_Ł.**

## 11. Theorem Ω: NT_Ł is ω-inconsistent (with an explicit witness)  [verified]

This is the result attributed to Restall (1992); I could not read his paper,
so here is a complete proof from the schema alone. No uniform disquotation,
no induction on T-formulas, no ω-rule is used.

Setup as in §4: C ↔ ∃x¬T(τ(x)), with T(τ(1)) ↔ C and
T(τ(n+1)) ↔ (C ∘ T(τ(n))) as schema instances, so that in every model
D(n) := ‖T(τ(n))‖ equals cⁿ for standard n, where c := ‖C‖. Write p := ¬c.
By the first biconditional, c = sup_m ¬D(m) over the whole domain, i.e.

    p = inf_m D(m)      (over all m in the domain, standard or not).      (†)

**Witness.**   φ(x) := (T(τ(x)) → ¬C) ∘ (T(τ(x)) → ¬C).

**Claim 1: NT_Ł ⊢ ¬φ(n̄) for every n.**
¬φ(n) is (T(τ(n)) → ¬C) → ¬(T(τ(n)) → ¬C), i.e. ¬Cⁿ⁺¹ → Cⁿ⁺¹ after
unfolding (T(τ(n)) → ¬C = ¬(Cⁿ ∘ C) = ¬Cⁿ⁺¹). By §4, NT_Ł ⊢ ¬C → Cᵏ for
every k. Propositional Ł proves the inference

    ¬C → C^{2n+2}   ⊢   ¬Cⁿ⁺¹ → Cⁿ⁺¹ ,

because the corresponding quasi-identity "x ∘ (2n+2)·x = 0 ⟹
((n+1)·x) ∘ ((n+1)·x) = 0" holds in every MV-chain (in the group
representation Γ(G,u): x ∘ (2n+2)x = 0 forces (2n+3)x ≤ u, hence
(2n+2)x ≤ u, hence (n+1)x ∘ (n+1)x = 0), hence in every MV-algebra
(subdirect products of chains), hence is derivable in Ł, which is
algebraizable with the MV-algebras as its equivalent algebraic semantics.
So NT_Ł ⊢ ¬φ(n̄). □

**Claim 2: NT_Ł ⊢ ∃xφ(x).**
Semantic proof, using Hájek's strong completeness of Ł∀ for theories
w.r.t. safe models over MV-chains. Let M be any safe MV-chain model of 𝒯,
with values in the chain [0,u] ⊆ G (G a totally ordered abelian group).
Since D(m) ≥ p for all m by (†), D(m) → p = u − D(m) + p, so
sup_m (D(m) → p) = u − inf_m D(m) + p = u by (†) (order-reversing translation
preserves infs/sups in a totally ordered group; safety guarantees the sup
exists as the value of ∃x(T(τ(x)) → ¬C)). Put y_m := D(m) → p, so
sup y_m = u and ‖φ(m)‖ = y_m ∘ y_m = max(0, 2y_m − u). If some y_m = u we are
done. Otherwise e_m := u − y_m > 0 with inf e_m = 0; if t < u bounded every
2y_m − u then 2e_m ≥ u − t =: d > 0 for all m; in a non-discrete totally
ordered group every d > 0 has some g > 0 with 2g < d, and then e_m > g for
all m contradicts inf e_m = 0; a discrete group has no sequence of positive
elements with infimum 0. Hence sup_m ‖φ(m)‖ = u = 1. So ‖∃xφ(x)‖ = 1 in
every safe model of 𝒯, hence NT_Ł ⊢ ∃xφ(x). □

Syntactic route for Claim 2 (for the reader who prefers derivations):
(a) C ↔ ∃x¬T(τ(x)) (schema); (b) hence ¬C ↔ ∀xT(τ(x)); (c) the Ł∀ theorem
∃x(A(x) → ∀yA(y)) with A(x) := T(τ(x)) gives ∃x(T(τ(x)) → ¬C); (d) from
⊢ ∃xY(x) get ⊢ (∃xY) ∘ (∃xY) (fusion of theorems), then
⊢ ∃x∃x'(Y(x) ∘ Y(x')) (Ł∀ moves ∃ out of ∘), then, using prelinearity
(Y(x) → Y(x')) ∨ (Y(x') → Y(x)) and distribution of ∘ over ∨,
⊢ ∃x(Y(x) ∘ Y(x)) = ∃xφ(x).

**So NT_Ł proves ∃xφ(x) and refutes every instance: ω-inconsistent.**
This confirms the reported Restall result and shows it needs nothing beyond
the sentence-by-sentence schema. (§4's observation that NT_Ł ⊬ C is
compatible: the witness is not C.)

Remark. In every safe model, ¬c is an "infinitesimal" (¬c ∘ n·¬c = 0 for
all n), and the witness says "some power of C is as close to ¬C as ¬C is to
1, twice over"; standard powers are only infinitesimally close to 1, but
the infimum (†) forces a nonstandard power down to ¬c.

## 12. Exactly where the proof uses more than RWK  [verified]

The derivation uses two principles, both invalid in RWK, and I have a
concrete RWK-algebra refuting each.

**(α) Infinitesimals do not interact.** Claim 1 needs the inference
{¬C → Cᵏ : k ≥ 1} ⊢ ¬C² → C², i.e. the quasi-identity
"p ∘ k·p = 0 for all k ⟹ 2p ∘ 2p = 0". This holds in every prelinear
algebra (§6, Prop. 6.3) and fails in the following **6-element RWK-algebra
A₆**, verified by `verify_A6.py`:

    0 < p < x, y < q < 1,   x and y incomparable (a chain–diamond–chain),
    ¬: 0↔1, p↔q, x↔y,
    fusion on join-irreducibles: p∘p = p∘x = p∘y = 0, x∘x = x, x∘y = 0, y∘y = p,
    extended by join-preservation; 1 is the unit.

A₆ is a bounded integral commutative involutive distributive residuated
lattice (all residuated-lattice axioms machine-checked), it is not prelinear
((x→y) ∨ (y→x) = q ≠ 1), and p is an interacting infinitesimal: the
multiples are p, 2p = y, 3p = y, …, all ≤ ¬p = q, while 2p ∘ 2p = y ∘ y = p ≠ 0.
Interpreting C as q, every premise ¬C → Cᵏ holds (¬q = p ≤ q, x = qᵏ for k ≥ 2)
while ¬C² → C² = (y → x) fails. So the inference is not RWK-valid.

**(β) The drinker principle.** Claim 2 needs ∃x(A(x) → ∀yA(y)), valid in
all MV-chains, not a theorem of RWKQ. Counter-model: the **completed Chang
chain** 0 < ε < 2ε < … < ω < … < 1−2ε < 1−ε < 1 with
(1−jε)∘(1−kε) = 1−(j+k)ε, (1−jε)∘kε = (k−j)ε if k > j else 0,
(1−jε)∘ω = ω, and all products of elements ≤ ω equal 0. This is a complete
involutive residuated chain (associativity and sup-preservation checked by
cases; ¬ω = ω), hence an RWK-algebra, and it is not an MV-algebra. Take
A(n) := 1 − nε: inf_n A(n) = ω and A(n) → ω = ω for every n, so
sup_n (A(n) → inf_m A(m)) = ω ≠ 1.

(The squaring step in (d) also uses prelinearity; A₆ refutes that too.)

**Consequence.** The Łukasiewicz ω-inconsistency proof does not go through
in RWK: both of its non-RWK ingredients are refuted by RWK-algebras. This
is precisely the "individually harmless subsystems" phenomenon Bacon's
abstract describes; the two ingredients here are "prelinearity-type"
principles, which RWK lacks. **It does not show NT_RWK is ω-consistent.**
To show that one needs an RWK-model of *all* of 𝒯 in which the relevant
sentences take the "wrong" values, and neither A₆ nor the completed Chang
chain is known to carry such a model.

## 13. What ω-consistency of NT_RWK would require, and what is ruled out

**13.1 The ω-closure.** Let NT_RWK^ω be NT_RWK closed under the ω-rule
(from ⊢ φ(n̄) for all n infer ⊢ ∀xφ(x)).
* If NT_RWK is ω-inconsistent then NT_RWK^ω is trivial (it proves ∃xφ and
  ∀x¬φ, and RWK has multiplicative explosion, §1).
* NT_RWK^ω is non-trivial iff there is a **safe standard-domain
  RWK-model** of 𝒯: its Lindenbaum algebra, with the numerals as domain, is
  such a model (the ω-rule makes [∀xφ] = inf_n [φ(n̄)]), and conversely any
  such model is sound for the ω-rule.
So a safe standard-domain RWK-model of 𝒯 would prove NT_RWK ω-consistent,
and the natural way to prove ω-inconsistency is to show no such model exists
and then extract a witness. Every such model must solve the single equation
(P) of §6 for Restall's sentence, and (Lemma 6.1(e)) must contain interacting
infinitesimals. A₆ shows that ingredient is available in RWK; the difficulty
is combining it with infinitely descending powers whose infimum is ¬q.

**13.2 What is ruled out** (all [verified]):
1. complete chains, complete prelinear algebras (Props 6.2, 6.3);
2. twist products K(L) over complete chains, and K(K(M)) for M a chain (Prop 6.4 and the same argument one level up);
3. **the family A(C₁)**: for any chain C₁ with an order-reversing involution
   ν and a commutative associative sup-preserving integral operation ⋆
   whose orthogonality relation x ⋆ y = ⊥ ⟺ x ≤ ν(y) is balanced
   (Z(a⋆b,c) ⟺ Z(a,b⋆c)), the algebra {0,1} ∪ C₁×{0,1} with
   ¬(a,i) = (ν(a),1−i) and (a,i)∘(b,j) = 0 if [a ≤ ν(b) and i+j ≤ 1], else
   (a⋆b, 0), is a complete distributive involutive FL_ew-algebra (A₆ is the
   case C₁ = 2). In A(C₁) equation (P) reduces to inf_n a^{⋆n} = ν(a) with
   a^{⋆n} ≠ ⊥, which is impossible in a chain by the argument of Prop 6.2.
   (Join-preservation forces the orthogonal products to be ⊥, which is why
   a "threshold" variant with x ⋆ y ≤ θ does not work either.)
4. **ultraproducts followed by completion**: if A* = ∏ A_N / U and q = [q_N]
   has ¬q ≤ qⁿ for all standard n, then for every function k(N) → ∞ along U
   the element [q_N^{k(N)}] is a lower bound of all standard powers; requiring
   all of them to lie below ¬q forces the least exponent m(N) with
   q_N^{m(N)} ≤ ¬q_N to be bounded, hence q^{H+1} = 0 for a standard H. So no
   MacNeille completion of an ultraproduct of models of the relations solves (P).

**13.3 The most promising positive route.** Let F be the RWK-algebra
presented by one generator q and the relations ¬q ≤ qⁿ (n ≥ 1). (P) holds in
F iff every term t(q) with F ⊨ t ≤ qⁿ for all n satisfies F ⊨ t ≤ ¬q — an
"ω-rule admissibility" statement about the equational theory of RWK-algebras.
Every candidate term I tried (2p∘2p, 2p∘q, q^k ∧ 2p, (q→p)∘q, …) is
provably ≤ ¬q, and a counterexample would need a term that is a lower bound
of all powers in every model yet exceeds ¬q in some model like A₆, where
the only such elements are the stabilised powers, which are not provable
lower bounds. If (P) holds in F, then F, or its MacNeille completion, is a
safe RWK-algebra solving the Restall equation; the remaining task would be a
simultaneous fixed point for all sentences over it (a substitute for
Brouwer), which is the real obstacle in every non-Ł route.

## 14. Status of the ω-consistency question

| Theory | ω-consistent? | Evidence |
|---|---|---|
| NT_Ł (schema only) | **No** | Theorem Ω, witness (T(τ(x)) → ¬C)² |
| NT_RWK | **Open** | Theorem Ω's proof fails at two RWK-invalid steps (A₆, completed Chang); no RWK-model of 𝒯 outside the Ł-models is known; standard-domain models are ruled out over chains, prelinear algebras, twist products over chains, the family A(C₁), and completions of ultraproducts |
| NT_RWK^ω (ω-closure) | **Open**, equivalent to existence of a safe standard-domain RWK-model | §13.1 |

What I could not do: produce either a witness valid in *all* RWK-models of
𝒯, or a single RWK-model of 𝒯 that is not an Ł-model. The first would need
a provable existential in RWKQ + 𝒯 with all instances refutable, and RWKQ
proves very few existentials without witnesses (the drinker and its relatives
fail); the second needs a fixed-point theorem over a non-prelinear algebra.
My best guess is that NT_RWK is ω-consistent, because every mechanism that
produces the Ł witness is prelinearity-driven, but that is a guess, not a
theorem.
