# Is RWK compatible with naive truth?

*Final write-up. Working notes, proofs, failed attempts, and the source list are in `notes.md`; the numerical check of the key inclusion is `check_rwk_in_L.py`.*

## Short answer

Yes for naive truth as a **schema**, and this is not open: it follows from a theorem that is already in the literature once one notices a simple fact about RWK. What is open is everything stronger than the schema, and the open part has a sharper shape than I expected going in.

1. **RWK is a sublogic of infinite-valued Łukasiewicz logic Ł.** Every axiom of RWK, including K, holds in the [0,1] Łukasiewicz algebra, and the rules are shared. This extends to the first-order logics with the usual constant-domain quantifier axioms. (Checked by hand and by machine.)
2. **Hájek, Paris and Shepherdson (2000) proved that Ł with Peano arithmetic and the full dequotation schema T⟨φ⟩ ↔ φ is consistent.** So every RWK-derivation of triviality from finitely many T-biconditionals would be an Ł-derivation, which cannot exist. The theory RWK + PA (T-free induction) + naive truth is non-trivial and negation-consistent, and this survives adding the T-rules and full intersubstitutivity of T⟨A⟩ and A. Every finite fragment even has a model with the standard natural numbers.
3. **The bad news about Ł does not automatically follow for RWK.** Ł's naive truth theory has no standard model, is ω-inconsistent, and becomes inconsistent if truth commutes with the connectives. Those are results about Ł's stronger logic and Ł's specific algebra. For RWK they are open questions, and I can show that the "no standard model" result is really a theorem about *linearity*: it holds over every complete linearly ordered RWK-algebra and every complete prelinear one, but the non-prelinear case, which is exactly the extra room RWK has over Ł, is unresolved. I reduce it to a concrete algebraic problem.
4. **Naive comprehension is a different and harder question**, and it is open for RWK in both directions.

## What RWK is, and the one fact that does the work

RWK is the relevant logic R with contraction W removed and the weakening axiom K, A → (B → A), added. Two consequences of K matter here. First, the Ackermann constant t becomes the top element, so RWK-algebras are integral: bounded, integral, commutative, involutive, distributive residuated lattices. Second, RWK proves multiplicative explosion, (A ∘ ¬A) → B, so ⊢ A and ⊢ ¬A together give everything. RWK is therefore not paraconsistent at the level of rules, and excluded middle is fatal for it: a liar L ↔ ¬L plus L ∨ ¬L gives ⊢ L and ⊢ ¬L. RWK's chance with naive truth rests entirely on the absence of contraction.

In the terminology of fuzzy logic, RWK-algebras are the distributive involutive FL_ew-algebras. Adding prelinearity, (A → B) ∨ (B → A), gives the IMTL-algebras; adding divisibility as well gives the MV-algebras, which are the algebras of Ł. So as logics

    RWK  ⊂  IMTL  ⊂  Ł,

with prelinearity as the first gap and divisibility as the second. I verified each RWK axiom in the standard Łukasiewicz algebra by hand and numerically (grid plus 20,000 random points); contraction, excluded middle, A ∧ B → A ∘ B and additive explosion all fail there at value 1/2, as they should.

## Why the schema is consistent, without trusting anyone

I reconstructed the consistency argument so the conclusion does not depend on reading it off an abstract. Take any finite set of T-biconditionals, for sentences φ₁,…,φₙ with codes c₁,…,cₙ. Fix the value of T at every other code, and regard the values at c₁,…,cₙ as unknowns v ∈ [0,1]ⁿ. Each sentence gets a value by the Łukasiewicz truth functions with ∀ as infimum and ∃ as supremum over the standard naturals. The map v ↦ (‖φ₁‖(v),…,‖φₙ‖(v)) is continuous: every Łukasiewicz connective is 1-Lipschitz in each argument, the instances of a quantified subformula have a uniformly bounded number of unknown-atom occurrences, and infima and suprema of uniformly Lipschitz families are Lipschitz. Brouwer's theorem gives a fixed point, which is a standard-domain model of those finitely many biconditionals. Since derivations are finite and Ł∀ is sound for these models, no contradiction, and no arbitrary sentence, is derivable. The same finite model makes T⟨φᵢ⟩ and φᵢ agree in value, so intersubstitutivity steps for those sentences are sound too.

Two corollaries. The liar takes value 1/2 and the theory proves neither L nor ¬L. And no RWK-definable connective can be used for a Curry-style argument to triviality, since any such derivation would be an Ł-derivation. So RWK is "robustly contraction free" in Restall's (1993) sense as far as naive truth goes.

## Where the finite trick stops, and why that is where the open problems start

The argument is sentence-by-sentence. A **uniform** disquotation axiom with a parameter, ∀x(T⟨φ(ẋ)⟩ ↔ φ(x)), constrains infinitely many T-values at once, and suprema over infinitely many coordinates are not continuous in the product topology, so Brouwer no longer applies. That single fact explains the whole landscape:

- Hájek–Paris–Shepherdson: Ł's theory is consistent but has **no standard model**, and is **inconsistent if truth commutes with the connectives**.
- Restall (1992) and Bacon (2013): the theory is **ω-inconsistent**; Bacon gives a proof-theoretic version and, per his abstract, identifies two natural subsystems of Ł that individually but not jointly avoid the problem. I could not open the paper from this session to see which two. If one of them contains RWK, the title question has a sharper positive answer than the schema result. That is the single most useful thing to check next.
- Naive **comprehension** is uniform by nature. Over Ł its consistency was claimed by White (1979), but Hájek's later papers report a gap, and in 2014 Terui communicated a serious flaw; the problem is reported as unsettled. Grišin's cut-elimination consistency proof for naive comprehension covers affine linear logic without distribution, and RWK has distribution and the constant-domain quantifier axiom, so it is not covered either. Naive comprehension over RWK is open in both directions.

Because RWK is weaker than Ł, negative results about Ł transfer to RWK only if their derivations use only RWK principles. The obvious suspects for Ł-only ingredients are prelinearity and its consequences such as ¬Aⁿ ∨ ¬(¬A)ⁿ for n ≥ 2, and Łukasiewicz's A ∨ B ↔ ((A → B) → B). None of these is an RWK theorem.

## Restall's sentence in RWK

Let C be a sentence with C ↔ ∃x ¬T(τ(x)), where T(τ(n)) is provably equivalent to the n-fold fusion Cⁿ for each standard n. In the standard [0,1] semantics the right-hand side has value 1 if c < 1 and 0 if c = 1, so there is no fixed point: this is the "no standard model" phenomenon.

What RWKQ plus the schema actually proves about C: ⊢ ¬C → Cⁿ for every n, indeed uniformly ⊢ ¬C → ∀x T(τ(x)); ⊢ Cⁿ⁺¹ → Cⁿ by weakening; and in particular ⊢ ¬C → C. What it does not prove is C itself. Every finite subset of the schema that includes the biconditionals for C and for the first N powers has a standard-domain model with c = N/(N+1) (set T(τ(k)) = 1 for k > N). So the naive form of syntactic ω-inconsistency, "⊢ Cⁿ for all n and ⊢ ∃x ¬T(τ(x))", is not available from the schema alone, in RWK or in Ł. Whatever the published ω-inconsistency arguments use beyond the schema, this is the point at which RWK could come apart from Ł.

## Standard models over RWK-algebras: partial results and the crux

A standard model of RWK + naive truth over a complete RWK-algebra 𝔸 needs, at least, a fixed point for Restall's sentence: an element q with ¬q = inf_n qⁿ. Writing p = ¬q and using De Morgan, this is

**(P)** an element p ≠ 0 with sup_n n·p = ¬p, where n·p is the n-fold fission.

Three things I proved (details in the notes):

- In any solution the powers qⁿ strictly decrease, p is "infinitesimal" (n·p ≤ ¬p for all n), and yet **some (n·p) ∘ (m·p) ≠ 0 with n, m ≥ 2**. Infinitesimals whose multiples interact multiplicatively: this never happens in a chain.
- **No complete chain** solves (P). So there is no standard model over any linearly ordered RWK-algebra, including the nonstandard MV-chains of the general semantics of Ł∀.
- **No complete prelinear algebra** solves (P), by the subdirect decomposition into chains. So there is no standard model over any complete IMTL-algebra, in particular any complete MV-algebra. The Ł result is really a theorem about linearity.
- I also built a family of genuinely non-prelinear complete RWK-algebras, the twist products K(L) = {(a,b) : a ∘ b = 0} over a complete distributive integral residuated lattice L, and showed that **K(L) has no solution when L is a chain**.

What is left is precisely the non-prelinear complete RWK-algebras beyond these, which is exactly the room RWK has that Ł lacks. If no such algebra solves (P), then "RWK + naive truth has no standard model" holds in full generality, and the Łukasiewicz negative result becomes a theorem about all of RWK. If some algebra does, the next step is a fixed-point theorem for all sentences simultaneously, replacing Brouwer, over that algebra. Either result would be new as far as I can tell. My attempts to build a solution directly (a countable poset with the interaction pattern forced by the necessary conditions) failed on associativity of fusion; I do not read that as evidence either way.

## Consolidated status

| Question | Status for RWK |
|---|---|
| Naive truth schema (+ T-rules, intersubstitutivity) over PA | **Consistent** (via RWK ⊂ Ł and HPS 2000) |
| Standard model over [0,1], over any complete chain, over any complete prelinear algebra | **No** (HPS for [0,1]; my proofs for the rest) |
| Standard model over some non-prelinear complete RWK-algebra | **Open**; reduces to problem (P) |
| Syntactic ω-consistency of the schema theory | **Open**; schema alone does not prove Restall's C |
| Uniform disquotation / truth commuting with connectives | **Open** (inconsistent over Ł) |
| Truth allowed in induction | **Open** (reportedly inconsistent over Ł) |
| Naive comprehension | **Open** both ways (White's Ł proof flawed; Grišin does not cover distribution) |
| Adding excluded middle | **Trivial** |

## What would settle the open parts

1. Read Bacon (2013) and check whether its strengthened Curry derivation, and its two "individually harmless" subsystems, use anything outside RWK; specifically whether prelinearity or Łukasiewicz's axiom is needed. This decides the ω-inconsistency row.
2. Decide problem (P) for distributive involutive FL_ew-algebras. A negative answer likely goes through some structural fact about elements p with n·p ≤ ¬p in non-prelinear algebras; a positive answer probably needs an algebra not of twist form.
3. For comprehension, try to add naive comprehension to a Dunn–Mints or display calculus for RWK and push Grišin/Cantini-style cut elimination through distribution.

## Caveats

Fetching from the journal and preprint sites was blocked in this session, so the results of Hájek–Paris–Shepherdson, Restall, Bacon, Hájek, Yatabe and Field–Lederman–Øgaard are taken from abstracts and secondary summaries; statements marked as reported in the notes should be checked against the papers. The inclusion RWK ⊂ Ł, the reconstruction of the consistency argument, the analysis of Restall's sentence, and the three "no standard model" propositions and the twist-product construction are my own and are written out in full in the notes.
