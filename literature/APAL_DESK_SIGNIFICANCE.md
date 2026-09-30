# APAL_DESK_SIGNIFICANCE — why a substantial number of logicians should care (Gate 3 deliverable 2, r17, 2026-08-30)

The desk question is not "is it correct" (the kernel answers that) but "is it logic, and is it significant". The answer has to be made in the introduction, in the language of definability, without the repository vocabulary. This note fixes the argument the introduction must carry; it is the author's own case, to be tested by the desk-editor simulation (referee_simulation/APAL_DESK_EDITOR.md).

## 1. The object is a definability invariant, not an equation
The paper studies existential definitions Φ(a) ≡ ∃u ∈ ℤʳ P(a,u) = 0 over ℕ-inputs under a syntactic budget (r witnesses, total degree d) and asks how much *input arity* such a definition can carry under three semantic demands: injective coefficient specialization (S), representation of an injective function's graph (G), and representation of every Diophantine set (U). These are resource-bounded versions of the classical questions behind DPRM (how many unknowns, what degree) and of the existential-rank program of Daans–Dittmann–Fehm; the difference is that the degree is fixed and the equation is the fixed object, so the invariants see the phase where decidability still holds.

## 2. The three exact values and the two implications are theorems in the language of logic
- Sandwich, kernel-checked (Sandwich.lean, CapacityBireduction.lean): UniversalAchievable(n+1, r, d) ⇒ GraphAchievable(n, r, d) ⇒ SpecializationAchievable(n, r+1, d); hence U(r,d) ≤ G(r,d)+1 ≤ S(d, r+1)+1 for d ≥ 1, with the arity shift stated. (The manuscript must display these; a referee simulation asked for exactly them, and they already exist.)
- Exact values at d = 2, for every r: S(2, r+1) = r+3, G_ℤ(r,2) = 2, U_ℤ(r,2) = U_ℕ(r,2) = 0 (the last relative to GS + DPRM).
- Witness inertia: G_ℤ(r,2) = G_ℤ(0,2). At the last degree where single-equation solvability is decidable, existential quantifiers over ℤ do not raise the arity a graph definition can carry. This is a statement about the expressive power of ∃-quantification under a degree bound — the kind of statement definability theory is about — and it is sharp in both directions.

## 3. What the arithmetic supplies to the logic
The uniform projection dichotomy (Theorem A): for a fixed quadratic part, every affine perturbation has output projection infinite or bounded by K·((1+|ℓ|₁)²+|q|) with K independent of the perturbation. Logically this is a *uniform elimination bound*: the existential quantifier ∃u over a quadratic can be replaced, for graph-type definitions, by a bounded search whose bound is polynomial in the input, uniformly in the definition's affine data. The definability consequence (arity ≤ 2) follows by counting. This is the part that is new and that no per-instance decision procedure (Grunewald–Segal) gives.

## 4. Connection to open questions logicians already own
BDHMS 2025 §6.2 asked whether multiparameter universal pairs exist; the answer here is no, with a quantitative reason (the S/G/U spectrum). The result therefore lands in a live conversation (universal pairs, AFP formalization) rather than in isolation.

## 5. Honest boundaries the introduction must state (so the desk does not discover them)
- "Parameter" means free input variable, not a model-theoretic parameter (referee simulation 1, item 1.1). The introduction defines the term in its first paragraph.
- Degree two is the highest degree at which single-equation solvability is known decidable, not a proven boundary (cubic open).
- U = 0 is a corollary of GS + DPRM; its depth is not comparable to Theorem A.
- S is a coefficient-specialization invariant; it is the syntactic ceiling, not a definability notion in itself.
- The inertia statement is about achievable arities, not elimination of witnesses from a given representation.

## 6. Desk-reject risk, self-assessed before the simulation
Main risk: the paper is read as "a long study of one quadratic equation". Mitigation: title on definitions, first paragraph on existential definitions and resource budgets, sandwich displayed early, Theorem A stated as a uniform elimination bound, §4 clearly marked as the arithmetic engine, formalization compressed. Residual risk after mitigation: moderate; the desk-editor simulation gives an independent number.
