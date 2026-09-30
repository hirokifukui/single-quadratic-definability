# NOTATION_CROSSWALK — mpup ↔ Daans–Dittmann–Fehm (arXiv 2102.06941v5)
| mpup / r04 (GPT §3) | DDF | Match? |
|---|---|---|
| witness count r (ν) — unknowns in ℕ or ℤ, one equation P=0 | rk∃⁺_K(D) = min m, finitely many f_i with common zero in K^m (Def 1.3(1)); rk∃_K allows ¬ (Def 1.3(3)) | analogous, but over a field; DDF Remark 3.4: over non-alg-closed fields r=1 equation suffices, matching our single-equation convention |
| degree-bounded witness count (r,d) | none in Def 1.3; DDF rank is degree-free | NO counterpart [V]; this is BDHMS's (ν,δ) |
| graph capacity G_R(r,d) (max n with an injective e: ℕ^n→ℕ whose graph is (r,d)-representable) | essential fibre dimension efd_K(D) (Def 1.3, Cor 6.17: D = f(V(K)) with fibres of dim ≤ d) is about fibre *dimension*, not degree | different object; no counterpart |
| universal arity U_R(r,d) | rk∃,n(K) = sup over D ⊆ K^n of rk∃_K(D) (Def 2.12/2.17): rank in dimension n | closest analogue: DDF ask "how many quantifiers for all D ⊆ K^n"; we ask "for fixed (r,d), how large n" — inverse function, plus degree |
| specialization capacity S(d,q) | none | purely syntactic; no counterpart |
| arity collapse via polynomial injection | Fact 1.7 / §8 (Prop 8.22, Cor 8.24): injective f: ℚ²→ℚ would collapse; ℤ case **[V s5 2026-08-26]**: Lemma 8.19 (ring collapse, degree-free) + Lemma 8.20 (explicit f: ℤ²→ℤ, f(ℤ²) ⊆ ℤ≥0) | the mechanism we show *fails* under a total-degree bound (quantitatively: n ≤ C(d+r+1, r+2)) |
