/-
  MPUP/Quantitative.lean — session 2 (2026-08-26), written by claude.ai directly (not CC).
  Quantitative form of the counting obstruction (GPT r01 request 7 / OBSTRUCTION_THEOREM.md C3):
  any multiparameter universal pair (ν(n), δ(n)) — arbitrary maps, not just constants — obeys
      n ≤ δ(n+1) · monoCount (δ(n+1)) (ν(n+1)+1)        for every n,
  by applying universality at n+1 parameters to the graph of the injective `code : ℕ^n → ℕ`.
  Frozen files (Spec/Gate/Task1/Obstruction) are NOT modified; this file only imports them.
-/
import MPUP.Obstruction

namespace MPUP

/-- Quantitative obstruction, ℕ-unknowns. -/
theorem multiUniversalN_bound {ν δ : ℕ → ℕ} (h : MultiUniversalN ν δ) (n : ℕ) :
    n ≤ δ (n + 1) * monoCount (δ (n + 1)) (ν (n + 1) + 1) := by
  obtain ⟨r', hr', C, hCd, hC⟩ := h (n + 1) _ (diophN_graph_code n)
  have h1 := coder_counting_bound _ C code (code_injective n)
    ((representsN_iff_representsIn C _).1 hC)
  have h2 : C.totalDegree * monoCount C.totalDegree (r' + 1)
      ≤ δ (n + 1) * monoCount (δ (n + 1)) (ν (n + 1) + 1) :=
    Nat.mul_le_mul hCd (monoCount_mono hCd (by omega))
  omega

/-- Quantitative obstruction, ℤ-unknowns (hypothesis still Diophantine over ℕ, as in the AFP). -/
theorem multiUniversalZ_bound {ν δ : ℕ → ℕ} (h : MultiUniversalZ ν δ) (n : ℕ) :
    n ≤ δ (n + 1) * monoCount (δ (n + 1)) (ν (n + 1) + 1) := by
  obtain ⟨r', hr', C, hCd, hC⟩ := h (n + 1) _ (diophN_graph_code n)
  have h1 := coder_counting_bound _ C code (code_injective n)
    ((representsZ_iff_representsIn C _).1 hC)
  have h2 : C.totalDegree * monoCount C.totalDegree (r' + 1)
      ≤ δ (n + 1) * monoCount (δ (n + 1)) (ν (n + 1) + 1) :=
    Nat.mul_le_mul hCd (monoCount_mono hCd (by omega))
  omega

/-- Sanity: the constant case recovers `not_MPUP_N` from the quantitative bound alone. -/
theorem not_MPUP_N_of_bound : ¬ MPUP_N := by
  rintro ⟨ν, δ, h⟩
  have := multiUniversalN_bound h (δ * monoCount δ (ν + 1) + 1)
  omega

theorem not_MPUP_Z_of_bound : ¬ MPUP_Z := by
  rintro ⟨ν, δ, h⟩
  have := multiUniversalZ_bound h (δ * monoCount δ (ν + 1) + 1)
  omega

/-- Sanity (GPT r01 request 2, "degree 1"): with total degree ≤ 1 the universal pair handles at most
    `monoCount 1 (ν+1) = ν + 2` parameters beyond the first, whatever ν is. -/
theorem multiUniversalN_degree_one {ν : ℕ → ℕ} (h : MultiUniversalN ν (fun _ => 1)) (n : ℕ) :
    n ≤ monoCount 1 (ν (n + 1) + 1) := by
  have := multiUniversalN_bound h n
  simpa using this

/-- Boundary instances (GPT r01 request 2): the obstruction is unconditional in r and d,
    including r = 0 and d = 0. -/
example : ¬ TupleCoderN 0 0 := not_tupleCoderN 0 0
example : ¬ TupleCoderZ 0 0 := not_tupleCoderZ 0 0
example (d : ℕ) : ¬ TupleCoderN 0 d := not_tupleCoderN 0 d
example (r : ℕ) : ¬ TupleCoderN r 0 := not_tupleCoderN r 0

end MPUP

#print axioms MPUP.multiUniversalN_bound
#print axioms MPUP.multiUniversalZ_bound
#print axioms MPUP.not_MPUP_N_of_bound
#print axioms MPUP.not_MPUP_Z_of_bound
#print axioms MPUP.multiUniversalN_degree_one
