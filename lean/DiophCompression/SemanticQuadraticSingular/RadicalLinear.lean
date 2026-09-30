/-
  DiophCompression/SemanticQuadraticSingular/RadicalLinear.lean — r10 必須C (GPT r09 §8): the radical variables
  enter linearly, so their existence is a gcd divisibility (Bezout on a finset gcd). Statements frozen in
  `Singular_STATEMENTS.lean` (md5 281708fb). Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.DefsSingular

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

/-- The finset gcd over `Fin (s+1)` splits off the first coordinate. -/
theorem aux_gcd_univ_succ {s : ℕ} (a : Fin (s + 1) → ℤ) :
    Finset.univ.gcd a = (Int.gcd (a 0) (Finset.univ.gcd (Fin.tail a)) : ℤ) := by
  apply Int.dvd_antisymm Finset.Int.finsetGcd_nonneg (by positivity)
  · rw [Int.coe_gcd]
    apply dvd_gcd
    · exact Finset.gcd_dvd (Finset.mem_univ _)
    · exact Finset.dvd_gcd (fun i _ => Finset.gcd_dvd (Finset.mem_univ _))
  · apply Finset.dvd_gcd
    intro i _
    refine Fin.cases ?_ ?_ i
    · exact Int.gcd_dvd_left _ _
    · intro j
      exact dvd_trans (Int.gcd_dvd_right _ _) (Finset.gcd_dvd (Finset.mem_univ j))

theorem exists_dot_eq_iff_gcd_dvd {s : ℕ} (a : Fin s → ℤ) (T : ℤ) :
    (∃ v : Fin s → ℤ, a ⬝ᵥ v = T) ↔ Finset.univ.gcd a ∣ T := by
  induction s generalizing T with
  | zero =>
    constructor
    · rintro ⟨v, rfl⟩
      simp [dotProduct]
    · intro h
      simp only [Finset.univ_eq_empty, Finset.gcd_empty, zero_dvd_iff] at h
      exact ⟨0, by simp [dotProduct, h]⟩
  | succ n ih =>
    constructor
    · rintro ⟨v, rfl⟩
      unfold dotProduct
      exact Finset.dvd_sum (fun i _ => Dvd.dvd.mul_right (Finset.gcd_dvd (Finset.mem_univ i)) _)
    · intro h
      rw [aux_gcd_univ_succ] at h
      obtain ⟨k, hk⟩ := h
      obtain ⟨v', hv'⟩ := (ih (Fin.tail a) (Finset.univ.gcd (Fin.tail a))).mpr dvd_rfl
      have hbez := Int.gcd_eq_gcd_ab (a 0) (Finset.univ.gcd (Fin.tail a))
      refine ⟨Fin.cons (Int.gcdA (a 0) (Finset.univ.gcd (Fin.tail a)) * k)
        (fun j => Int.gcdB (a 0) (Finset.univ.gcd (Fin.tail a)) * k * v' j), ?_⟩
      unfold dotProduct at hv' ⊢
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      have : ∑ i : Fin n, a i.succ * (Int.gcdB (a 0) (Finset.univ.gcd (Fin.tail a)) * k * v' i)
          = Int.gcdB (a 0) (Finset.univ.gcd (Fin.tail a)) * k * ∑ i : Fin n, Fin.tail a i * v' i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.tail]
        ring
      rw [this, hv', hk]
      linear_combination (-k) * hbez

theorem radical_variables_exist_iff_affineGcd_dvd {s : ℕ} (b m : Fin s → ℤ) (c T : ℤ) :
    (∃ v : Fin s → ℤ, T + ∑ i, (b i * c + m i) * v i = 0) ↔ affineGcd b m c ∣ T := by
  have h := exists_dot_eq_iff_gcd_dvd (affineCoeff b m c) (-T)
  unfold affineGcd
  rw [← dvd_neg, ← h]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by unfold dotProduct affineCoeff; linear_combination hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by unfold dotProduct affineCoeff at hv; linear_combination hv⟩

theorem singular_fiberSet_eq_divisibility (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q : ℤ) :
    fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q =
      {c : ℕ | ∃ u v : ℤ, (b * (c : ℤ) + μ) ∣ fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c : ℤ) u v} := by
  ext c
  simp only [fiberSet3S, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, v, w, h⟩
    unfold fq3S at h
    exact ⟨u, v, ⟨-w, by linear_combination h⟩⟩
  · rintro ⟨u, v, k, hk⟩
    exact ⟨u, v, -k, by unfold fq3S; linear_combination hk⟩

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.exists_dot_eq_iff_gcd_dvd
#print axioms DiophCompression.SemanticQuadraticSingular.radical_variables_exist_iff_affineGcd_dvd
#print axioms DiophCompression.SemanticQuadraticSingular.singular_fiberSet_eq_divisibility
