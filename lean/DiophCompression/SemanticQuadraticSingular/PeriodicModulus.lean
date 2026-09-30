/-
  DiophCompression/SemanticQuadraticSingular/PeriodicModulus.lean — r10 必須D + 必須G (GPT r09 §4.1, §8):
  the periodic divisibility master lemma (g T-periodic, g(c) ∣ T, P polynomial in c ⇒ {c | ∃u, g(c) ∣ P(c,u)}
  is T-periodic, hence infinite or empty) and the fixed-modulus leaf (b = 0): every witness block satisfies
  the dichotomy with a fixed radical modulus — no Hensel, no prime powers. Statements frozen in
  `Singular_STATEMENTS.lean` (md5 281708fb). Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.RadicalLinear

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

theorem polynomial_eval_add_period_mod (P : Polynomial ℤ) (c T : ℤ) :
    T ∣ P.eval (c + T) - P.eval c := by
  have h := Polynomial.sub_dvd_eval_sub (c + T) c P
  rwa [add_sub_cancel_left] at h

/-- Membership in {c | ∃ u, g(c) ∣ P(c,u)} is T-periodic when g is T-periodic, g(c) ∣ T and
    P(·,u) is an integer polynomial in c (any shift moves the value by a multiple of the shift). -/
theorem periodic_divisibility_set {ι : Type*} (g : ℤ → ℤ) (P : ℤ → ι → ℤ) (T : ℕ)
    (hg : ∀ c, g (c + T) = g c) (hgT : ∀ c, g c ∣ (T : ℤ))
    (hP : ∀ c u (t : ℤ), t ∣ P (c + t) u - P c u) (c : ℕ) :
    (∃ u, g c ∣ P c u) ↔ ∃ u, g ((c + T : ℕ) : ℤ) ∣ P ((c + T : ℕ) : ℤ) u := by
  push_cast
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hg]
    have h1 : g c ∣ P ((c : ℤ) + T) u - P c u := dvd_trans (hgT c) (hP c u T)
    have := dvd_add h1 hu
    simpa using this
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hg] at hu
    have h1 : g c ∣ P ((c : ℤ) + T) u - P c u := dvd_trans (hgT c) (hP c u T)
    have := dvd_sub hu h1
    simpa using this

theorem periodic_fiber_infinite_or_empty {ι : Type*} (g : ℤ → ℤ) (P : ℤ → ι → ℤ) (T : ℕ) (hT : 1 ≤ T)
    (hg : ∀ c, g (c + T) = g c) (hgT : ∀ c, g c ∣ (T : ℤ))
    (hP : ∀ c u (t : ℤ), t ∣ P (c + t) u - P c u) :
    ({c : ℕ | ∃ u, g c ∣ P c u} : Set ℕ).Infinite ∨ ({c : ℕ | ∃ u, g c ∣ P c u} : Set ℕ) = ∅ := by
  apply periodic_infinite_or_empty _ T hT
  intro c
  simp only [Set.mem_setOf_eq]
  exact periodic_divisibility_set g P T hg hgT hP c

theorem affineGcd_nonzeroMinor_fiber_periodic {s : ℕ} {ι : Type*} (b m : Fin s → ℤ)
    (hD : minorContent b m ≠ 0) (P : ℤ → ι → ℤ) (hP : ∀ c u (t : ℤ), t ∣ P (c + t) u - P c u) :
    ({c : ℕ | ∃ u, affineGcd b m c ∣ P c u} : Set ℕ).Infinite ∨
      ({c : ℕ | ∃ u, affineGcd b m c ∣ P c u} : Set ℕ) = ∅ := by
  refine periodic_fiber_infinite_or_empty (affineGcd b m) P (minorContent b m).natAbs
    (Int.natAbs_pos.mpr hD) ?_ ?_ hP
  · intro c
    have h := affineGcd_periodic b m c (Int.sign (minorContent b m))
    rw [Int.mul_sign_self] at h
    simpa [Int.natCast_natAbs] using h
  · intro c
    rw [Int.natCast_natAbs]
    exact dvd_trans (affineGcd_dvd_minorContent b m c) (self_dvd_abs _)

theorem fixed_radical_modulus_fiber_periodic (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ μ q : ℤ) (hμ : μ ≠ 0) :
    (fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 l m₁ m₂ μ q).Infinite ∨
      fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 l m₁ m₂ μ q = ∅ := by
  have hset : fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 l m₁ m₂ μ q =
      {c : ℕ | ∃ uv : ℤ × ℤ, (fun c : ℤ => 0 * c + μ) c ∣
        (fun (c : ℤ) (uv : ℤ × ℤ) => fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c uv.1 uv.2) c uv} := by
    rw [singular_fiberSet_eq_divisibility]
    ext c
    simp only [Set.mem_setOf_eq, Prod.exists]
  rw [hset]
  refine periodic_fiber_infinite_or_empty (g := fun c : ℤ => 0 * c + μ)
    (P := fun (c : ℤ) (uv : ℤ × ℤ) => fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c uv.1 uv.2)
    μ.natAbs (Int.natAbs_pos.mpr hμ) ?_ ?_ ?_
  · intro c; simp
  · intro c
    simp only [zero_mul, zero_add, Int.natCast_natAbs]
    exact self_dvd_abs μ
  · intro c uv t
    exact ⟨A * (2 * c + t) + B₁ * uv.1 + B₂ * uv.2 + l, by unfold fq2; ring⟩

theorem fiberSet3S_b_zero_μ_zero (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q : ℤ) :
    fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 l m₁ m₂ 0 q = fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q := by
  ext c
  simp only [fiberSet3S, fiberSet2, Set.mem_setOf_eq, fq3S, zero_mul, add_zero]
  exact ⟨fun ⟨u, v, _, h⟩ => ⟨u, v, h⟩, fun ⟨u, v, h⟩ => ⟨u, v, 0, h⟩⟩

theorem fixed_modulus_dichotomy (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 := by
  obtain ⟨K, hK⟩ := dichotomy2_all A B₁ B₂ C₁₁ C₁₂ C₂₂
  refine ⟨K, fun l m₁ m₂ μ q => ?_⟩
  by_cases hμ : μ = 0
  · subst hμ
    rw [fiberSet3S_b_zero_μ_zero]
    rcases hK l m₁ m₂ q with hInf | hBd
    · exact Or.inl hInf
    · right
      intro c hc
      have := hBd c hc
      unfold fbound2 at this
      unfold fbound3S
      simpa using this
  · rcases fixed_radical_modulus_fiber_periodic A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ μ q hμ with hInf | hEmp
    · exact Or.inl hInf
    · right
      intro c hc
      rw [hEmp] at hc
      exact absurd hc (Set.notMem_empty c)

theorem rank_two_fixed_modulus_periodic (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ μ q : ℤ)
    (hN : discW C₁₁ C₁₂ C₂₂ ≠ 0) (hμ : μ ≠ 0) :
    (fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 l m₁ m₂ μ q).Infinite ∨
      fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 l m₁ m₂ μ q = ∅ :=
  fixed_radical_modulus_fiber_periodic A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ μ q hμ

theorem rank_two_fixed_modulus_dichotomy (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hN : discW C₁₁ C₁₂ C₂₂ ≠ 0) :
    DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ 0 :=
  fixed_modulus_dichotomy A B₁ B₂ C₁₁ C₁₂ C₂₂

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.polynomial_eval_add_period_mod
#print axioms DiophCompression.SemanticQuadraticSingular.periodic_divisibility_set
#print axioms DiophCompression.SemanticQuadraticSingular.periodic_fiber_infinite_or_empty
#print axioms DiophCompression.SemanticQuadraticSingular.affineGcd_nonzeroMinor_fiber_periodic
#print axioms DiophCompression.SemanticQuadraticSingular.fixed_radical_modulus_fiber_periodic
#print axioms DiophCompression.SemanticQuadraticSingular.fiberSet3S_b_zero_μ_zero
#print axioms DiophCompression.SemanticQuadraticSingular.fixed_modulus_dichotomy
#print axioms DiophCompression.SemanticQuadraticSingular.rank_two_fixed_modulus_periodic
#print axioms DiophCompression.SemanticQuadraticSingular.rank_two_fixed_modulus_dichotomy
