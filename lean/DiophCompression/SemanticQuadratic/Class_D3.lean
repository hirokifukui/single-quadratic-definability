import DiophCompression.SemanticQuadratic.FiberDefs
namespace DiophCompression.SemanticQuadratic
open MPUP

/-- Unboundedness from a strictly increasing family inside the set. -/
theorem fiberSet_infinite_of_family (A B C l m q : ℤ) (c₀ : ℕ) (s : ℕ) (hs : 1 ≤ s)
    (ut : ℕ → ℤ) (hfam : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (ut t) = 0) :
    (fiberSet A B C l m q).Infinite := by
  apply Set.infinite_of_not_bddAbove
  intro ⟨M, hM⟩
  have hmem : c₀ + s * (M + 1) ∈ fiberSet A B C l m q := ⟨ut (M + 1), hfam (M + 1)⟩
  have := hM hmem
  nlinarith

theorem dichotomy_degenerate_C_zero (A B C : ℤ) (h : disc A B C = 0) (hC : C = 0) : Dichotomy A B C := by
  subst hC
  have hB : B = 0 := by
    unfold disc at h
    have : B ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  subst hB
  refine ⟨(|A| + 1).toNat, ?_⟩
  have hK : (((|A| + 1).toNat : ℕ) : ℤ) = |A| + 1 := by
    rw [Int.toNat_of_nonneg]; have := abs_nonneg A; omega
  intro l m q
  by_cases hm : m = 0
  · subst hm
    by_cases hA : A = 0
    · subst hA
      by_cases hl : l = 0
      · subst hl
        by_cases hq : q = 0
        · subst hq
          left
          exact fiberSet_infinite_of_family 0 0 0 0 0 0 0 1 le_rfl (fun _ => 0)
            (fun t => by simp [fq])
        · right
          intro c hc
          obtain ⟨u, hu⟩ := hc
          simp [fq] at hu
          exact absurd hu hq
      · right
        intro c hc
        obtain ⟨u, hu⟩ := hc
        simp only [fq] at hu
        have hlc : l * (c : ℤ) = -q := by linarith
        have h1 : |l| * |(c : ℤ)| = |q| := by rw [← abs_mul, hlc, abs_neg]
        have hl1 : 1 ≤ |l| := Int.one_le_abs hl
        have hc0 : |(c : ℤ)| = c := abs_of_nonneg (by exact_mod_cast Nat.zero_le c)
        rw [hc0] at h1
        unfold fbound; rw [hK]; simp only [abs_zero, add_zero, zero_add]
        have := abs_nonneg l; have := abs_nonneg q
        have hcl : (c : ℤ) ≤ |q| := by nlinarith
        nlinarith [sq_nonneg (1 + |l|)]
    · right
      intro c hc
      obtain ⟨u, hu⟩ := hc
      simp only [fq] at hu
      have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
      have hA1 : 1 ≤ |A| := Int.one_le_abs hA
      -- |A| c^2 = |l c + q| ≤ |l| c + |q|
      have h1 : |A| * (c : ℤ) ^ 2 ≤ |l| * c + |q| := by
        have e : A * (c : ℤ) ^ 2 = -(l * c + q) := by linarith
        have : |A| * (c : ℤ) ^ 2 = |l * c + q| := by
          rw [← abs_of_nonneg (sq_nonneg (c : ℤ)), ← abs_mul, e, abs_neg]
        rw [this]
        calc |l * (c : ℤ) + q| ≤ |l * c| + |q| := abs_add_le _ _
          _ = |l| * c + |q| := by rw [abs_mul, abs_of_nonneg hc0]
      have h2 : (c : ℤ) ≤ |l| + |q| := by
        by_contra hcon
        push Not at hcon
        have hpos : (0 : ℤ) < c := by have := abs_nonneg l; have := abs_nonneg q; omega
        nlinarith [abs_nonneg l, abs_nonneg q]
      unfold fbound; rw [hK, abs_zero, add_zero]
      have := abs_nonneg A; have := abs_nonneg l; have := abs_nonneg q
      nlinarith [sq_nonneg (1 + |l|), mul_nonneg (abs_nonneg A) (abs_nonneg l),
        mul_nonneg (abs_nonneg A) (abs_nonneg q), mul_nonneg (abs_nonneg A) (sq_nonneg (1 + |l|))]
  · -- m ≠ 0: infinite if nonempty
    by_cases hne : ∃ c ∈ fiberSet A 0 0 l m q, True
    · left
      obtain ⟨c₀, ⟨u₀, hu₀⟩, -⟩ := hne
      have hs : 1 ≤ (m ^ 2).toNat := by
        have : 1 ≤ m ^ 2 := by nlinarith [Int.one_le_abs hm, sq_abs m, abs_nonneg m]
        omega
      refine fiberSet_infinite_of_family A 0 0 l m q c₀ (m ^ 2).toNat hs
        (fun t => u₀ - (2 * A * c₀ * m * t + A * m ^ 3 * t ^ 2 + l * m * t)) ?_
      intro t
      have hm2 : (((m ^ 2).toNat : ℕ) : ℤ) = m ^ 2 := Int.toNat_of_nonneg (sq_nonneg m)
      push_cast
      rw [hm2]
      simp only [fq] at hu₀ ⊢
      linear_combination hu₀
    · right
      intro c hc
      exact absurd ⟨c, hc, trivial⟩ hne

end DiophCompression.SemanticQuadratic
#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_zero
