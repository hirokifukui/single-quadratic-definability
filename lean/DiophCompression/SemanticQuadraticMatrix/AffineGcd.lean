/-
  DiophCompression/SemanticQuadraticMatrix/AffineGcd.lean — r09 必須G (GPT r08 §6): arithmetic of the radical
  coefficients aᵢ(c) = bᵢc + mᵢ of a singular witness block. Central identity gcdᵢ(bᵢc + mᵢ) ∣ bᵢmⱼ − bⱼmᵢ;
  consequences: g(c) ∣ minorContent, g(c) ≥ 1 whenever some pair minor is non-zero, g is minorContent-periodic,
  all pair minors vanish ⟺ one primitive direction, and then g(c) = gcd(λ)·|b₀c + m₀| (one coupled radical).
  Statements frozen first in the frozen statement file `AffineGcd_STATEMENTS.lean` (md5 2f22b481).
  Session 9, 2026-08-27, claude.ai direct.
-/
import Mathlib

namespace DiophCompression.SemanticQuadraticMatrix

/-- The affine radical coefficient aᵢ(c) = bᵢ c + mᵢ. -/
def affineCoeff {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) (i : Fin s) : ℤ := b i * c + m i

/-- g(c) = gcdᵢ (bᵢ c + mᵢ) (normalised, hence ≥ 0; g(c) = 0 iff every aᵢ(c) = 0). -/
def affineGcd {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) : ℤ := Finset.univ.gcd (affineCoeff b m c)

/-- The pair minor bᵢ mⱼ − bⱼ mᵢ of the affine family. -/
def pairMinor {s : ℕ} (b m : Fin s → ℤ) (i j : Fin s) : ℤ := b i * m j - b j * m i

/-- The content of the pair minors: gcd over all (i, j) (0 iff every pair minor vanishes). -/
def minorContent {s : ℕ} (b m : Fin s → ℤ) : ℤ :=
  Finset.univ.gcd (fun p : Fin s × Fin s => pairMinor b m p.1 p.2)

/-- (b, m) is a rank-one affine family: every (bᵢ, mᵢ) is an integer multiple of one primitive (b₀, m₀). -/
def RankOneAffineFamily {s : ℕ} (b m : Fin s → ℤ) : Prop :=
  ∃ b₀ m₀ : ℤ, Int.gcd b₀ m₀ = 1 ∧ ∃ lam : Fin s → ℤ, ∀ i, b i = lam i * b₀ ∧ m i = lam i * m₀

theorem affineGcd_nonneg {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) : 0 ≤ affineGcd b m c :=
  Finset.Int.finsetGcd_nonneg

theorem affineGcd_dvd_affineCoeff {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) (i : Fin s) :
    affineGcd b m c ∣ b i * c + m i :=
  Finset.gcd_dvd (Finset.mem_univ i)

theorem affineGcd_eq_zero_iff {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) :
    affineGcd b m c = 0 ↔ ∀ i, b i * c + m i = 0 := by
  unfold affineGcd
  rw [Finset.gcd_eq_zero_iff]
  simp [affineCoeff]

theorem pairMinor_eq_combination {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) (i j : Fin s) :
    pairMinor b m i j = b i * (b j * c + m j) - b j * (b i * c + m i) := by
  unfold pairMinor; ring

/-- Central identity: g(c) ∣ bᵢ mⱼ − bⱼ mᵢ. -/
theorem affineGcd_dvd_pairMinor {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) (i j : Fin s) :
    affineGcd b m c ∣ pairMinor b m i j := by
  rw [pairMinor_eq_combination b m c i j]
  exact dvd_sub ((affineGcd_dvd_affineCoeff b m c j).mul_left _)
    ((affineGcd_dvd_affineCoeff b m c i).mul_left _)

theorem affineGcd_dvd_minorContent {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) :
    affineGcd b m c ∣ minorContent b m :=
  Finset.dvd_gcd (fun p _ => affineGcd_dvd_pairMinor b m c p.1 p.2)

/-- If some pair minor is non-zero, no c annihilates all coefficients: g(c) ≥ 1 for every c. -/
theorem affineGcd_pos_of_pairMinor_ne_zero {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) (i j : Fin s)
    (h : pairMinor b m i j ≠ 0) : 0 < affineGcd b m c := by
  rcases (affineGcd_nonneg b m c).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply h
    have h0 := (affineGcd_eq_zero_iff b m c).mp heq.symm
    rw [pairMinor_eq_combination b m c i j, h0 i, h0 j]
    ring

/-- g is periodic with period minorContent (unconditionally; trivial when the content is 0). -/
theorem affineGcd_periodic {s : ℕ} (b m : Fin s → ℤ) (c t : ℤ) :
    affineGcd b m (c + minorContent b m * t) = affineGcd b m c := by
  apply Int.dvd_antisymm (affineGcd_nonneg _ _ _) (affineGcd_nonneg _ _ _)
  · unfold affineGcd
    apply Finset.dvd_gcd
    intro i _
    have h1 := affineGcd_dvd_affineCoeff b m (c + minorContent b m * t) i
    have h2 := affineGcd_dvd_minorContent b m (c + minorContent b m * t)
    have e : affineCoeff b m c i
        = (b i * (c + minorContent b m * t) + m i) - minorContent b m * (b i * t) := by
      unfold affineCoeff; ring
    rw [e]
    exact dvd_sub h1 (h2.mul_right _)
  · unfold affineGcd
    apply Finset.dvd_gcd
    intro i _
    have h1 := affineGcd_dvd_affineCoeff b m c i
    have h2 := affineGcd_dvd_minorContent b m c
    have e : affineCoeff b m (c + minorContent b m * t) i
        = (b i * c + m i) + minorContent b m * (b i * t) := by
      unfold affineCoeff; ring
    rw [e]
    exact dvd_add h1 (h2.mul_right _)

/-- With a non-zero content D: g is D-periodic and takes values among the divisors of D, so g ≤ |D|. -/
theorem affineGcd_periodic_of_minorContent_ne_zero {s : ℕ} (b m : Fin s → ℤ)
    (hD : minorContent b m ≠ 0) (c t : ℤ) :
    affineGcd b m (c + minorContent b m * t) = affineGcd b m c ∧
      affineGcd b m c ≤ |minorContent b m| :=
  ⟨affineGcd_periodic b m c t,
    Int.le_of_dvd (abs_pos.mpr hD) ((dvd_abs _ _).mpr (affineGcd_dvd_minorContent b m c))⟩

/-- All pair minors vanish iff (b, m) is a rank-one affine family (one primitive direction). -/
theorem all_pairMinors_zero_iff_rank_one_affine_family {s : ℕ} (b m : Fin s → ℤ) :
    (∀ i j, pairMinor b m i j = 0) ↔ RankOneAffineFamily b m := by
  constructor
  · intro h
    by_cases hz : ∀ i, b i = 0 ∧ m i = 0
    · exact ⟨1, 0, by norm_num, fun _ => 0, fun i => by simp [(hz i).1, (hz i).2]⟩
    · push_neg at hz
      obtain ⟨i₀, hi₀⟩ := hz
      have hne : ¬ (b i₀ = 0 ∧ m i₀ = 0) := fun ⟨h1, h2⟩ => hi₀ h1 h2
      have hpos : 0 < Int.gcd (b i₀) (m i₀) :=
        Nat.pos_of_ne_zero (fun h0 => hne (Int.gcd_eq_zero_iff.mp h0))
      obtain ⟨g, hg⟩ : ∃ g : ℤ, g = ((Int.gcd (b i₀) (m i₀) : ℕ) : ℤ) := ⟨_, rfl⟩
      have hgpos : 0 < g := by rw [hg]; exact_mod_cast hpos
      have hgb : g ∣ b i₀ := by rw [hg]; exact Int.gcd_dvd_left _ _
      have hgm : g ∣ m i₀ := by rw [hg]; exact Int.gcd_dvd_right _ _
      obtain ⟨b₀, hb₀⟩ := hgb
      obtain ⟨m₀, hm₀⟩ := hgm
      have hcop : Int.gcd b₀ m₀ = 1 := by
        have := Int.gcd_div_gcd_div_gcd hpos
        rw [← hg] at this
        rw [hb₀, hm₀, Int.mul_ediv_cancel_left _ hgpos.ne', Int.mul_ediv_cancel_left _ hgpos.ne'] at this
        exact this
      have hprop : ∀ i, b i * m₀ = b₀ * m i := by
        intro i
        have := h i i₀
        unfold pairMinor at this
        rw [hb₀, hm₀] at this
        have h2 : g * (b i * m₀ - b₀ * m i) = 0 := by linear_combination this
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 hgpos.ne'
        · linarith
      by_cases hb0 : b₀ = 0
      · have hm1 : m₀ * m₀ = 1 := by
          rw [hb0, Int.gcd_zero_left] at hcop
          rcases Int.natAbs_eq_iff.mp hcop with h | h <;> rw [h] <;> norm_num
        have hm0 : m₀ ≠ 0 := by rintro rfl; simp at hm1
        refine ⟨b₀, m₀, hcop, fun i => m i * m₀, fun i => ⟨?_, ?_⟩⟩
        · have h1 := hprop i
          rw [hb0, zero_mul] at h1
          rcases mul_eq_zero.mp h1 with h2 | h2
          · rw [h2, hb0]; ring
          · exact absurd h2 hm0
        · linear_combination (-(m i)) * hm1
      · have hcop' : IsCoprime b₀ m₀ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
        refine ⟨b₀, m₀, hcop, fun i => b i / b₀, fun i => ?_⟩
        have hdvd : b₀ ∣ b i := hcop'.dvd_of_dvd_mul_right ⟨m i, hprop i⟩
        obtain ⟨lam, hlam⟩ := hdvd
        have hdiv : b i / b₀ = lam := by rw [hlam, Int.mul_ediv_cancel_left _ hb0]
        refine ⟨?_, ?_⟩
        · show b i = b i / b₀ * b₀
          rw [hdiv, hlam]; ring
        show m i = b i / b₀ * m₀
        rw [hdiv]
        have h1 := hprop i
        rw [hlam] at h1
        have h2 : b₀ * (m i - lam * m₀) = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 hb0
        · linarith
  · rintro ⟨b₀, m₀, -, lam, hl⟩ i j
    unfold pairMinor
    rw [(hl i).1, (hl i).2, (hl j).1, (hl j).2]
    ring

/-- Rank-one reduction: for bᵢ = λᵢ b₀, mᵢ = λᵢ m₀ one has g(c) = gcd(λ) · |b₀ c + m₀|. -/
theorem affineGcd_of_rank_one_family {s : ℕ} (lam : Fin s → ℤ) (b₀ m₀ c : ℤ) :
    affineGcd (fun i => lam i * b₀) (fun i => lam i * m₀) c = Finset.univ.gcd lam * |b₀ * c + m₀| := by
  unfold affineGcd
  have e : affineCoeff (fun i => lam i * b₀) (fun i => lam i * m₀) c = fun i => lam i * (b₀ * c + m₀) := by
    funext i; unfold affineCoeff; ring
  rw [e, Finset.gcd_mul_right, ← Int.abs_eq_normalize]

end DiophCompression.SemanticQuadraticMatrix

#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_nonneg
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_dvd_affineCoeff
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_eq_zero_iff
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_dvd_pairMinor
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_dvd_minorContent
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_pos_of_pairMinor_ne_zero
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_periodic
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_periodic_of_minorContent_ne_zero
#print axioms DiophCompression.SemanticQuadraticMatrix.all_pairMinors_zero_iff_rank_one_affine_family
#print axioms DiophCompression.SemanticQuadraticMatrix.affineGcd_of_rank_one_family
