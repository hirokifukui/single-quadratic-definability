/-
  RadicalAffine.lean — r11 (GPT r10 必須F): the one-direction reduction of the radical affine
  family. Statements frozen in RadicalAffine_STATEMENTS.lean (md5 24b913ab) before proofs.
  Part 1 (s11, claude.ai direct): theorems 1, 2, 3, 5 and the finite Bezout helper; theorem 4
  (unimodular completion, general s) ships with the RadicalDecomposition machinery.
-/
import DiophCompression.SemanticQuadraticMatrix.AffineGcd
import DiophCompression.SemanticQuadraticSingular.DefsSingularGeneral

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix

/-- Finite Bezout: the gcd of a finite integer family is an integer combination of it. -/
theorem exists_sum_eq_finset_gcd : ∀ {s : ℕ} (lam : Fin s → ℤ),
    ∃ w : Fin s → ℤ, ∑ i, lam i * w i = Finset.univ.gcd lam := by
  intro s
  induction s with
  | zero =>
    intro lam
    exact ⟨fun i => i.elim0, by simp [Finset.univ_eq_empty]⟩
  | succ n ih =>
    intro lam
    obtain ⟨w', hw'⟩ := ih (fun i => lam i.succ)
    obtain ⟨x, y, hxy⟩ :=
      exists_gcd_eq_mul_add_mul (lam 0) (Finset.univ.gcd (fun i : Fin n => lam i.succ))
    have hgcd : Finset.univ.gcd lam
        = gcd (lam 0) (Finset.univ.gcd (fun i : Fin n => lam i.succ)) := by
      rw [Fin.univ_succ, Finset.gcd_cons]
      congr 1
      simp only [Finset.gcd_def, Finset.map_val, Multiset.map_map]
      rfl
    refine ⟨Fin.cons x (fun i => y * w' i), ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hsum : ∑ i : Fin n, lam i.succ * (y * w' i)
        = (∑ i : Fin n, lam i.succ * w' i) * y := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum, hw', hgcd, hxy]

/-- GPT r10 必須F theorem 1 (name verbatim): with a nonzero pair minor the affine gcd is periodic,
positive, and bounded by the minor content. -/
theorem affine_family_nonzero_minor_periodic {s : ℕ} (b m : Fin s → ℤ) (i j : Fin s)
    (h : pairMinor b m i j ≠ 0) (c t : ℤ) :
    affineGcd b m (c + minorContent b m * t) = affineGcd b m c ∧
      0 < affineGcd b m c ∧ affineGcd b m c ≤ |minorContent b m| := by
  have hD : minorContent b m ≠ 0 := by
    intro h0
    exact h (Finset.gcd_eq_zero_iff.mp h0 ⟨i, j⟩ (Finset.mem_univ _))
  exact ⟨affineGcd_periodic b m c t,
    affineGcd_pos_of_pairMinor_ne_zero b m c i j h,
    (affineGcd_periodic_of_minorContent_ne_zero b m hD c t).2⟩

/-- GPT r10 必須F theorem 2 (name verbatim): all pair minors zero ⇒ rank-one affine family. -/
theorem affine_family_zero_minors_proportional {s : ℕ} (b m : Fin s → ℤ)
    (h : ∀ i j, pairMinor b m i j = 0) : RankOneAffineFamily b m :=
  (all_pairMinors_zero_iff_rank_one_affine_family b m).mp h

/-- GPT r10 必須F theorem 3 (name verbatim): a rank-one family has a primitive affine direction. -/
theorem primitive_affine_direction {s : ℕ} (b m : Fin s → ℤ) (h : RankOneAffineFamily b m) :
    ∃ (b₀ m₀ : ℤ) (lam : Fin s → ℤ), Int.gcd b₀ m₀ = 1 ∧
      ∀ i, b i = lam i * b₀ ∧ m i = lam i * m₀ := by
  obtain ⟨b₀, m₀, hcop, lam, hprop⟩ := h
  exact ⟨b₀, m₀, lam, hcop, hprop⟩

/-- GPT r10 必須F theorem 5 (name verbatim): a zero-minor radical family compresses to one coupled
variable, with the bound transfer the assembly needs. -/
theorem radical_family_reduces_to_one_coupled_variable {s : ℕ} (b m : Fin s → ℤ)
    (h : ∀ i j, pairMinor b m i j = 0) :
    ∃ b' μ' : ℤ, |b'| = Finset.univ.gcd b ∧ |μ'| ≤ ∑ i, |m i| ∧
      ∀ (c N : ℤ), (∃ w : Fin s → ℤ, (∑ i, (b i * c + m i) * w i) = N) ↔
        ∃ w' : ℤ, (b' * c + μ') * w' = N := by
  obtain ⟨b₀, m₀, lam, hcop, hprop⟩ :=
    primitive_affine_direction b m (affine_family_zero_minors_proportional b m h)
  have hgnn : (0 : ℤ) ≤ Finset.univ.gcd lam := Finset.Int.finsetGcd_nonneg
  refine ⟨Finset.univ.gcd lam * b₀, Finset.univ.gcd lam * m₀, ?_, ?_, ?_⟩
  · have hb : b = fun i => lam i * b₀ := funext fun i => (hprop i).1
    rw [hb, abs_mul, abs_of_nonneg hgnn, Finset.gcd_mul_right]
    congr 1
    rw [Int.abs_eq_normalize]
  · rcases eq_or_ne (Finset.univ.gcd lam) 0 with h0 | h0
    · rw [h0, zero_mul, abs_zero]
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    · have hex : ∃ i, lam i ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact h0 (Finset.gcd_eq_zero_iff.mpr (fun i _ => hall i))
      obtain ⟨i, hi⟩ := hex
      have hdvd : Finset.univ.gcd lam ∣ lam i := Finset.gcd_dvd (Finset.mem_univ i)
      have hle : Finset.univ.gcd lam ≤ |lam i| :=
        Int.le_of_dvd (abs_pos.mpr hi) ((dvd_abs _ _).mpr hdvd)
      calc |Finset.univ.gcd lam * m₀| = Finset.univ.gcd lam * |m₀| := by
            rw [abs_mul, abs_of_nonneg hgnn]
        _ ≤ |lam i| * |m₀| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
        _ = |lam i * m₀| := (abs_mul _ _).symm
        _ = |m i| := by rw [(hprop i).2]
        _ ≤ ∑ j, |m j| :=
            Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  · intro c N
    have hbc : ∀ i, b i * c + m i = lam i * (b₀ * c + m₀) := fun i => by
      rw [(hprop i).1, (hprop i).2]; ring
    constructor
    · rintro ⟨w, hw⟩
      have hN : N = (b₀ * c + m₀) * ∑ i, lam i * w i := by
        rw [← hw, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [hbc i]; ring)
      have hgd : Finset.univ.gcd lam ∣ ∑ i, lam i * w i :=
        Finset.dvd_sum (fun i _ => Dvd.dvd.mul_right (Finset.gcd_dvd (Finset.mem_univ i)) _)
      obtain ⟨t, ht⟩ := hgd
      refine ⟨t, ?_⟩
      rw [hN, ht]
      ring
    · rintro ⟨w', hw'⟩
      obtain ⟨w₀, hw₀⟩ := exists_sum_eq_finset_gcd lam
      refine ⟨fun i => w₀ i * w', ?_⟩
      calc ∑ i, (b i * c + m i) * (w₀ i * w')
          = ∑ i, (b₀ * c + m₀) * (lam i * w₀ i) * w' :=
            Finset.sum_congr rfl (fun i _ => by rw [hbc i]; ring)
        _ = (b₀ * c + m₀) * (∑ i, lam i * w₀ i) * w' := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = (Finset.univ.gcd lam * b₀ * c + Finset.univ.gcd lam * m₀) * w' := by
            rw [hw₀]; ring
        _ = N := hw'

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.exists_sum_eq_finset_gcd
#print axioms DiophCompression.SemanticQuadraticSingular.affine_family_nonzero_minor_periodic
#print axioms DiophCompression.SemanticQuadraticSingular.affine_family_zero_minors_proportional
#print axioms DiophCompression.SemanticQuadraticSingular.primitive_affine_direction
#print axioms DiophCompression.SemanticQuadraticSingular.radical_family_reduces_to_one_coupled_variable
