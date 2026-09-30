/-
  Shadow/SingularAssemblyR.lean — ray-carrying shadow of the singular all-r assembly.
  Verbatim transplant of the DATA-level singular assembly in
  DiophCompression/SemanticQuadraticSingular/SingularAssembly.lean, with `StructuredFamily` →
  `StructuredFamilyR` and `DichotomySGData`/`DichotomyMData` → `DichotomySGDataR`/`DichotomyMDataR`.
  The public baseline helpers (fqM_congruence, witnessQuad_drop_of_gram_block, trailIdx,
  nondegenerate_quotient_block, radical_family_reduces_to_one_coupled_variable, …) are imported and
  reused unchanged; the file's `private` helpers are re-declared verbatim with a `ru_` prefix.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.Shadow.DefsSingularGeneralR
import ResearchUpgrade.Shadow.QuotientRankZeroR
import ResearchUpgrade.Shadow.QuotientRankOneR
import ResearchUpgrade.Shadow.MovingModulusGeneralR
import DiophCompression.SemanticQuadraticSingular.SingularAssembly

namespace DiophCompression.ResearchUpgrade

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticGeneral
  DiophCompression.SemanticQuadraticSingular

variable {k : ℕ}

/-! ## Congruence-frame private restatements (re-declared verbatim with `ru_` prefix) -/

private theorem ru_aux_witnessGram_symm' {r : ℕ} (C : Matrix (Fin r) (Fin r) ℤ) :
    (witnessGram C)ᵀ = witnessGram C := by
  unfold witnessGram
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

private theorem ru_witnessGram_conj' {r : ℕ} (C U : Matrix (Fin r) (Fin r) ℤ) :
    witnessGram (Uᵀ * C * U) = Uᵀ * witnessGram C * U := by
  unfold witnessGram
  rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-! ## Index infrastructure (`sum_split2`) -/

private lemma ru_sum_split2 {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (f : Fin k → ℤ) :
    ∑ i : Fin k, f i =
      (∑ a : Fin k₀, f (Fin.castLE hk₀ a)) + ∑ j : Fin (k - k₀), f (trailIdx hk₀ j) := by
  have heq : k₀ + (k - k₀) = k := Nat.add_sub_cancel' hk₀
  let E : Fin k₀ ⊕ Fin (k - k₀) ≃ Fin k := (finSumFinEquiv).trans (finCongr heq)
  have hL : ∀ a : Fin k₀, E (Sum.inl a) = Fin.castLE hk₀ a := by
    intro a; apply Fin.ext; simp [E, finSumFinEquiv]
  have hR : ∀ j : Fin (k-k₀), E (Sum.inr j) = trailIdx hk₀ j := by
    intro j; apply Fin.ext; simp [E, finSumFinEquiv, trailIdx]
  rw [← Fintype.sum_equiv E (fun p => f (E p)) f (fun p => rfl), Fintype.sum_sum_type]
  simp_rw [hL, hR]

/-! ## Witness-quadratic reduction to the leading block (2-cancellation) -/

private lemma ru_wq_reduce {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (C' : Matrix (Fin k) (Fin k) ℤ)
    (hzj : ∀ i j : Fin k, k₀ ≤ (j:ℕ) → witnessGram C' i j = 0)
    (hzi : ∀ i j : Fin k, k₀ ≤ (i:ℕ) → witnessGram C' i j = 0)
    (v : Fin k → ℤ) :
    witnessQuad C' v
      = witnessQuad (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) (fun a => v (Fin.castLE hk₀ a)) := by
  set vz : Fin k → ℤ := fun i => if h : (i:ℕ) < k₀ then v (Fin.castLE hk₀ ⟨i, h⟩) else 0 with hvz
  have hlead : ∀ a : Fin k₀, vz (Fin.castLE hk₀ a) = v (Fin.castLE hk₀ a) := by
    intro a
    have hlt : ((Fin.castLE hk₀ a : Fin k) : ℕ) < k₀ := a.isLt
    simp only [hvz, dif_pos hlt]
    apply congrArg; apply Fin.ext; simp
  have htz : ∀ j : Fin (k-k₀), vz (trailIdx hk₀ j) = 0 := by
    intro j
    have hge : ¬ ((trailIdx hk₀ j : Fin k) : ℕ) < k₀ := by simp
    simp only [hvz, dif_neg hge]
  have hagree : ∀ i : Fin k, (i:ℕ) < k₀ → v i = vz i := by
    intro i hi
    have hvi : vz i = v i := by
      simp only [hvz, dif_pos hi]; apply congrArg; apply Fin.ext; simp
    rw [hvi]
  rw [witnessQuad_drop_of_gram_block C' hzj hzi v vz hagree]
  simp only [witnessQuad, dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [ru_sum_split2 hk₀ (fun i => vz i * ∑ j, C' i j * vz j)]
  have h2 : (∑ j : Fin (k-k₀), vz (trailIdx hk₀ j) * ∑ jj, C' (trailIdx hk₀ j) jj * vz jj) = 0 := by
    apply Finset.sum_eq_zero; intro j _; rw [htz j, zero_mul]
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [hlead a]
  congr 1
  rw [ru_sum_split2 hk₀ (fun j => C' (Fin.castLE hk₀ a) j * vz j)]
  have h3 : (∑ j : Fin (k-k₀), C' (Fin.castLE hk₀ a) (trailIdx hk₀ j) * vz (trailIdx hk₀ j)) = 0 := by
    apply Finset.sum_eq_zero; intro j _; rw [htz j, mul_zero]
  rw [h3, add_zero]
  apply Finset.sum_congr rfl
  intro b _
  rw [hlead b]

/-! ## The block decomposition of the fiber polynomial -/

private lemma ru_fqM_block_decomp {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (A : ℤ) (B' : Fin k → ℤ)
    (C' : Matrix (Fin k) (Fin k) ℤ)
    (hzj : ∀ i j : Fin k, k₀ ≤ (j:ℕ) → witnessGram C' i j = 0)
    (hzi : ∀ i j : Fin k, k₀ ≤ (i:ℕ) → witnessGram C' i j = 0)
    (l : ℤ) (m' : Fin k → ℤ) (q c : ℤ) (v : Fin k → ℤ) :
    fqM A B' C' l m' q c v
      = fqM A (fun a => B' (Fin.castLE hk₀ a))
            (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) l
            (fun a => m' (Fin.castLE hk₀ a)) q c (fun a => v (Fin.castLE hk₀ a))
        + ∑ j : Fin (k - k₀), (B' (trailIdx hk₀ j) * c + m' (trailIdx hk₀ j)) * v (trailIdx hk₀ j) := by
  simp only [fqM]
  rw [ru_wq_reduce hk₀ C' hzj hzi v]
  have hB : B' ⬝ᵥ v = (fun a => B' (Fin.castLE hk₀ a)) ⬝ᵥ (fun a => v (Fin.castLE hk₀ a))
      + ∑ j : Fin (k-k₀), B' (trailIdx hk₀ j) * v (trailIdx hk₀ j) := by
    simp only [dotProduct]
    exact ru_sum_split2 hk₀ (fun i => B' i * v i)
  have hm : m' ⬝ᵥ v = (fun a => m' (Fin.castLE hk₀ a)) ⬝ᵥ (fun a => v (Fin.castLE hk₀ a))
      + ∑ j : Fin (k-k₀), m' (trailIdx hk₀ j) * v (trailIdx hk₀ j) := by
    simp only [dotProduct]
    exact ru_sum_split2 hk₀ (fun i => m' i * v i)
  rw [hB, hm]
  have hSeq : c * (∑ j : Fin (k-k₀), B' (trailIdx hk₀ j) * v (trailIdx hk₀ j))
        + ∑ j : Fin (k-k₀), m' (trailIdx hk₀ j) * v (trailIdx hk₀ j)
      = ∑ j : Fin (k - k₀), (B' (trailIdx hk₀ j) * c + m' (trailIdx hk₀ j)) * v (trailIdx hk₀ j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  linear_combination hSeq

/-! ## Bezout for a finite family and the recombination map -/

private lemma ru_exists_sum_mul_eq_iff_gcd_dvd {s : ℕ} (lam : Fin s → ℤ) (N : ℤ) :
    (∃ w : Fin s → ℤ, ∑ i, lam i * w i = N) ↔ Finset.univ.gcd lam ∣ N := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact Finset.dvd_sum (fun i _ => Dvd.dvd.mul_right (Finset.gcd_dvd (Finset.mem_univ i)) _)
  · rintro ⟨t, ht⟩
    obtain ⟨w₀, hw₀⟩ := exists_sum_eq_finset_gcd lam
    refine ⟨fun i => t * w₀ i, ?_⟩
    calc ∑ i, lam i * (t * w₀ i) = t * ∑ i, lam i * w₀ i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = t * Finset.univ.gcd lam := by rw [hw₀]
      _ = N := by rw [ht]; ring

private def ru_combine {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (v₁ : Fin k₀ → ℤ) (w : Fin (k - k₀) → ℤ) :
    Fin k → ℤ := fun i => if h : (i:ℕ) < k₀ then v₁ ⟨i, h⟩ else w ⟨i - k₀, by omega⟩

private lemma ru_combine_lead {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (v₁ : Fin k₀ → ℤ) (w : Fin (k - k₀) → ℤ)
    (a : Fin k₀) : ru_combine hk₀ v₁ w (Fin.castLE hk₀ a) = v₁ a := by
  have hlt : ((Fin.castLE hk₀ a : Fin k) : ℕ) < k₀ := a.isLt
  simp only [ru_combine, dif_pos hlt]; apply congrArg; apply Fin.ext; simp

private lemma ru_combine_trail {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (v₁ : Fin k₀ → ℤ) (w : Fin (k - k₀) → ℤ)
    (j : Fin (k - k₀)) : ru_combine hk₀ v₁ w (trailIdx hk₀ j) = w j := by
  have hge : ¬ ((trailIdx hk₀ j : Fin k) : ℕ) < k₀ := by simp
  simp only [ru_combine, dif_neg hge]; apply congrArg; apply Fin.ext; simp

/-! ## The membership characterization of the fiber set -/

private lemma ru_fiberSetM_block_iff {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (A : ℤ) (B' : Fin k → ℤ)
    (C' : Matrix (Fin k) (Fin k) ℤ)
    (hzj : ∀ i j : Fin k, k₀ ≤ (j:ℕ) → witnessGram C' i j = 0)
    (hzi : ∀ i j : Fin k, k₀ ≤ (i:ℕ) → witnessGram C' i j = 0)
    (l : ℤ) (m' : Fin k → ℤ) (q : ℤ) (c : ℕ) :
    c ∈ fiberSetM A B' C' l m' q ↔
      ∃ (v₁ : Fin k₀ → ℤ) (w : Fin (k-k₀) → ℤ),
        fqM A (fun a => B' (Fin.castLE hk₀ a)) (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) l
            (fun a => m' (Fin.castLE hk₀ a)) q (c:ℤ) v₁
          + ∑ j, (B' (trailIdx hk₀ j) * (c:ℤ) + m' (trailIdx hk₀ j)) * w j = 0 := by
  simp only [fiberSetM, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun a => v (Fin.castLE hk₀ a), fun j => v (trailIdx hk₀ j), ?_⟩
    rw [← ru_fqM_block_decomp hk₀ A B' C' hzj hzi l m' q (c:ℤ) v]; exact hv
  · rintro ⟨v₁, w, hvw⟩
    refine ⟨ru_combine hk₀ v₁ w, ?_⟩
    rw [ru_fqM_block_decomp hk₀ A B' C' hzj hzi l m' q (c:ℤ) (ru_combine hk₀ v₁ w)]
    have h1 : (fun a => ru_combine hk₀ v₁ w (Fin.castLE hk₀ a)) = v₁ :=
      funext (fun a => ru_combine_lead hk₀ v₁ w a)
    rw [h1]
    simp only [ru_combine_trail]
    exact hvw

/-! ## Sign-flip helpers for DichotomySG -/

private lemma ru_fiberSetSG_neg_b (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    fiberSetSG A B C (-b) l m μ q = fiberSetSG A B C b l m (-μ) q := by
  ext c
  simp only [fiberSetSG, fqSG, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, w, h⟩; exact ⟨u, -w, by linear_combination h⟩
  · rintro ⟨u, w, h⟩; exact ⟨u, -w, by linear_combination h⟩

private lemma ru_fboundSG_neg_mu (K : ℕ) (l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    fboundSG K l m (-μ) q = fboundSG K l m μ q := by
  simp only [fboundSG, abs_neg]

/-! ## The nonzero-minor branch (data form): fiber set periodic, hence a periodic progression or empty -/

private lemma ru_nonzero_minor_periodic_data {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (A : ℤ) (B' : Fin k → ℤ)
    (C' : Matrix (Fin k) (Fin k) ℤ)
    (hzj : ∀ i j : Fin k, k₀ ≤ (j:ℕ) → witnessGram C' i j = 0)
    (hzi : ∀ i j : Fin k, k₀ ≤ (i:ℕ) → witnessGram C' i j = 0)
    (l : ℤ) (m : Fin k → ℤ) (q : ℤ)
    (i0 j0 : Fin (k - k₀))
    (hij : pairMinor (fun j => B' (trailIdx hk₀ j)) (fun j => m (trailIdx hk₀ j)) i0 j0 ≠ 0) :
    Nonempty (DiophCompression.PeriodicProgression (fiberSetM A B' C' l m q))
      ∨ fiberSetM A B' C' l m q = ∅ := by
  set β : Fin (k-k₀) → ℤ := fun j => B' (trailIdx hk₀ j) with hβ
  set γ : Fin (k-k₀) → ℤ := fun j => m (trailIdx hk₀ j) with hγ
  set F : ℤ → (Fin k₀ → ℤ) → ℤ :=
    fqM A (fun a => B' (Fin.castLE hk₀ a)) (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) l
      (fun a => m (Fin.castLE hk₀ a)) q with hF
  have hD : minorContent β γ ≠ 0 := by
    intro h0; exact hij (Finset.gcd_eq_zero_iff.mp h0 ⟨i0, j0⟩ (Finset.mem_univ _))
  have memiff2 : ∀ c : ℕ, c ∈ fiberSetM A B' C' l m q ↔
      ∃ v₁ : Fin k₀ → ℤ, affineGcd β γ (c:ℤ) ∣ F (c:ℤ) v₁ := by
    intro c
    rw [ru_fiberSetM_block_iff hk₀ A B' C' hzj hzi l m q c]
    simp only [← hF]
    have hgcdeq : affineGcd β γ (c:ℤ) = Finset.univ.gcd (fun j => β j * (c:ℤ) + γ j) := rfl
    constructor
    · rintro ⟨v₁, w, hvw⟩
      refine ⟨v₁, ?_⟩
      rw [hgcdeq]
      have hex : ∃ w : Fin (k - k₀) → ℤ, ∑ j, (β j * (c:ℤ) + γ j) * w j = -(F (c:ℤ) v₁) := by
        refine ⟨w, ?_⟩; linear_combination hvw
      have hdiv := (ru_exists_sum_mul_eq_iff_gcd_dvd (fun j => β j * (c:ℤ) + γ j) _).mp hex
      exact (dvd_neg).mp hdiv
    · rintro ⟨v₁, hdvd⟩
      rw [hgcdeq] at hdvd
      have hdiv : Finset.univ.gcd (fun j => β j * (c:ℤ) + γ j) ∣ -(F (c:ℤ) v₁) := dvd_neg.mpr hdvd
      obtain ⟨w, hw⟩ := (ru_exists_sum_mul_eq_iff_gcd_dvd (fun j => β j * (c:ℤ) + γ j) _).mpr hdiv
      refine ⟨v₁, w, ?_⟩
      linear_combination hw
  set Pd : ℕ := (minorContent β γ).natAbs * (minorContent β γ).natAbs with hPddef
  have hPdcast : ((Pd:ℕ):ℤ) = minorContent β γ * minorContent β γ := by
    rw [hPddef]; push_cast [Int.natCast_natAbs]; rw [abs_mul_abs_self]
  have hPd1 : 1 ≤ Pd := by
    rw [hPddef]
    have hne : (minorContent β γ).natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hD
    have h1 : 1 ≤ (minorContent β γ).natAbs := Nat.one_le_iff_ne_zero.mpr hne
    calc 1 = 1 * 1 := by ring
      _ ≤ (minorContent β γ).natAbs * (minorContent β γ).natAbs := Nat.mul_le_mul h1 h1
  have hperiodic : ∀ c : ℕ, c ∈ fiberSetM A B' C' l m q ↔ c + Pd ∈ fiberSetM A B' C' l m q := by
    intro c
    rw [memiff2 c, memiff2 (c + Pd)]
    have hcast : ((c + Pd : ℕ) : ℤ) = (c:ℤ) + minorContent β γ * minorContent β γ := by
      push_cast [hPdcast]; ring
    apply exists_congr; intro v₁
    have hper : affineGcd β γ ((c + Pd : ℕ):ℤ) = affineGcd β γ (c:ℤ) := by
      rw [hcast]; exact affineGcd_periodic β γ (c:ℤ) (minorContent β γ)
    rw [hper]
    have hdvd_diff : affineGcd β γ (c:ℤ) ∣ (F ((c+Pd:ℕ):ℤ) v₁ - F (c:ℤ) v₁) := by
      have hdiff : F ((c+Pd:ℕ):ℤ) v₁ - F (c:ℤ) v₁
          = ((Pd:ℕ):ℤ) * (A * (((c+Pd:ℕ):ℤ) + (c:ℤ))
              + ((fun a => B' (Fin.castLE hk₀ a)) ⬝ᵥ v₁) + l) := by
        simp only [hF, fqM]; push_cast; ring
      rw [hdiff]
      have h1 : affineGcd β γ (c:ℤ) ∣ minorContent β γ := affineGcd_dvd_minorContent β γ (c:ℤ)
      have h2 : minorContent β γ ∣ ((Pd:ℕ):ℤ) := by rw [hPdcast]; exact Dvd.intro _ rfl
      exact Dvd.dvd.mul_right (dvd_trans h1 h2) _
    have hEq : F ((c+Pd:ℕ):ℤ) v₁ = (F ((c+Pd:ℕ):ℤ) v₁ - F (c:ℤ) v₁) + F (c:ℤ) v₁ := by ring
    rw [hEq, Int.dvd_add_right hdvd_diff]
  exact DiophCompression.periodicProgression_or_empty (fiberSetM A B' C' l m q) Pd hPd1 hperiodic

/-! ## The block dichotomy at the data level (ray-carrying) -/

private lemma ru_singular_block_dichotomy_dataR {k k₀ : ℕ} (hk₀ : k₀ ≤ k) (A : ℤ) (B' : Fin k → ℤ)
    (C' : Matrix (Fin k) (Fin k) ℤ)
    (hzj : ∀ i j : Fin k, k₀ ≤ (j:ℕ) → witnessGram C' i j = 0)
    (hzi : ∀ i j : Fin k, k₀ ≤ (i:ℕ) → witnessGram C' i j = 0)
    (hleaf : DichotomySGDataR A (fun a => B' (Fin.castLE hk₀ a))
        (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀))
        (Finset.univ.gcd (fun j => B' (trailIdx hk₀ j)))) :
    DichotomyMDataR A B' C' := by
  obtain ⟨Kleaf, hKleaf⟩ := hleaf
  have hg_nonneg : (0:ℤ) ≤ Finset.univ.gcd (fun j => B' (trailIdx hk₀ j)) :=
    Finset.Int.finsetGcd_nonneg
  have hleafAbs : ∀ (b' : ℤ), |b'| = Finset.univ.gcd (fun j => B' (trailIdx hk₀ j)) →
      ∀ (l : ℤ) (mm : Fin k₀ → ℤ) (μ q : ℤ),
        Nonempty (StructuredFamilyR (fiberSetSG A (fun a => B' (Fin.castLE hk₀ a))
            (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) b' l mm μ q)) ∨
        ∀ c ∈ fiberSetSG A (fun a => B' (Fin.castLE hk₀ a))
            (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) b' l mm μ q,
          (c:ℤ) ≤ fboundSG Kleaf l mm μ q := by
    intro b' hb' l mm μ q
    rcases (abs_eq hg_nonneg).mp hb' with rfl | rfl
    · exact hKleaf l mm μ q
    · rw [ru_fiberSetSG_neg_b]
      rcases hKleaf l mm (-μ) q with h | h
      · left; exact h
      · right; intro c hc; have := h c hc; rwa [ru_fboundSG_neg_mu] at this
  refine ⟨Kleaf, fun l m q => ?_⟩
  by_cases hz0 : ∀ i j, pairMinor (fun j => B' (trailIdx hk₀ j)) (fun j => m (trailIdx hk₀ j)) i j = 0
  · obtain ⟨b', μ', hb'abs, hμ'abs, hFiff⟩ :=
      radical_family_reduces_to_one_coupled_variable
        (fun j => B' (trailIdx hk₀ j)) (fun j => m (trailIdx hk₀ j)) hz0
    have hset : fiberSetM A B' C' l m q =
        fiberSetSG A (fun a => B' (Fin.castLE hk₀ a))
          (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) b' l (fun a => m (Fin.castLE hk₀ a)) μ' q := by
      ext c
      rw [ru_fiberSetM_block_iff hk₀ A B' C' hzj hzi l m q c]
      simp only [fiberSetSG, fqSG, Set.mem_setOf_eq]
      constructor
      · rintro ⟨v₁, w, hvw⟩
        obtain ⟨w', hw'⟩ :=
          (hFiff (c:ℤ) (-(fqM A (fun a => B' (Fin.castLE hk₀ a))
              (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) l
              (fun a => m (Fin.castLE hk₀ a)) q (c:ℤ) v₁))).mp ⟨w, by linear_combination hvw⟩
        exact ⟨v₁, w', by linear_combination hw'⟩
      · rintro ⟨v₁, w', hw'⟩
        obtain ⟨w, hw⟩ :=
          (hFiff (c:ℤ) (-(fqM A (fun a => B' (Fin.castLE hk₀ a))
              (C'.submatrix (Fin.castLE hk₀) (Fin.castLE hk₀)) l
              (fun a => m (Fin.castLE hk₀ a)) q (c:ℤ) v₁))).mpr ⟨w', by linear_combination hw'⟩
        exact ⟨v₁, w, by linear_combination hw⟩
    rw [hset]
    rcases hleafAbs b' hb'abs l (fun a => m (Fin.castLE hk₀ a)) μ' q with hinf | hbnd
    · left; exact hinf
    · right
      intro c hc
      have h1 := hbnd c hc
      have hbound : fboundSG Kleaf l (fun a => m (Fin.castLE hk₀ a)) μ' q
          ≤ (Kleaf : ℤ) * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|) := by
        simp only [fboundSG]
        have hsplit : (∑ a : Fin k₀, |m (Fin.castLE hk₀ a)|)
            + (∑ j : Fin (k-k₀), |m (trailIdx hk₀ j)|) = ∑ i, |m i| :=
          (ru_sum_split2 hk₀ (fun i => |m i|)).symm
        have htail_nn : (0:ℤ) ≤ ∑ j : Fin (k-k₀), |m (trailIdx hk₀ j)| :=
          Finset.sum_nonneg (fun j _ => abs_nonneg _)
        have hlead_nn : (0:ℤ) ≤ ∑ a : Fin k₀, |m (Fin.castLE hk₀ a)| :=
          Finset.sum_nonneg (fun a _ => abs_nonneg _)
        have hbase : (0:ℤ) ≤ 1 + |l| + ∑ a : Fin k₀, |m (Fin.castLE hk₀ a)| + |μ'| := by positivity
        have hle : 1 + |l| + ∑ a : Fin k₀, |m (Fin.castLE hk₀ a)| + |μ'|
            ≤ 1 + |l| + ∑ i, |m i| := by
          rw [← hsplit]; nlinarith [hμ'abs]
        have hKnn : (0:ℤ) ≤ (Kleaf:ℤ) := by positivity
        nlinarith [hle, hbase, abs_nonneg q, hKnn,
          mul_le_mul hle hle hbase (by linarith [hle, hbase] : (0:ℤ) ≤ 1 + |l| + ∑ i, |m i|)]
      exact le_trans h1 hbound
  · push_neg at hz0
    obtain ⟨i0, j0, hij⟩ := hz0
    rcases ru_nonzero_minor_periodic_data hk₀ A B' C' hzj hzi l m q i0 j0 hij with h | h
    · exact Or.inl (h.elim fun F => ⟨StructuredFamilyR.ofPeriodic F⟩)
    · right; intro c hc; rw [h] at hc; simp at hc

/-! ## The leaf dichotomy by quotient rank (ray-carrying) -/

private lemma ru_leaf_dichotomySG_dataR {k₀ : ℕ} (A : ℤ) (B'' : Fin k₀ → ℤ)
    (C'' : Matrix (Fin k₀) (Fin k₀) ℤ) (g : ℤ) (hdet'' : (witnessGram C'').det ≠ 0)
    (hzero : ∀ (A g : ℤ) (B : Fin 0 → ℤ) (C : Matrix (Fin 0) (Fin 0) ℤ), DichotomySGDataR A B C g) :
    DichotomySGDataR A B'' C'' g := by
  rcases Nat.lt_or_ge k₀ 2 with hlt | hge
  · interval_cases k₀
    · exact hzero A g B'' C''
    · apply quotient_rank_one_dichotomy_dataR A B'' C'' g
      intro h00
      apply hdet''
      simp [witnessGram, Matrix.transpose_apply, h00]
  · exact quotient_rank_ge_two_moving_dichotomy_dataR hge A B'' C'' g (by
      simpa [witnessGram] using hdet'')

/-! ### s28 必須F step 3: the unimodular dichotomy transfer (ray-carrying data form) -/

theorem dichotomyMDataR_of_unimodular (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (U : Matrix (Fin k) (Fin k) ℤ) (hU : IsUnit U.det)
    (h : DichotomyMDataR A (Matrix.vecMul B U) (Uᵀ * C * U)) : DichotomyMDataR A B C := by
  obtain ⟨K', hK'⟩ := h
  set T : ℤ := ∑ i, ∑ j, |U i j| with hT
  have hT0 : (0 : ℤ) ≤ T := by positivity
  set NU : ℕ := T.toNat + 1 with hNU
  have hNUZ : (NU : ℤ) = T + 1 := by
    rw [hNU]
    push_cast
    rw [Int.toNat_of_nonneg hT0]
  refine ⟨K' * NU ^ 2, fun l m q => ?_⟩
  have hset : fiberSetM A B C l m q
      = fiberSetM A (Matrix.vecMul B U) (Uᵀ * C * U) l (Matrix.vecMul m U) q := by
    ext c
    simp only [fiberSetM, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨U⁻¹ *ᵥ u, ?_⟩
      rw [← fqM_congruence]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv U hU, Matrix.one_mulVec]
      exact hu
    · rintro ⟨v, hv⟩
      exact ⟨U *ᵥ v, by rw [fqM_congruence]; exact hv⟩
  rcases hK' l (Matrix.vecMul m U) q with hinf | hbnd
  · left
    rw [hset]
    exact hinf
  · right
    intro c hc
    rw [hset] at hc
    have h1 := hbnd c hc
    have hmb : ∑ j, |Matrix.vecMul m U j| ≤ T * ∑ i, |m i| := by
      calc ∑ j, |Matrix.vecMul m U j|
          ≤ ∑ j, ∑ i, |m i| * |U i j| := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            calc |Matrix.vecMul m U j| = |∑ i, m i * U i j| := by
                  simp [Matrix.vecMul, dotProduct]
              _ ≤ ∑ i, |m i * U i j| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ i, |m i| * |U i j| :=
                  Finset.sum_congr rfl (fun i _ => abs_mul _ _)
        _ = ∑ i, |m i| * ∑ j, |U i j| := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
        _ ≤ ∑ i, |m i| * T := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact Finset.single_le_sum (f := fun i => ∑ j, |U i j|)
              (fun i _ => by positivity) (Finset.mem_univ i)
        _ = T * ∑ i, |m i| := by
            rw [← Finset.sum_mul]
            ring
    have hs0 : (0 : ℤ) ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hs1 : 1 + |l| + ∑ j, |Matrix.vecMul m U j|
        ≤ (NU : ℤ) * (1 + |l| + ∑ i, |m i|) := by
      rw [hNUZ]
      nlinarith [hmb, abs_nonneg l, hs0, hT0,
        mul_nonneg hT0 (abs_nonneg l), mul_nonneg hT0 hs0]
    have hs2 : (0 : ℤ) ≤ 1 + |l| + ∑ j, |Matrix.vecMul m U j| := by positivity
    have hsq : (1 + |l| + ∑ j, |Matrix.vecMul m U j|) ^ 2
        ≤ (NU : ℤ) ^ 2 * (1 + |l| + ∑ i, |m i|) ^ 2 := by
      have := mul_self_le_mul_self hs2 hs1
      nlinarith [this]
    have hNU1 : (1 : ℤ) ≤ (NU : ℤ) := by rw [hNUZ]; linarith
    have hfbb : fboundM K' l (Matrix.vecMul m U) q
        ≤ fboundM (K' * NU ^ 2) l m q := by
      simp only [fboundM]
      push_cast
      have habsq : |q| ≤ (NU : ℤ) ^ 2 * |q| := by
        have h2 : (1 : ℤ) ≤ (NU : ℤ) ^ 2 := by nlinarith [hNU1]
        nlinarith [abs_nonneg q, h2, mul_nonneg (abs_nonneg q) (sub_nonneg.mpr h2)]
      nlinarith [hsq, habsq,
        mul_le_mul_of_nonneg_left (add_le_add hsq habsq)
          (show (0 : ℤ) ≤ (K' : ℤ) from by positivity)]
    calc (c : ℤ) ≤ fboundM K' l (Matrix.vecMul m U) q := h1
      _ ≤ fboundM (K' * NU ^ 2) l m q := hfbb

/-! ## Main theorem 1 (ray-carrying data form): the singular projection dichotomy, uniformly in r -/

theorem singular_projection_dichotomy_all_r_dataR (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (hdet : (witnessGram C).det = 0)
    (hzero : ∀ (A g : ℤ) (B : Fin 0 → ℤ) (C : Matrix (Fin 0) (Fin 0) ℤ), DichotomySGDataR A B C g) :
    DichotomyMDataR A B C := by
  match k, B, C, hdet with
  | 0, B, C, _ =>
    exact dichotomyMDataR_of_dichotomySGDataR_zero A B C (hzero A 0 B C)
  | (k+1), B, C, hdet =>
    obtain ⟨k₀, hk₀, U, hU, hzj0, hzi0, hdet₀⟩ :=
      nondegenerate_quotient_block (witnessGram C) (ru_aux_witnessGram_symm' C)
    apply dichotomyMDataR_of_unimodular A B C U hU
    have hGeq : witnessGram (Uᵀ * C * U) = Uᵀ * witnessGram C * U := ru_witnessGram_conj' C U
    have hzj : ∀ i j : Fin (k+1), k₀ ≤ (j:ℕ) → witnessGram (Uᵀ * C * U) i j = 0 := by
      intro i j hj; rw [hGeq]; exact hzj0 i j hj
    have hzi : ∀ i j : Fin (k+1), k₀ ≤ (i:ℕ) → witnessGram (Uᵀ * C * U) i j = 0 := by
      intro i j hi; rw [hGeq]; exact hzi0 i j hi
    have hWsub : witnessGram ((Uᵀ * C * U).submatrix (Fin.castLE hk₀) (Fin.castLE hk₀))
        = (witnessGram (Uᵀ * C * U)).submatrix (Fin.castLE hk₀) (Fin.castLE hk₀) := by
      unfold witnessGram
      rw [Matrix.transpose_submatrix]
      rfl
    have hdet'' : (witnessGram ((Uᵀ * C * U).submatrix (Fin.castLE hk₀) (Fin.castLE hk₀))).det ≠ 0 := by
      rw [hWsub, hGeq]; exact hdet₀
    exact ru_singular_block_dichotomy_dataR hk₀ A (Matrix.vecMul B U) (Uᵀ * C * U) hzj hzi
      (ru_leaf_dichotomySG_dataR A (fun a => (Matrix.vecMul B U) (Fin.castLE hk₀ a))
        ((Uᵀ * C * U).submatrix (Fin.castLE hk₀) (Fin.castLE hk₀))
        (Finset.univ.gcd (fun j => (Matrix.vecMul B U) (trailIdx hk₀ j))) hdet'' hzero)

/-- 必須F step 3, MILESTONE (ray-carrying): the singular block is UNCONDITIONAL in ray-carrying
    data form. -/
theorem singular_projection_dichotomy_all_r_dataR_full {k : ℕ} (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (hdet : (witnessGram C).det = 0) :
    DichotomyMDataR A B C :=
  singular_projection_dichotomy_all_r_dataR A B C hdet
    (fun A g B C => quotient_rank_zero_dichotomy_dataR A g B C)

end DiophCompression.ResearchUpgrade
