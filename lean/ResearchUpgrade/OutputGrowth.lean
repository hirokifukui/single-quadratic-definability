/-
  OutputGrowth.lean — s48.  Gate22 task **G22-T08** — output-only linear growth.

  This is the join that closes the positive-semidefinite branch WITHOUT any coercivity.  The
  chain, each link already proved elsewhere in this session:

    * the centre is affine in the input        (G22-T06 §3.1, AffineCentre.lean)
    * every integer solution sits at squared distance exactly `R(a)` from it  (G21-T07)
    * each output coordinate is `polar(wⱼ, ·)`  (G22-T06 §3.2)
    * `polar(v,w)² ≤ 4 Q(v) Q(w)` for `0 ≤ Q`   (G22-T07)

  so `|πⱼ(z − h(a))|² ≤ 4 Q(wⱼ) R(a)` and it remains to bound `R(a)` by `C₀(1 + ‖a‖∞)²`.  That
  bound is arithmetic on explicit coefficient sums: no square roots are introduced (the integer
  constant is chosen by `K = 4WC₀ + 1`, which satisfies `K² ≥ K ≥ 4WC₀` because `K ≥ 1`), and no
  bound on the WITNESSES is used or available — `P = (b−a)²` has a free witness and is inside the
  scope of this theorem, which is exactly what E-21-2 said `LatticeCoercive` could not manage.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import ResearchUpgrade.AffineCentre
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.LinearGrowthDimension
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

/-! ### The growth argument `N a = 1 + ‖a‖∞`, read in ℚ -/

/-- `1 + ‖a‖∞`, as a rational.  Every bound below is stated against this. -/
def growthArg {n : ℕ} (a : Fin n → ℤ) : ℚ := 1 + (supNorm a : ℚ)

theorem one_le_growthArg {n : ℕ} (a : Fin n → ℤ) : 1 ≤ growthArg a := by
  simp only [growthArg]
  have : (0 : ℚ) ≤ (supNorm a : ℚ) := by positivity
  linarith

theorem growthArg_nonneg {n : ℕ} (a : Fin n → ℤ) : 0 ≤ growthArg a :=
  le_trans zero_le_one (one_le_growthArg a)

theorem abs_input_le {n : ℕ} (a : Fin n → ℤ) (i : Fin n) : |(a i : ℚ)| ≤ growthArg a := by
  have h : |a i| ≤ (supNorm a : ℤ) := abs_le_supNorm a i
  have h' : |(a i : ℚ)| ≤ (supNorm a : ℚ) := by exact_mod_cast h
  have := one_le_growthArg a
  simp only [growthArg] at *
  linarith

/-! ### Two generic bounds -/

/-- An affine ℚ-form in the input is bounded by its coefficient sum times `N a`. -/
theorem abs_affine_le {n : ℕ} (g₀ : ℚ) (g : Fin n → ℚ) (a : Fin n → ℤ) :
    |g₀ + ∑ i, (a i : ℚ) * g i| ≤ (|g₀| + ∑ i, |g i|) * growthArg a := by
  have hN := one_le_growthArg a
  have hN0 := growthArg_nonneg a
  have h1 : |g₀| ≤ |g₀| * growthArg a := le_mul_of_one_le_right (abs_nonneg _) hN
  have h3 : ∑ i, |(a i : ℚ)| * |g i| ≤ ∑ i, growthArg a * |g i| :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (abs_input_le a i) (abs_nonneg _)
  have h4 : |∑ i, (a i : ℚ) * g i| ≤ ∑ i, |(a i : ℚ)| * |g i| := by
    calc |∑ i, (a i : ℚ) * g i| ≤ ∑ i, |(a i : ℚ) * g i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |(a i : ℚ)| * |g i| := by simp [abs_mul]
  have h5 : ∑ i, growthArg a * |g i| = growthArg a * ∑ i, |g i| := by rw [Finset.mul_sum]
  calc |g₀ + ∑ i, (a i : ℚ) * g i| ≤ |g₀| + |∑ i, (a i : ℚ) * g i| := abs_add_le _ _
    _ ≤ |g₀| * growthArg a + growthArg a * ∑ i, |g i| := by rw [← h5]; linarith
    _ = (|g₀| + ∑ i, |g i|) * growthArg a := by ring

/-- A bilinear ℚ-form is bounded by its coefficient sum times the two sup bounds. -/
theorem abs_bilin_le {ι : Type*} [Fintype ι] (M : ι → ι → ℚ) (v w : ι → ℚ) (S T : ℚ)
    (hS : ∀ k, |v k| ≤ S) (hT : ∀ k, |w k| ≤ T) (hS0 : 0 ≤ S) (_hT0 : 0 ≤ T) :
    |∑ k, ∑ k', v k * (M k k' * w k')| ≤ (∑ k, ∑ k', |M k k'|) * (S * T) := by
  have step : ∀ k k', |v k * (M k k' * w k')| ≤ |M k k'| * (S * T) := by
    intro k k'
    have : |v k * (M k k' * w k')| = |v k| * |M k k'| * |w k'| := by
      rw [abs_mul, abs_mul]; ring
    rw [this]
    have h1 : |v k| * |M k k'| ≤ S * |M k k'| :=
      mul_le_mul_of_nonneg_right (hS k) (abs_nonneg _)
    have h2 : S * |M k k'| * |w k'| ≤ S * |M k k'| * T :=
      mul_le_mul_of_nonneg_left (hT k') (by positivity)
    have h3 : |v k| * |M k k'| * |w k'| ≤ S * |M k k'| * |w k'| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have : S * |M k k'| * T = |M k k'| * (S * T) := by ring
    linarith [h3, h2, this.ge, this.le]
  calc |∑ k, ∑ k', v k * (M k k' * w k')|
      ≤ ∑ k, |∑ k', v k * (M k k' * w k')| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ k', |v k * (M k k' * w k')| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ k', |M k k'| * (S * T) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun k' _ => step k k'
    _ = (∑ k, ∑ k', |M k k'|) * (S * T) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### Explicit coefficient sums -/

/-- Coefficient sum of the output/witness quadratic part. -/
def quadCoeffSum : ℚ := ∑ k, ∑ k', |((D.P.Q (Sum.inr k) (Sum.inr k') : ℤ) : ℚ)|

/-- Coefficient sum of the input-only part `q(a)`. -/
def aPartCoeffSum : ℚ :=
  |((D.P.c : ℤ) : ℚ)| + (∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ)|)
    + ∑ i, ∑ j, |((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ)|

theorem quadCoeffSum_nonneg : 0 ≤ D.quadCoeffSum := by
  refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun k' _ => abs_nonneg _

theorem aPartCoeffSum_nonneg : 0 ≤ D.aPartCoeffSum := by
  refine add_nonneg (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _))
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)

theorem abs_aPart_le (a : Fin n → ℤ) :
    |((D.aPart a : ℤ) : ℚ)| ≤ D.aPartCoeffSum * (growthArg a) ^ 2 := by
  have hN := one_le_growthArg a
  have hN0 := growthArg_nonneg a
  have hsplit : ((D.aPart a : ℤ) : ℚ)
      = ((D.P.c : ℤ) : ℚ) + (∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ))
        + ∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ)) := by
    simp only [aPart]
    push_cast
    ring
  -- the three pieces
  have hc : |((D.P.c : ℤ) : ℚ)| ≤ |((D.P.c : ℤ) : ℚ)| * (growthArg a) ^ 2 :=
    le_mul_of_one_le_right (abs_nonneg _) (by nlinarith)
  have hl : |∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ)|
      ≤ (∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ)|) * (growthArg a) ^ 2 := by
    have h1 : |∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ)|
        ≤ ∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ)| * |(a i : ℚ)| := by
      calc |∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ)|
          ≤ ∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ)| * |(a i : ℚ)| := by simp [abs_mul]
    have h2 : ∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ)| * |(a i : ℚ)|
        ≤ ∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ)| * (growthArg a) ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (le_trans (abs_input_le a i) (by nlinarith)) (abs_nonneg _)
    rw [← Finset.sum_mul] at h2
    linarith
  have hq : |∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ))|
      ≤ (∑ i, ∑ j, |((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ)|) * (growthArg a) ^ 2 := by
    have := abs_bilin_le (fun i j => ((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ))
      (fun i => (a i : ℚ)) (fun i => (a i : ℚ)) (growthArg a) (growthArg a)
      (abs_input_le a) (abs_input_le a) hN0 hN0
    calc |∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ))|
        ≤ (∑ i, ∑ j, |((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ)|)
            * (growthArg a * growthArg a) := this
      _ = (∑ i, ∑ j, |((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ)|) * (growthArg a) ^ 2 := by ring
  rw [hsplit, aPartCoeffSum]
  calc |((D.P.c : ℤ) : ℚ) + (∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ))
          + ∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ))|
      ≤ |((D.P.c : ℤ) : ℚ) + ∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ)|
          + |∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ))| :=
        abs_add_le _ _
    _ ≤ (|((D.P.c : ℤ) : ℚ)| + |∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ)|)
          + |∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ))| := by
        have := abs_add_le ((D.P.c : ℤ) : ℚ) (∑ i, ((D.P.l (Sum.inl i) : ℤ) : ℚ) * (a i : ℚ))
        linarith
    _ ≤ (|((D.P.c : ℤ) : ℚ)| + (∑ i, |((D.P.l (Sum.inl i) : ℤ) : ℚ)|)
          + ∑ i, ∑ j, |((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ)|) * (growthArg a) ^ 2 := by
        nlinarith [hc, hl, hq]

/-! ### The affine centre, bounded -/

/-- Coefficient sum of an affine centre family. -/
def centreCoeffSum {m r n : ℕ} (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ) : ℚ :=
  ∑ k, (|c₀ k| + ∑ i, |cs i k|)

theorem centreCoeffSum_nonneg {m r n : ℕ} (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ) :
    0 ≤ centreCoeffSum c₀ cs :=
  Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem abs_centre_le {m r n : ℕ} (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (a : Fin n → ℤ) (k : OutWit m r) :
    |(c₀ + ∑ i, (a i : ℚ) • cs i) k| ≤ centreCoeffSum c₀ cs * growthArg a := by
  have hval : (c₀ + ∑ i, (a i : ℚ) • cs i) k = c₀ k + ∑ i, (a i : ℚ) * cs i k := by
    simp [Finset.sum_apply]
  have h1 : |c₀ k + ∑ i, (a i : ℚ) * cs i k|
      ≤ (|c₀ k| + ∑ i, |cs i k|) * growthArg a := abs_affine_le _ _ a
  have h2 : |c₀ k| + ∑ i, |cs i k| ≤ centreCoeffSum c₀ cs :=
    Finset.single_le_sum
      (f := fun k => |c₀ k| + ∑ i, |cs i k|)
      (fun _ _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      (Finset.mem_univ k)
  rw [hval]
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (growthArg_nonneg a))


/-! ### The residual, bounded quadratically -/

theorem abs_residual_le (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ) (a : Fin n → ℤ) :
    |D.residual a (c₀ + ∑ i, (a i : ℚ) • cs i)|
      ≤ (D.quadCoeffSum * (centreCoeffSum c₀ cs) ^ 2 + D.aPartCoeffSum) * (growthArg a) ^ 2 := by
  have hL0 : 0 ≤ centreCoeffSum c₀ cs := centreCoeffSum_nonneg c₀ cs
  have hN0 := growthArg_nonneg a
  have hb : ∀ k, |(c₀ + ∑ i, (a i : ℚ) • cs i) k| ≤ centreCoeffSum c₀ cs * growthArg a :=
    fun k => abs_centre_le c₀ cs a k
  have hQ : |D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i)|
      ≤ D.quadCoeffSum * ((centreCoeffSum c₀ cs * growthArg a) * (centreCoeffSum c₀ cs * growthArg a)) := by
    have := abs_bilin_le (fun k k' => ((D.P.Q (Sum.inr k) (Sum.inr k') : ℤ) : ℚ))
      (c₀ + ∑ i, (a i : ℚ) • cs i) (c₀ + ∑ i, (a i : ℚ) • cs i)
      (centreCoeffSum c₀ cs * growthArg a) (centreCoeffSum c₀ cs * growthArg a)
      hb hb (by positivity) (by positivity)
    simpa [zQuadQ, quadCoeffSum] using this
  have hA := D.abs_aPart_le a
  have hres : D.residual a (c₀ + ∑ i, (a i : ℚ) • cs i)
      = D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i) - ((D.aPart a : ℤ) : ℚ) := rfl
  have htri : |D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i) - ((D.aPart a : ℤ) : ℚ)|
      ≤ |D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i)| + |((D.aPart a : ℤ) : ℚ)| := by
    rw [sub_eq_add_neg]
    calc |D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i) + -((D.aPart a : ℤ) : ℚ)|
        ≤ |D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i)| + |-((D.aPart a : ℤ) : ℚ)| := abs_add_le _ _
      _ = |D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i)| + |((D.aPart a : ℤ) : ℚ)| := by rw [abs_neg]
  rw [hres]
  nlinarith [hQ, hA, htri]

/-! ### G22-T08 — linear growth of the defined function -/

/-- **G22-T08.**  A positive semidefinite output/witness form, an affine centre family and polar
representatives for the output coordinates force LINEAR growth of the defined function.  No bound
on the witnesses is used: they may be free, as in `P = (b − a)²`.  The integer constant is built
without a square root, by `K = 4WC₀ + 1 ≥ 1`, so `K² ≥ K ≥ 4WC₀`. -/
theorem linearGrowth_of_semidefinite
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (c₀ + ∑ i, (a i : ℚ) • cs i))
    {ws : Fin m → OutWit m r → ℚ}
    (hws : ∀ (j : Fin m) (v : OutWit m r → ℚ), D.zPolarQ (ws j) v = v (Sum.inl j))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f := by
  have hL0 : 0 ≤ centreCoeffSum c₀ cs := centreCoeffSum_nonneg c₀ cs
  have hqc := D.quadCoeffSum_nonneg
  have hac := D.aPartCoeffSum_nonneg
  set L := centreCoeffSum c₀ cs with hLdef
  set C₀ := D.quadCoeffSum * L ^ 2 + D.aPartCoeffSum with hC₀def
  set W := ∑ j, D.zQuadQ (ws j) with hWdef
  set K := 4 * W * C₀ + 1 with hKdef
  have hC₀0 : 0 ≤ C₀ := by
    have : 0 ≤ D.quadCoeffSum * L ^ 2 := by positivity
    linarith
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun j _ => hpos _
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 4 * W * C₀ := by positivity
    linarith
  have hK0 : 0 ≤ K := by linarith
  refine ⟨⌈L + K⌉₊, fun a => ?_⟩
  have hN0 := growthArg_nonneg a
  have hN1 := one_le_growthArg a
  obtain ⟨u, hu⟩ : D.Graph a (f a) := (hf a (f a)).mpr rfl
  set z : OutWit m r → ℤ := Sum.elim (f a) u with hzdef
  have hsol : D.SolZ a z := hu
  have hR : D.zQuadQ (toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i))
      = D.residual a (c₀ + ∑ i, (a i : ℚ) • cs i) := D.offCentre_norm (hcen a) hsol
  have hRnn : 0 ≤ D.residual a (c₀ + ∑ i, (a i : ℚ) • cs i) := by rw [← hR]; exact hpos _
  have hRle : D.residual a (c₀ + ∑ i, (a i : ℚ) • cs i) ≤ C₀ * (growthArg a) ^ 2 :=
    le_trans (le_abs_self _) (D.abs_residual_le c₀ cs a)
  have hcoord : ∀ j : Fin m, |((z (Sum.inl j) : ℤ) : ℚ)| ≤ (L + K) * growthArg a := by
    intro j
    have hcau := D.outCoord_sq_le hpos (hws j) (toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i))
    have hQwj : D.zQuadQ (ws j) ≤ W :=
      Finset.single_le_sum (f := fun j => D.zQuadQ (ws j)) (fun j _ => hpos _) (Finset.mem_univ j)
    have hQwj0 : 0 ≤ D.zQuadQ (ws j) := hpos _
    have hb1 : 4 * D.zQuadQ (ws j) * D.zQuadQ (toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i))
        ≤ 4 * W * (C₀ * (growthArg a) ^ 2) := by
      rw [hR]
      exact mul_le_mul (by linarith) hRle hRnn (by linarith)
    have hKK : 4 * W * C₀ ≤ K ^ 2 := by nlinarith
    have hb2 : 4 * W * (C₀ * (growthArg a) ^ 2) ≤ (K * growthArg a) ^ 2 := by
      nlinarith [sq_nonneg (growthArg a)]
    have hsq : ((toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i)) (Sum.inl j)) ^ 2
        ≤ (K * growthArg a) ^ 2 := by linarith
    have habs : |((toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i)) (Sum.inl j))| ≤ K * growthArg a := by
      nlinarith [sq_abs ((toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i)) (Sum.inl j)),
        abs_nonneg ((toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i)) (Sum.inl j)),
        mul_nonneg hK0 hN0]
    have hval : (toQ z - (c₀ + ∑ i, (a i : ℚ) • cs i)) (Sum.inl j)
        = ((z (Sum.inl j) : ℤ) : ℚ) - (c₀ + ∑ i, (a i : ℚ) • cs i) (Sum.inl j) := rfl
    rw [hval] at habs
    have hhb : |(c₀ + ∑ i, (a i : ℚ) • cs i) (Sum.inl j)| ≤ L * growthArg a :=
      abs_centre_le c₀ cs a _
    have htri := abs_add_le (((z (Sum.inl j) : ℤ) : ℚ)
      - (c₀ + ∑ i, (a i : ℚ) • cs i) (Sum.inl j)) ((c₀ + ∑ i, (a i : ℚ) • cs i) (Sum.inl j))
    have heq : (((z (Sum.inl j) : ℤ) : ℚ) - (c₀ + ∑ i, (a i : ℚ) • cs i) (Sum.inl j))
        + (c₀ + ∑ i, (a i : ℚ) • cs i) (Sum.inl j) = ((z (Sum.inl j) : ℤ) : ℚ) := by ring
    rw [heq] at htri
    calc |((z (Sum.inl j) : ℤ) : ℚ)| ≤ K * growthArg a + L * growthArg a := by linarith
      _ = (L + K) * growthArg a := by ring
  simp only [supNorm]
  refine Finset.sup_le fun j _ => ?_
  have hfz : f a j = z (Sum.inl j) := rfl
  have h1 : ((f a j).natAbs : ℚ) = |((f a j : ℤ) : ℚ)| := by
    have h0 := congrArg (fun t : ℤ => (t : ℚ)) (Int.natCast_natAbs (f a j))
    push_cast at h0
    simpa using h0
  have h5 : ((⌈L + K⌉₊ * (1 + supNorm a) : ℕ) : ℚ) = (⌈L + K⌉₊ : ℚ) * growthArg a := by
    simp only [growthArg]
    push_cast
    ring
  have hq : ((f a j).natAbs : ℚ) ≤ ((⌈L + K⌉₊ * (1 + supNorm a) : ℕ) : ℚ) := by
    rw [h1, hfz, h5]
    have h2 := hcoord j
    have h3 : (L + K) ≤ (⌈L + K⌉₊ : ℚ) := Nat.le_ceil _
    have h4 : (L + K) * growthArg a ≤ (⌈L + K⌉₊ : ℚ) * growthArg a :=
      mul_le_mul_of_nonneg_right h3 hN0
    linarith
  exact_mod_cast hq


/-! ### The payoff and the controls -/

/-- **The semidefinite branch, closed.**  Together with `dim_le_of_linearGrowth_injective` (G21-T09)
this is one of the two disjuncts of the II-D summit, discharged without any coercivity. -/
theorem dim_le_of_semidefinite
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (c₀ + ∑ i, (a i : ℚ) • cs i))
    {ws : Fin m → OutWit m r → ℚ}
    (hws : ∀ (j : Fin m) (v : OutWit m r → ℚ), D.zPolarQ (ws j) v = v (Sum.inl j))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ m :=
  dim_le_of_linearGrowth_injective (D.linearGrowth_of_semidefinite hpos hcen hws hf) hinj

/-- POSITIVE control, and a usable corollary: when the form is nondegenerate the centre family and
the output representatives BOTH come for free, so the hypothesis package of
`linearGrowth_of_semidefinite` is jointly satisfiable and the theorem is not vacuous. -/
theorem linearGrowth_of_semidefinite_nondeg
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) (hnd : D.NondegQ)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f := by
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_nondegQ hnd
  have hrep : ∀ j : Fin m, ∃ w : OutWit m r → ℚ, ∀ v, D.zPolarQ w v = v (Sum.inl j) := by
    intro j
    refine D.exists_polar_representative ?_
    intro e he
    by_cases h0 : e = 0
    · subst h0; simp
    · obtain ⟨w, hw⟩ := hnd e h0
      exact absurd (he w) hw
  choose ws hws using hrep
  exact D.linearGrowth_of_semidefinite hpos hcen hws hf

theorem dim_le_of_semidefinite_nondeg
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) (hnd : D.NondegQ)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ m :=
  dim_le_of_linearGrowth_injective (D.linearGrowth_of_semidefinite_nondeg hpos hnd hf) hinj

/-- NEGATIVE control for the SHAPE of the theorem: the form is CONSTANT along every radical
direction, so no bound of the form `c‖z‖² ≤ N Q(z)` can hold once the radical is nonzero, however
the constants are chosen.  Bounding the output is therefore not a convenience but the only
available route — this is E-21-2 stated as a theorem rather than as a single counterexample. -/
theorem zQuadQ_invariant_along_radical {v e : OutWit m r → ℚ} (he : D.InRadicalQ e) (t : ℚ) :
    D.zQuadQ (v + t • e) = D.zQuadQ v := by
  have h1 : D.zPolarQ v e = 0 := by rw [D.zPolarQ_symm v e]; exact he v
  have h2 : D.zQuadQ e = 0 := by
    have h := he e
    rw [D.zPolarQ_self] at h
    linarith
  rw [D.zQuadQ_add, D.zPolarQ_smul_right, D.zQuadQ_smul, h1, h2]
  ring

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
