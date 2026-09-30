/-
  DoubledCentre.lean — Gate-20 Packet R1 (tasks R1.1, R1.2, R1.3).

  Reviewer P0 #4: "integral centre" and "doubled centre integral" are different hypotheses,
  and the LATTICE REFLECTION only needs the second.  `C3Reflection.lean` (s45) assumed the
  first: its `CentreId` reflects `(y,u) ↦ (2(p x + q) − y, 2(r x + s) − u)`, i.e. the centre
  itself is an integer affine function of the input.  Here the centre is allowed to be
  half-integral: the reflection is

      (y, u) ↦ (h_y(x) − y, h_u(x) − u),   h_y(x) = p x + q,  h_u(x) = r x + s   (p q r s : ℤ)

  so the CENTRE is `(h_y/2, h_u/2)` and only its DOUBLE is required to be integral.

  Results.
  * `doubledCentre_iff`        — the identity holds iff the four integer conditions
                                 `2ap + br + 2d = 0`, `2aq + bs + 2g = 0`,
                                 `bp + 2cr + 2e = 0`, `bq + 2cs + 2h = 0` hold.
  * `centreId_imp_doubledCentre` — the s45 hypothesis is the special case `(2p,2q,2r,2s)`;
                                 nothing proved in `C3Reflection.lean` is lost.
  * `rgen_reflect_doubled`     — the reflection of a solution is a solution.
  * `rgen_unique_forces_doubled_centre` — unique output forces `2y = p x + q`
                                 (NOT `y = p x + q`: the output may be half-integral in the
                                 centre coordinate, and that is the point).
  * `rgen_doubled_global` / `rgen_doubled_full` — total + unique ⇒ the output function is a
                                 GLOBAL degree-≤1 polynomial with RATIONAL (half-integer)
                                 coefficients, hence `FullCosetNF`.  No coset restriction is
                                 needed: `QuadForm` has ℚ coefficients by design.
  * `control_iii_doubled_centre` (R1.3) — `(2y − x)² + (2u − 1)² − 2` DOES admit the doubled
                                 centre `(x, 1)`, i.e. is invariant under `(y,u) ↦ (x−y, 1−u)`.
                                 `C3Reflection.control_iii_no_integral_centre` remains true and
                                 is re-exported here with the corrected reading: what fails for
                                 that relation is the INTEGRAL centre, not the reflection.
  * R1.1 controls — `y² + (2u−1)² − 1` is total with unique output `y = 0` and TWO witnesses;
                    `y² + (u−v)²` is total with unique output `0` and INFINITELY many witness
                    pairs.  Both are kernel witnesses for P0 #2: unique output implies neither
                    unique witness nor finiteness of the solution set.

  Claim tags: every theorem below is [P] (std-3, no `sorry`, no new axiom).
  Baseline (mpup-lean r39) is read-only and imports nothing from here.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.SetNotationForOrder
import ResearchUpgrade.C3Reflection
import ResearchUpgrade.CosetNormalForm

namespace DiophCompression.ResearchUpgrade

open Matrix

/-! ## R1.2 — the doubled-centre reflection interface -/

/-- The doubled-centre identity: `P` is invariant under the reflection
`(y,u) ↦ (p x + q − y, r x + s − u)` for all `x, y, u`.  The centre is `((px+q)/2, (rx+s)/2)`;
only its double is required to be integral. -/
def DoubledCentreId (a b c d e f g h i j p q r s : ℤ) : Prop :=
  ∀ x y u : ℤ,
    Pgen a b c d e f g h i j x y u
      = Pgen a b c d e f g h i j x ((p * x + q) - y) ((r * x + s) - u)

/-- The doubled-centre identity holds iff the gradient of the `(y,u)`-part vanishes at the
half-integral centre, as a polynomial identity in `x`. -/
theorem doubledCentre_iff (a b c d e f g h i j p q r s : ℤ) :
    DoubledCentreId a b c d e f g h i j p q r s ↔
      (2 * a * p + b * r + 2 * d = 0 ∧ 2 * a * q + b * s + 2 * g = 0 ∧
        b * p + 2 * c * r + 2 * e = 0 ∧ b * q + 2 * c * s + 2 * h = 0) := by
  constructor
  · intro hh
    have e1 := hh 1 1 0
    have e2 := hh 1 0 0
    have e3 := hh 0 1 0
    have e4 := hh 0 0 0
    have e5 := hh 0 0 1
    have e6 := hh 1 0 1
    simp only [Pgen] at e1 e2 e3 e4 e5 e6
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination e1 - e2 - e3 + e4
    · linear_combination e3 - e4
    · linear_combination e6 - e2 - e5 + e4
    · linear_combination e5 - e4
  · rintro ⟨hc1, hc2, hc3, hc4⟩ x y u
    have key : (2 : ℤ) * (Pgen a b c d e f g h i j x y u
        - Pgen a b c d e f g h i j x ((p * x + q) - y) ((r * x + s) - u)) = 0 := by
      simp only [Pgen]
      linear_combination (2 * x * y - (p * x + q) * x) * hc1 + (2 * y - (p * x + q)) * hc2
        + (2 * x * u - (r * x + s) * x) * hc3 + (2 * u - (r * x + s)) * hc4
    linarith

/-- The s45 integral-centre hypothesis is the special case in which the doubled centre has
even coefficients.  Nothing proved under `CentreId` is lost. -/
theorem centreId_imp_doubledCentre (a b c d e f g h i j p q r s : ℤ)
    (hc : CentreId a b c d e f g h i j p q r s) :
    DoubledCentreId a b c d e f g h i j (2 * p) (2 * q) (2 * r) (2 * s) := by
  rw [centre_iff] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [doubledCentre_iff]
  refine ⟨by linear_combination 2 * h1, by linear_combination 2 * h2,
    by linear_combination 2 * h3, by linear_combination 2 * h4⟩

/-- Reflection of a solution is a solution. -/
theorem rgen_reflect_doubled (a b c d e f g h i j p q r s : ℤ)
    (hc : DoubledCentreId a b c d e f g h i j p q r s) (x y : ℤ)
    (hR : Rgen a b c d e f g h i j x y) :
    Rgen a b c d e f g h i j x ((p * x + q) - y) := by
  obtain ⟨u, hu⟩ := hR
  exact ⟨(r * x + s) - u, by rw [← hc x y u]; exact hu⟩

/-- Uniqueness of the output forces the output onto the (possibly half-integral) centre:
`2y = p x + q`. -/
theorem rgen_unique_forces_doubled_centre (a b c d e f g h i j p q r s : ℤ)
    (hc : DoubledCentreId a b c d e f g h i j p q r s)
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    ∀ x y, Rgen a b c d e f g h i j x y → 2 * y = p * x + q := by
  intro x y hxy
  have hrefl := rgen_reflect_doubled a b c d e f g h i j p q r s hc x y hxy
  have hEq := hU x y ((p * x + q) - y) hxy hrefl
  linarith

/-- Total + unique output ⇒ the output function is a single degree-≤1 polynomial over ℚ with
half-integer coefficients.  No coset restriction is needed. -/
theorem rgen_doubled_global (a b c d e f g h i j p q r s : ℤ)
    (hc : DoubledCentreId a b c d e f g h i j p q r s)
    (hT : RelTotal (Rgen a b c d e f g h i j))
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    GlobalQuadratic (rgenOut a b c d e f g h i j hT) := by
  refine ⟨⟨(q : ℚ) / 2, fun _ => (p : ℚ) / 2, 0⟩, fun v => ?_⟩
  have hval : Rgen a b c d e f g h i j (v 0) (Classical.choose (hT (v 0))) :=
    Classical.choose_spec (hT (v 0))
  have hy : 2 * Classical.choose (hT (v 0)) = p * (v 0) + q :=
    rgen_unique_forces_doubled_centre a b c d e f g h i j p q r s hc hU (v 0) _ hval
  have hyQ : (2 : ℚ) * ((Classical.choose (hT (v 0)) : ℤ) : ℚ)
      = (p : ℚ) * ((v 0 : ℤ) : ℚ) + (q : ℚ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hy
  simp only [rgenOut]
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.zero_apply,
    mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  linarith

theorem rgen_doubled_full (a b c d e f g h i j p q r s : ℤ)
    (hc : DoubledCentreId a b c d e f g h i j p q r s)
    (hT : RelTotal (Rgen a b c d e f g h i j))
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    FullCosetNF (rgenOut a b c d e f g h i j hT) :=
  globalQuadratic_imp_fullCoset (rgen_doubled_global a b c d e f g h i j p q r s hc hT hU)

/-! ## R1.3 — the half-centre control, corrected

`(2y − x)² + (2u − 1)² − 2 = 4y² + 4u² − 4xy + x² − 4u − 1` has NO integral centre
(`C3Reflection.control_iii_no_integral_centre`), which s45 recorded as "the reflection
argument does not apply".  That reading was wrong: the DOUBLED centre `(x, 1)` is integral and
the relation is invariant under `(y,u) ↦ (x − y, 1 − u)`. -/

theorem control_iii_doubled_centre :
    DoubledCentreId 4 0 4 (-4) 0 1 0 (-4) 0 (-1) 1 0 0 1 :=
  (doubledCentre_iff 4 0 4 (-4) 0 1 0 (-4) 0 (-1) 1 0 0 1).mpr (by norm_num)

/-- The corrected pair, stated together: no integral centre, but a doubled centre. -/
theorem control_iii_half_centre :
    (¬ ∃ p q r s : ℤ, CentreId 4 0 4 (-4) 0 1 0 (-4) 0 (-1) p q r s) ∧
      DoubledCentreId 4 0 4 (-4) 0 1 0 (-4) 0 (-1) 1 0 0 1 :=
  ⟨control_iii_no_integral_centre, control_iii_doubled_centre⟩

/-! ## R1.1 — unique output implies neither unique witness nor finiteness

Reviewer P0 #2 and regression control #9. -/

/-! ### Control (a): `y² + (2u − 1)² − 1` — unique output `y = 0`, exactly two witnesses. -/

/-- `Pgen 1 0 4 0 0 0 0 (-4) 0 0 x y u = y² + 4u² − 4u = y² + (2u−1)² − 1`. -/
theorem r11a_eq (x y u : ℤ) :
    Pgen 1 0 4 0 0 0 0 (-4) 0 0 x y u = y ^ 2 + (2 * u - 1) ^ 2 - 1 := by
  simp only [Pgen]; ring

theorem r11a_total : RelTotal (Rgen 1 0 4 0 0 0 0 (-4) 0 0) := by
  intro x
  exact ⟨0, 0, by simp only [Pgen]; ring⟩

theorem r11a_unique : RelUnique (Rgen 1 0 4 0 0 0 0 (-4) 0 0) := by
  have key : ∀ x y : ℤ, Rgen 1 0 4 0 0 0 0 (-4) 0 0 x y → y = 0 := by
    rintro _x y ⟨u, hu⟩
    simp only [Pgen] at hu
    have hnn : 0 ≤ 4 * u ^ 2 - 4 * u := by
      rcases le_or_gt 1 u with hu1 | hu1
      · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ u) (by linarith : (0:ℤ) ≤ u - 1)]
      · have hu0 : u ≤ 0 := by omega
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -u) (by linarith : (0:ℤ) ≤ 1 - u)]
    have hy2 : y ^ 2 = 0 := by nlinarith [sq_nonneg y]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy2
  intro x y y' h h'
  rw [key x y h, key x y' h']

/-- The output `y = 0` is reached by TWO different witnesses, `u = 0` and `u = 1`. -/
theorem r11a_two_witnesses (x : ℤ) :
    Pgen 1 0 4 0 0 0 0 (-4) 0 0 x 0 0 = 0 ∧ Pgen 1 0 4 0 0 0 0 (-4) 0 0 x 0 1 = 0 ∧
      (0 : ℤ) ≠ 1 := by
  refine ⟨by simp only [Pgen]; ring, by simp only [Pgen]; ring, by norm_num⟩

/-! ### Control (b): `y² + (u − v)²` — unique output `0`, infinitely many witness pairs.

Two witnesses, so this relation lives outside `Rgen`; it is defined directly. -/

/-- `∃ u v, y² + (u − v)² = 0`: input `x` (dummy), output `y`, witness pair `(u,v)`. -/
def R2wit (_x y : ℤ) : Prop := ∃ u v : ℤ, y ^ 2 + (u - v) ^ 2 = 0

theorem r11b_total : RelTotal R2wit := fun _ => ⟨0, 0, 0, by ring⟩

theorem r11b_unique : RelUnique R2wit := by
  have key : ∀ x y : ℤ, R2wit x y → y = 0 := by
    rintro _x y ⟨u, v, huv⟩
    have hy2 : y ^ 2 = 0 := by nlinarith [sq_nonneg y, sq_nonneg (u - v)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy2
  intro x y y' h h'
  rw [key x y h, key x y' h']

/-- The witness set at the unique output `y = 0` is infinite: every diagonal pair `(t,t)`
is a witness.  Unique output therefore implies neither unique witness nor finiteness of the
solution set (reviewer P0 #2, regression control #9). -/
theorem r11b_witnesses_infinite :
    {w : ℤ × ℤ | (0 : ℤ) ^ 2 + (w.1 - w.2) ^ 2 = 0}.Infinite := by
  have hinj : Function.Injective (fun t : ℤ => ((t, t) : ℤ × ℤ)) := by
    intro t t' htt
    simpa using congrArg Prod.fst htt
  have hsub : Set.range (fun t : ℤ => ((t, t) : ℤ × ℤ))
      ⊆ {w : ℤ × ℤ | (0 : ℤ) ^ 2 + (w.1 - w.2) ^ 2 = 0} := by
    rintro w ⟨t, rfl⟩
    simp
  exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)

end DiophCompression.ResearchUpgrade
