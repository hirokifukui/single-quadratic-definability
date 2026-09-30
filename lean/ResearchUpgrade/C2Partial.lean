/-
  C2Partial.lean — Gate-18 research program, Packet c2_partial.
  Four deliverables:
    1. C2-1 multi-input rigidity: for Δ(x) = xᵀAx + b·x + c with `∀ x, IsSquare (Δ x)`,
       (a) the LINE LEMMA (every one-variable restriction `t ↦ Δ(ρ + t v)` is a perfect-square
           quadratic, so `4·(vᵀAv)·Δ(ρ) = (∂_v Δ(ρ))²` and `IsSquare (vᵀAv)`), and
       (b) the CONSEQUENCE: the quadratic part `Q(v) = vᵀAv` is the square of a ℚ-linear form,
           and `Δ` itself is the square of a ℚ-affine form.
    2. C0-3 NO-GO in Lean: the divisibility relation `dvdRel x y := ∃ z, y = x·z` (one degree-2
       equation) is total but NOT unique, with a linear-in-`X` fibre count — hence every rigidity
       statement in this program assumes `RelTotal ∧ RelUnique`.
    3. C4-4 baseline bridge: `SingleQuadraticDefinableFunctionZZ (pad h)` via the witness-free
       polynomial `Σ_{j<m} (Y_j − (pad X)_j)²` of total degree ≤ 2.
    4. QuadForm ↔ MvPolynomial: `QuadForm.toMv` with its evaluation identity and degree bound.

  Baseline (mpup-lean r39) is read-only; nothing here is imported by the baseline. No sorry, no axiom.
-/
import DiophCompression.FiniteFiberGrowth
import MPUP.Spec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Int.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Defs
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.Counting
import ResearchUpgrade.OneInputNoWitness
import ResearchUpgrade.SmallLeaves

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial MPUP
open scoped Classical

/-! ## Part 1 — C2-1 multi-input rigidity

`Δ(x) = xᵀ A x + b·x + c` for `A : Matrix (Fin n) (Fin n) ℤ`, `b : Fin n → ℤ`, `c : ℤ`. -/

/-- The QuadForm-style integer polynomial `Δ(x) = xᵀ A x + b·x + c`. -/
def deltaQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (c : ℤ) (x : Fin n → ℤ) : ℤ :=
  x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c

/-- The line expansion: `Δ(ρ + t v) = (vᵀAv) t² + (ρᵀAv + vᵀAρ + b·v) t + Δ(ρ)`. -/
theorem deltaQ_line {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (c : ℤ)
    (ρ v : Fin n → ℤ) (t : ℤ) :
    deltaQ A b c (ρ + t • v)
      = (v ⬝ᵥ (A *ᵥ v)) * t ^ 2
        + (ρ ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ (A *ᵥ ρ) + b ⬝ᵥ v) * t + deltaQ A b c ρ := by
  simp only [deltaQ, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  ring

/-- **C2-1(a) — LINE LEMMA.** For every `ρ v`, the discriminant identity `4·(vᵀAv)·Δ(ρ) =
(ρᵀAv + vᵀAρ + b·v)²` holds and the quadratic part `vᵀAv` is a perfect square. -/
theorem c21_line {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (c : ℤ)
    (hsq : ∀ x : Fin n → ℤ, IsSquare (deltaQ A b c x)) (ρ v : Fin n → ℤ) :
    4 * (v ⬝ᵥ (A *ᵥ v)) * deltaQ A b c ρ
        = (ρ ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ (A *ᵥ ρ) + b ⬝ᵥ v) ^ 2
      ∧ IsSquare (v ⬝ᵥ (A *ᵥ v)) := by
  have hs : ∀ t : ℤ, IsSquare ((v ⬝ᵥ (A *ᵥ v)) * t ^ 2
      + (ρ ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ (A *ᵥ ρ) + b ⬝ᵥ v) * t + deltaQ A b c ρ) := by
    intro t; rw [← deltaQ_line]; exact hsq _
  obtain ⟨_, h4, hsqA⟩ := rigidity_deg_le_two _ _ _ hs
  exact ⟨by linear_combination h4, hsqA⟩

/-- **C2-1(b) — quadratic part is a square of a ℚ-linear form.**
`Q(v) = vᵀAv` equals `(ℓ·v)²` over ℚ for a fixed linear form `ℓ`. -/
theorem c21_quadratic_part_square {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (c : ℤ)
    (hsq : ∀ x : Fin n → ℤ, IsSquare (deltaQ A b c x)) :
    ∃ ℓ : Fin n → ℚ, ∀ v : Fin n → ℤ, ((v ⬝ᵥ (A *ᵥ v) : ℤ) : ℚ) = (ℓ ⬝ᵥ castQ v) ^ 2 := by
  by_cases hex : ∃ ρ, deltaQ A b c ρ ≠ 0
  · obtain ⟨ρ₀, hρ₀⟩ := hex
    obtain ⟨m, hm⟩ := hsq ρ₀
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hρ₀ hm
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
    refine ⟨fun j => (ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) j / (2 * (m : ℚ)), fun v => ?_⟩
    obtain ⟨hline, _⟩ := c21_line A b c hsq ρ₀ v
    have hw : ρ₀ ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ (A *ᵥ ρ₀) + b ⬝ᵥ v = (ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) ⬝ᵥ v := by
      rw [dotProduct_mulVec, dotProduct_comm v (A *ᵥ ρ₀), add_dotProduct, add_dotProduct]
    rw [hw, hm] at hline
    -- `hline : 4 * (v ⬝ᵥ (A *ᵥ v)) * (m * m) = ((ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) ⬝ᵥ v) ^ 2`
    have hcast : (((ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) ⬝ᵥ v : ℤ) : ℚ)
        = ∑ i, ((ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) i : ℚ) * (v i : ℚ) := by
      rw [dotProduct, Int.cast_sum]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
    have hℓ : (fun j => (ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) j / (2 * (m : ℚ))) ⬝ᵥ castQ v
        = (((ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) ⬝ᵥ v : ℤ) : ℚ) / (2 * (m : ℚ)) := by
      rw [hcast, Finset.sum_div]
      simp only [dotProduct, castQ]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hℓ, div_pow, eq_div_iff (pow_ne_zero 2 (mul_ne_zero two_ne_zero hmQ))]
    have hlineQ : (4 : ℚ) * ((v ⬝ᵥ (A *ᵥ v) : ℤ) : ℚ) * ((m : ℚ) * (m : ℚ))
        = (((ρ₀ ᵥ* A + A *ᵥ ρ₀ + b) ⬝ᵥ v : ℤ) : ℚ) ^ 2 := by exact_mod_cast hline
    linear_combination hlineQ
  · rw [not_exists] at hex
    simp only [not_not] at hex
    refine ⟨0, fun v => ?_⟩
    have hQid : deltaQ A b c v + deltaQ A b c (-v) - 2 * deltaQ A b c 0
        = 2 * (v ⬝ᵥ (A *ᵥ v)) := by
      simp only [deltaQ, mulVec_neg, dotProduct_neg, neg_dotProduct, mulVec_zero, dotProduct_zero]
      ring
    have hQ0 : v ⬝ᵥ (A *ᵥ v) = 0 := by
      have : (2 : ℤ) * (v ⬝ᵥ (A *ᵥ v)) = 0 := by
        rw [← hQid, hex v, hex (-v), hex 0]; ring
      linarith
    rw [hQ0]; simp

/-- **C2-1(b) — affine square.** `Δ` itself is the square of a ℚ-affine form `ℓ·x + s`. -/
theorem c21_affine_square {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (c : ℤ)
    (hsq : ∀ x : Fin n → ℤ, IsSquare (deltaQ A b c x)) :
    ∃ (ℓ : Fin n → ℚ) (s : ℚ), ∀ x : Fin n → ℤ, ((deltaQ A b c x : ℤ) : ℚ) = (ℓ ⬝ᵥ castQ x + s) ^ 2 := by
  have hd0 : deltaQ A b c 0 = c := by
    simp only [deltaQ, mulVec_zero, dotProduct_zero, add_zero, zero_add]
  have hbeta0 : ∀ v : Fin n → ℤ,
      (0 : Fin n → ℤ) ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ (A *ᵥ (0 : Fin n → ℤ)) + b ⬝ᵥ v = b ⬝ᵥ v := by
    intro v
    simp only [zero_dotProduct, mulVec_zero, dotProduct_zero, add_zero, zero_add]
  have hline0 : ∀ v : Fin n → ℤ, 4 * (v ⬝ᵥ (A *ᵥ v)) * c = (b ⬝ᵥ v) ^ 2 := by
    intro v
    obtain ⟨hl, _⟩ := c21_line A b c hsq 0 v
    rw [hbeta0 v, hd0] at hl; exact hl
  by_cases hc : deltaQ A b c 0 = 0
  · -- degenerate branch `c = 0`; `b·x = 0` for all `x`, and `Δ = Q = (ℓ·x)²`.
    obtain ⟨ℓ, hℓ⟩ := c21_quadratic_part_square A b c hsq
    have hc0 : c = 0 := by rw [← hd0]; exact hc
    refine ⟨ℓ, 0, fun x => ?_⟩
    have hbx : b ⬝ᵥ x = 0 := by
      have := hline0 x; rw [hc0, mul_zero] at this
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this.symm
    have hdeq : deltaQ A b c x = x ⬝ᵥ (A *ᵥ x) := by
      simp only [deltaQ, hbx, hc0, add_zero]
    rw [hdeq, add_zero]; exact hℓ x
  · -- generic branch `c ≠ 0`: `ℓ = b/(2m)`, `s = m` where `m² = c`.
    obtain ⟨m, hm⟩ := hsq 0
    have hcm : c = m * m := by rw [← hd0]; exact hm
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hcm; exact hc (by rw [hd0, hcm])
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
    refine ⟨fun j => (b j : ℚ) / (2 * (m : ℚ)), (m : ℚ), fun x => ?_⟩
    have hcast : ((b ⬝ᵥ x : ℤ) : ℚ) = ∑ i, (b i : ℚ) * (x i : ℚ) := by
      rw [dotProduct, Int.cast_sum]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
    have hℓx : (fun j => (b j : ℚ) / (2 * (m : ℚ))) ⬝ᵥ castQ x
        = ((b ⬝ᵥ x : ℤ) : ℚ) / (2 * (m : ℚ)) := by
      rw [hcast, Finset.sum_div]
      simp only [dotProduct, castQ]
      apply Finset.sum_congr rfl; intro i _; ring
    have h2mq : 2 * (m : ℚ) * ((fun j => (b j : ℚ) / (2 * (m : ℚ))) ⬝ᵥ castQ x)
        = ((b ⬝ᵥ x : ℤ) : ℚ) := by rw [hℓx]; field_simp
    have hLQ : (4 : ℚ) * ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) * ((m : ℚ) * (m : ℚ))
        = ((b ⬝ᵥ x : ℤ) : ℚ) ^ 2 := by
      have := hline0 x; rw [hcm] at this; exact_mod_cast this
    have hqsq : ((fun j => (b j : ℚ) / (2 * (m : ℚ))) ⬝ᵥ castQ x) ^ 2
        = ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) := by
      rw [hℓx, div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero two_ne_zero hmQ))]
      linear_combination -hLQ
    have hdx : ((deltaQ A b c x : ℤ) : ℚ)
        = ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) + ((b ⬝ᵥ x : ℤ) : ℚ) + (m : ℚ) * (m : ℚ) := by
      simp only [deltaQ]; rw [hcm]; push_cast; ring
    rw [hdx]
    linear_combination -hqsq - h2mq

/-! ## Part 2 — C0-3 NO-GO: `dvdRel` is total but not unique

`dvdRel x y := ∃ z, y = x·z` is a single equation of degree 2.  Its fibre over `x ≠ 0` is the whole
set of multiples of `x`, which is dense (`≥ 2·⌊X/|x|⌋ + 1` outputs below height `X`).  This is why
every rigidity statement in this program assumes `RelTotal ∧ RelUnique`. -/

/-- The divisibility relation, presented as a single degree-2 equation `y = x·z`. -/
def dvdRel (x y : ℤ) : Prop := ∃ z : ℤ, y = x * z

/-- The fibre of `dvdRel` over `x` is exactly the set of multiples of `x`. -/
theorem dvdRel_fiber (x : ℤ) : {y | dvdRel x y} = {y | x ∣ y} := by
  ext y
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz⟩⟩

/-- `dvdRel` is total: every input `x` has the output `0`. -/
theorem dvdRel_total : RelTotal dvdRel := fun x => ⟨0, 0, by ring⟩

/-- `dvdRel` is NOT unique: at `x = 1` both `0` and `1` are outputs. -/
theorem dvdRel_not_unique : ¬ RelUnique dvdRel := by
  intro hU
  have h := hU 1 0 1 ⟨0, by ring⟩ ⟨1, by ring⟩
  exact absurd h (by norm_num)

/-- **C0-3 density.** For `x ≠ 0`, the fibre `{y | dvdRel x y}` has at least `2·⌊X/|x|⌋ + 1`
outputs of height `≤ X` — a linear-in-`X` lower bound, incompatible with any finite-fibre rigidity. -/
theorem dvdRel_fiberCount_ge (x : ℤ) (hx : x ≠ 0) (X : ℕ) :
    2 * (X / x.natAbs) + 1 ≤ fiberCountZZ {y | dvdRel x y} X := by
  classical
  set q : ℕ := X / x.natAbs with hq
  have hsub : (Finset.Icc (-(q : ℤ)) (q : ℤ)).image (fun k => x * k)
      ⊆ (Finset.Icc (-(X : ℤ)) (X : ℤ)).filter (fun c => c ∈ {y | dvdRel x y}) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    rw [Finset.mem_Icc] at hk
    have hkabs : |k| ≤ (q : ℤ) := abs_le.mpr hk
    have hle : |x * k| ≤ (X : ℤ) := by
      rw [abs_mul]
      calc |x| * |k| ≤ |x| * (q : ℤ) := by
            exact mul_le_mul_of_nonneg_left hkabs (abs_nonneg x)
        _ ≤ (X : ℤ) := by
            rw [Int.abs_eq_natAbs]
            have hqm : q * x.natAbs ≤ X := Nat.div_mul_le_self X x.natAbs
            calc (x.natAbs : ℤ) * (q : ℤ) = ((q * x.natAbs : ℕ) : ℤ) := by push_cast; ring
              _ ≤ (X : ℤ) := by exact_mod_cast hqm
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp hle).1, (abs_le.mp hle).2⟩, ⟨k, rfl⟩⟩
  have hcard : ((Finset.Icc (-(q : ℤ)) (q : ℤ)).image (fun k => x * k)).card = 2 * q + 1 := by
    rw [Finset.card_image_of_injective _ (mul_right_injective₀ hx), Int.card_Icc]
    rw [show ((q : ℤ) + 1 - (-(q : ℤ))) = ((2 * q + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  calc 2 * (X / x.natAbs) + 1 = 2 * q + 1 := by rw [hq]
    _ = ((Finset.Icc (-(q : ℤ)) (q : ℤ)).image (fun k => x * k)).card := hcard.symm
    _ ≤ fiberCountZZ {y | dvdRel x y} X := Finset.card_le_card hsub

/-! ## Part 3 — C4-4 baseline bridge: `SingleQuadraticDefinableFunctionZZ (pad h)`

The zero-padding `pad : (Fin n → ℤ) → (Fin m → ℤ)` (for `n ≤ m`) is the unique zero of the
witness-free degree-2 polynomial `Σ_{j<m} (Y_j − (pad X)_j)²` in `Poly (n + m) 0`. -/

/-- The `j`-th "target" term: `X_i` if the output coordinate `j` corresponds to an input coordinate
`i < n`, else `0`. -/
noncomputable def padMv {n m : ℕ} (_h : n ≤ m) (j : Fin m) : Poly (n + m) 0 :=
  if hj : (j : ℕ) < n then X (Sum.inl (Fin.castAdd m ⟨j, hj⟩)) else 0

/-- The witness-free defining polynomial `Σ_{j<m} (Y_j − (pad X)_j)²`. -/
noncomputable def padPoly {n m : ℕ} (h : n ≤ m) : Poly (n + m) 0 :=
  ∑ j : Fin m, (X (Sum.inl (Fin.natAdd n j)) - padMv h j) ^ 2

theorem padPoly_totalDegree_le {n m : ℕ} (h : n ≤ m) : (padPoly h).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le ?_
  intro j _
  have hpad : (padMv h j).totalDegree ≤ 1 := by
    simp only [padMv]; split_ifs with hj
    · rw [totalDegree_X]
    · simp
  have hterm : (X (Sum.inl (Fin.natAdd n j)) - padMv h j).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_X]; exact max_le le_rfl hpad
  calc ((X (Sum.inl (Fin.natAdd n j)) - padMv h j) ^ 2).totalDegree
      ≤ 2 * (X (Sum.inl (Fin.natAdd n j)) - padMv h j).totalDegree := totalDegree_pow _ _
    _ ≤ 2 := by omega

/-- Evaluation of `padPoly` at a vector `w` (with the unique empty witness): the sum of squares
`Σ_j (w (natAdd n j) − pad h (input part of w) j)²`. -/
theorem padPoly_eval {n m : ℕ} (h : n ≤ m) (w : Fin (n + m) → ℤ) (y : Fin 0 → ℤ) :
    evalAtZZ (padPoly h) w y
      = ∑ j : Fin m, (w (Fin.natAdd n j) - pad h (fun i => w (Fin.castAdd m i)) j) ^ 2 := by
  simp only [evalAtZZ, padPoly, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have e1 : eval (Sum.elim w y) (X (Sum.inl (Fin.natAdd n j)) : Poly (n + m) 0)
      = w (Fin.natAdd n j) := by rw [eval_X]; rfl
  have e2 : eval (Sum.elim w y) (padMv h j) = pad h (fun i => w (Fin.castAdd m i)) j := by
    simp only [padMv, pad]
    split_ifs with hj
    · rw [eval_X]; rfl
    · rw [map_zero]
  rw [map_pow, map_sub, e1, e2]

/-- **C4-4 baseline bridge.** For `n ≤ m` the zero-padding `pad h` is single-quadratic-definable
over ℤ, witnessed by the degree-2 polynomial `padPoly h` with no witnesses (`r = 0`). -/
theorem pad_singleQuadratic {n m : ℕ} (h : n ≤ m) :
    SingleQuadraticDefinableFunctionZZ (pad h) := by
  refine ⟨0, padPoly h, padPoly_totalDegree_le h, ?_⟩
  intro w
  simp only [graphVecZZ, Set.mem_setOf_eq]
  constructor
  · intro hw
    refine ⟨0, ?_⟩
    rw [padPoly_eval]
    exact (padRel_iff h (fun i => w (Fin.castAdd m i)) (fun j => w (Fin.natAdd n j))).mpr hw
  · rintro ⟨y, hy⟩
    rw [padPoly_eval] at hy
    exact (padRel_iff h (fun i => w (Fin.castAdd m i)) (fun j => w (Fin.natAdd n j))).mp hy

/-! ## Part 4 — QuadForm ↔ MvPolynomial

`QuadForm.toMv q : MvPolynomial (Fin n) ℚ` realises `q.eval` as an honest polynomial of total
degree ≤ 2. -/

namespace QuadForm

/-- The MvPolynomial `c + Σᵢ lᵢ Xᵢ + Σᵢⱼ Qᵢⱼ Xᵢ Xⱼ` realising a `QuadForm`. -/
noncomputable def toMv {n : ℕ} (q : QuadForm n) : MvPolynomial (Fin n) ℚ :=
  C q.c + ∑ i, C (q.l i) * X i + ∑ i, ∑ j, C (q.Q i j) * X i * X j

/-- `toMv` evaluates to the `QuadForm`. -/
theorem eval_toMv {n : ℕ} (q : QuadForm n) (x : Fin n → ℚ) :
    MvPolynomial.eval x q.toMv = q.eval x := by
  simp only [toMv, QuadForm.eval, map_add, map_sum, map_mul, eval_C, eval_X]
  simp only [dotProduct, mulVec]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `toMv` has total degree ≤ 2. -/
theorem toMv_totalDegree_le {n : ℕ} (q : QuadForm n) : q.toMv.totalDegree ≤ 2 := by
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_C]; omega
    · refine totalDegree_finsetSum_le ?_
      intro i _
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]; omega
  · refine totalDegree_finsetSum_le ?_
    intro i _
    refine totalDegree_finsetSum_le ?_
    intro j _
    have h1 : (C (q.Q i j) * X i : MvPolynomial (Fin n) ℚ).totalDegree ≤ 1 := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]
    have h2 : (X j : MvPolynomial (Fin n) ℚ).totalDegree = 1 := totalDegree_X j
    refine (totalDegree_mul _ _).trans ?_
    rw [h2]; omega

/-- The requested specialisation: `eval (castQ t) q.toMv = q.eval (castQ t)`. -/
theorem eval_castQ_toMv {n : ℕ} (q : QuadForm n) (t : Fin n → ℤ) :
    MvPolynomial.eval (castQ t) q.toMv = q.eval (castQ t) := eval_toMv q (castQ t)

/-! ### Converse `ofMv` for `n = 1` and `n = 2` (honestly labelled: only these two arities).

The general converse (`p.totalDegree ≤ 2 → ∃ q, ∀ t, eval t p = q.eval t`) requires classifying
every monomial of degree ≤ 2; here it is delivered for `n = 1` and `n = 2` by extracting the
coefficients `constant / Xᵢ / Xᵢ²` (and `Xᵢ Xⱼ` for `n = 2`) explicitly. -/

/-- A `Fin 1 →₀ ℕ` finsupp is `single 0 (d 0)`. -/
private theorem finsupp_one_eq (d : Fin 1 →₀ ℕ) : d = Finsupp.single 0 (d 0) := by
  refine Finsupp.ext (fun i => ?_); fin_cases i; simp

/-- Its degree functional is `d 0`. -/
private theorem finsupp_one_deg (d : Fin 1 →₀ ℕ) : (d.sum fun _ e => e) = d 0 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; simp

/-- **ofMv, `n = 1`.** Every degree-≤2 polynomial in one variable is a `QuadForm`. -/
theorem ofMv_one (p : MvPolynomial (Fin 1) ℚ) (hp : p.totalDegree ≤ 2) :
    ∃ q : QuadForm 1, ∀ t : Fin 1 → ℚ, MvPolynomial.eval t p = q.eval t := by
  classical
  refine ⟨⟨coeff 0 p, fun _ => coeff (Finsupp.single 0 1) p,
          fun _ _ => coeff (Finsupp.single 0 2) p⟩, fun t => ?_⟩
  have hsub : p.support ⊆
      ({0, Finsupp.single 0 1, Finsupp.single 0 2} : Finset (Fin 1 →₀ ℕ)) := by
    intro d hd
    have hd0 : d 0 ≤ 2 := by
      have h := le_totalDegree hd; rw [finsupp_one_deg] at h; omega
    rw [finsupp_one_eq d]
    interval_cases hval : (d 0) <;>
      simp [Finset.mem_insert, Finset.mem_singleton, Finsupp.single_zero]
  rw [eval_eq']
  simp only [Fin.prod_univ_one]
  rw [Finset.sum_subset hsub (by
    intro d _ hdnot
    rw [MvPolynomial.notMem_support_iff.mp hdnot, zero_mul])]
  have h01 : (Finsupp.single (0 : Fin 1) 1) ≠ Finsupp.single 0 2 := by
    intro h; have := congrFun (congrArg (DFunLike.coe) h) 0; simp at this
  have h0 : (0 : Fin 1 →₀ ℕ) ∉ ({Finsupp.single 0 1, Finsupp.single 0 2} : Finset (Fin 1 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h) <;>
      · have := congrFun (congrArg (DFunLike.coe) h) 0; simp at this
  rw [Finset.sum_insert h0,
    Finset.sum_insert (by rw [Finset.mem_singleton]; exact h01), Finset.sum_singleton]
  simp only [QuadForm.eval, dotProduct, mulVec, Fin.sum_univ_one, Finsupp.coe_zero,
    Pi.zero_apply, Finsupp.single_eq_same]
  ring

/-- A `Fin 2 →₀ ℕ` finsupp is `single 0 (d 0) + single 1 (d 1)`. -/
private theorem finsupp_two_eq (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  refine Finsupp.ext (fun i => ?_); fin_cases i <;> simp

/-- Its degree functional is `d 0 + d 1`. -/
private theorem finsupp_two_deg (d : Fin 2 →₀ ℕ) : (d.sum fun _ e => e) = d 0 + d 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; simp [Fin.sum_univ_two]

/-- Coordinate-evaluation contradiction helper for finsupp inequalities. -/
private theorem finsupp_two_ne {a b : Fin 2 →₀ ℕ} (i : Fin 2) (h : a i ≠ b i) : a ≠ b :=
  fun he => h (by rw [he])

/-- **ofMv, `n = 2`.** Every degree-≤2 polynomial in two variables is a `QuadForm`. -/
theorem ofMv_two (p : MvPolynomial (Fin 2) ℚ) (hp : p.totalDegree ≤ 2) :
    ∃ q : QuadForm 2, ∀ t : Fin 2 → ℚ, MvPolynomial.eval t p = q.eval t := by
  classical
  refine ⟨⟨coeff 0 p,
          ![coeff (Finsupp.single 0 1) p, coeff (Finsupp.single 1 1) p],
          !![coeff (Finsupp.single 0 2) p, coeff (Finsupp.single 0 1 + Finsupp.single 1 1) p;
             0, coeff (Finsupp.single 1 2) p]⟩, fun t => ?_⟩
  have hsub : p.support ⊆
      ({0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2, Finsupp.single 1 2,
        Finsupp.single 0 1 + Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    intro d hd
    have hsum : d 0 + d 1 ≤ 2 := by
      have h := le_totalDegree hd; rw [finsupp_two_deg] at h; omega
    rw [finsupp_two_eq d]
    set a := d 0 with ha
    set b := d 1 with hb
    have hb0 : a ≤ 2 := by omega
    have hb1 : b ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;>
      simp_all [Finset.mem_insert, Finset.mem_singleton, Finsupp.single_zero]
  rw [eval_eq']
  simp only [Fin.prod_univ_two]
  rw [Finset.sum_subset hsub (by
    intro d _ hdnot
    rw [MvPolynomial.notMem_support_iff.mp hdnot, zero_mul])]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h | h | h)
        · exact finsupp_two_ne 0 (by simp) h
        · exact finsupp_two_ne 1 (by simp) h
        · exact finsupp_two_ne 0 (by simp) h
        · exact finsupp_two_ne 1 (by simp) h
        · exact finsupp_two_ne 0 (by simp) h),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h | h)
        · exact finsupp_two_ne 0 (by simp) h
        · exact finsupp_two_ne 0 (by simp) h
        · exact finsupp_two_ne 1 (by simp) h
        · exact finsupp_two_ne 1 (by simp) h),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact finsupp_two_ne 0 (by simp) h
        · exact finsupp_two_ne 1 (by simp) h
        · exact finsupp_two_ne 0 (by simp) h),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact finsupp_two_ne 0 (by simp) h
        · exact finsupp_two_ne 0 (by simp) h),
      Finset.sum_insert (by
        rw [Finset.mem_singleton]
        exact finsupp_two_ne 1 (by simp)),
      Finset.sum_singleton]
  simp only [QuadForm.eval, dotProduct, mulVec, Fin.sum_univ_two, Finsupp.coe_zero, Pi.zero_apply,
    Finsupp.single_eq_same, Finsupp.coe_add, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  norm_num
  ring

end QuadForm

end DiophCompression.ResearchUpgrade
