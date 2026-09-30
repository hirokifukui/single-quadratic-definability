/-
  SmallLeaves.lean — Gate-18 research program, small-leaf packet `small_leaves`.
  A3-3 (three SEPARATE reflection/projection APIs for the fixed-base prime ray), A4-2 strong form
  (a √X lower bound for the polynomial-progression fibre count), C4-1 / C4-2 (closure of the coset
  normal forms under affine input substitution and coordinatewise refinement) and C4-4 lower half
  (the padding relation Σ(yᵢ−xᵢ)² + Σyⱼ² = 0 is total, functional and injective).
  Baseline (mpup-lean r39) is read-only; nothing here is imported by the baseline. No sorry, no axiom.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.CertificateEnvelope
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.DimensionFromCoset

namespace DiophCompression.ResearchUpgrade

open Matrix MPUP

/-! ## A3-3(a) : witness reflection for the moving relation and the negative-slope ray transport

The ℤ-output set of the moving relation is invariant under `(b, μ) ↦ (−b, −μ)`; the witness identity
is the baseline `movingModulus_negSlope_witnessEquiv` (`fqSG` invariant under `(b,μ,w) ↦ (−b,−μ,−w)`),
here specialised to the divisibility form via `neg_dvd`. -/

/-- A3-3(a). The moving ℤ-output set is unchanged by the sign flip `(b, μ) ↦ (−b, −μ)`. -/
theorem movingOutputSet_negSlope {k : ℕ} (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    movingOutputSet A B C b l m μ q = movingOutputSet A B C (-b) l m (-μ) q := by
  ext c
  simp only [movingOutputSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rwa [show (-b) * c + (-μ) = -(b * c + μ) by ring, neg_dvd]⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [show (-b) * c + (-μ) = -(b * c + μ) by ring, neg_dvd] at hu
    exact hu

/-- A3-3(a). Transport a fixed-base prime ray along the sign flip. -/
def FixedBasePrimeRay.negSlope {k : ℕ} (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ)
    (R : FixedBasePrimeRay (movingOutputSet A B C b l m μ q)) :
    FixedBasePrimeRay (movingOutputSet A B C (-b) l m (-μ) q) :=
  movingOutputSet_negSlope A B C b l m μ q ▸ R

/-! ## A3-3(b) : outer output negation

`negOutput` pushes a ray through `c ↦ −c` into `negSet S`; it is `mapMul` with `ε = −1`.
The exponential-injection analogue is the already-existing `exponentialInjection_neg` (Counting.lean),
reused rather than duplicated. -/

/-- A3-3(b). Negate the outputs of a ray. -/
def FixedBasePrimeRay.negOutput {S : Set ℤ} (R : FixedBasePrimeRay S) :
    FixedBasePrimeRay (negSet S) :=
  R.mapMul (-1) (by norm_num) (fun c hc => by
    simp only [negSet, Set.mem_setOf_eq]
    simpa using hc)

/-! ## A3-3(c) : polynomial-level bridge

`ofSubset` is `mono` under the reviewer's name; a ray inside `S ⊆ fiberZZ P a` is a ray in the whole
scalar fibre. -/

/-- A3-3(c). A ray inside `S` is a ray inside any `T ⊇ S` (alias of `mono`). -/
def FixedBasePrimeRay.ofSubset {S T : Set ℤ} (R : FixedBasePrimeRay S) (h : S ⊆ T) :
    FixedBasePrimeRay T := R.mono h

/-- A3-3(c). A ray inside `S ⊆ fiberZZ P a` is a ray inside the scalar fibre `fiberZZ P a`. -/
def FixedBasePrimeRay.toFiberZZ {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ} {S : Set ℤ}
    (R : FixedBasePrimeRay S) (h : S ⊆ fiberZZ P a) : FixedBasePrimeRay (fiberZZ P a) :=
  R.ofSubset h

/-! ## A4-2 strong form : a `√X` lower bound for the polynomial-progression fibre count -/

/-- Finset envelope: an injective sequence in `S` with `|g j| ≤ X` for `j ≤ n` gives `N_S(X) ≥ n+1`.
(Polynomial-envelope analogue of `fiberCountZZ_ge_of_injection`.) -/
theorem fiberCountZZ_ge_of_polyEnvelope (S : Set ℤ) (g : ℕ → ℤ)
    (hinj : Function.Injective g) (hmem : ∀ j, g j ∈ S) (X n : ℕ)
    (hbd : ∀ j, j ≤ n → |g j| ≤ (X : ℤ)) :
    n + 1 ≤ fiberCountZZ S X := by
  classical
  unfold fiberCountZZ
  have hsub : (Finset.range (n + 1)).image g ⊆
      (Finset.Icc (-(X : ℤ)) (X : ℤ)).filter (fun c => c ∈ S) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨abs_le.mp (hbd j (by omega)), hmem j⟩
  calc n + 1 = ((Finset.range (n + 1)).image g).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-- A4-2 strong form. For a polynomial-progression realization with a nonconstant quadratic (degree
`≤ 2`) output polynomial there are `κ > 0` and an explicit `X₀` with `κ·√X ≤ N_{fiberZZ P a}(X)` for
`X ≥ X₀`. Explicit constants: `κ = 1/(2√K)`, `X₀ = 4·K·(t₀+1)²`, where
`K = |q₀| + |q₁| + |q₂| ≥ 1`. -/
theorem sqrtLowerBound_of_polynomialProgression {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PolynomialProgressionRealization P a) :
    ∃ (κ : ℝ) (X₀ : ℕ), 0 < κ ∧ ∀ X : ℕ, X₀ ≤ X →
      κ * Real.sqrt X ≤ (fiberCountZZ (fiberZZ P a) X : ℝ) := by
  classical
  -- the height coefficient `Kz = |q₀|+|q₁|+|q₂|`, shown ≥ 1 (nonconstant ⇒ leading coeff ≠ 0)
  have hq0 : c.q ≠ 0 := by
    intro hz; have h := c.nonconst; rw [hz, Polynomial.natDegree_zero] at h; exact absurd h (lt_irrefl 0)
  have hlc : c.q.coeff c.q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hKz0 : (0 : ℤ) ≤ |c.q.coeff 0| + |c.q.coeff 1| + |c.q.coeff 2| := by positivity
  have hKz1 : (1 : ℤ) ≤ |c.q.coeff 0| + |c.q.coeff 1| + |c.q.coeff 2| := by
    have hd := c.deg_le_two; have hp := c.nonconst
    rcases (by omega : c.q.natDegree = 1 ∨ c.q.natDegree = 2) with h1 | h2
    · rw [h1] at hlc
      have hone := Int.one_le_abs hlc
      have := abs_nonneg (c.q.coeff 0); have := abs_nonneg (c.q.coeff 2)
      linarith
    · rw [h2] at hlc
      have hone := Int.one_le_abs hlc
      have := abs_nonneg (c.q.coeff 0); have := abs_nonneg (c.q.coeff 1)
      linarith
  set Kz : ℤ := |c.q.coeff 0| + |c.q.coeff 1| + |c.q.coeff 2| with hKzdef
  set Kn : ℕ := Kz.toNat with hKndef
  have hKzn : (Kn : ℤ) = Kz := Int.toNat_of_nonneg hKz0
  have hKn1 : 1 ≤ Kn := by
    have : (1 : ℤ) ≤ (Kn : ℤ) := by rw [hKzn]; exact hKz1
    exact_mod_cast this
  have hKnR : (0 : ℝ) < (Kn : ℝ) := by exact_mod_cast hKn1
  have hrKpos : (0 : ℝ) < Real.sqrt (Kn : ℝ) := Real.sqrt_pos.mpr hKnR
  refine ⟨1 / (2 * Real.sqrt (Kn : ℝ)), 4 * Kn * (c.t₀ + 1) ^ 2, div_pos one_pos (by linarith), ?_⟩
  intro X hX
  -- the `√X`-many tail points that fit in the box; count via `m = ⌊√(X/K)⌋`
  set m : ℕ := Nat.sqrt (X / Kn) with hmdef
  have hmm : m ^ 2 ≤ X / Kn := by rw [hmdef]; exact Nat.sqrt_le' _
  have hN1 : Kn * m ^ 2 ≤ X := by
    calc Kn * m ^ 2 ≤ Kn * (X / Kn) := by gcongr
      _ = X / Kn * Kn := Nat.mul_comm _ _
      _ ≤ X := Nat.div_mul_le_self X Kn
  have hlt : X / Kn < (m + 1) ^ 2 := by rw [hmdef]; exact Nat.lt_succ_sqrt' _
  have hXlt : X < Kn * (m + 1) ^ 2 := by
    have hmod : X % Kn < Kn := Nat.mod_lt X (by omega)
    have hdm : Kn * (X / Kn) + X % Kn = X := Nat.div_add_mod X Kn
    calc X = Kn * (X / Kn) + X % Kn := hdm.symm
      _ < Kn * (X / Kn) + Kn := by omega
      _ = Kn * (X / Kn + 1) := by ring
      _ ≤ Kn * (m + 1) ^ 2 := Nat.mul_le_mul (le_refl Kn) hlt
  have hmt : c.t₀ + 1 ≤ m := by
    have h1 : Kn * (4 * (c.t₀ + 1) ^ 2) < Kn * (m + 1) ^ 2 := by
      have he : Kn * (4 * (c.t₀ + 1) ^ 2) = 4 * Kn * (c.t₀ + 1) ^ 2 := by ring
      omega
    have h2 : 4 * (c.t₀ + 1) ^ 2 < (m + 1) ^ 2 := Nat.lt_of_mul_lt_mul_left h1
    have h3 : 2 * (c.t₀ + 1) < m + 1 := by
      by_contra hc
      push_neg at hc
      have hpow : (m + 1) ^ 2 ≤ (2 * (c.t₀ + 1)) ^ 2 := Nat.pow_le_pow_left hc 2
      nlinarith [h2, hpow]
    omega
  set nn : ℕ := m - c.t₀ - 1 with hnndef
  have hn_eq : c.t₀ + nn + 1 = m := by omega
  -- the injective tail sequence and its envelope
  set g : ℕ → ℤ := fun j => c.q.eval ((c.t₀ + j : ℕ) : ℤ) with hg
  have hinj : Function.Injective g := by
    intro j j' hjj
    simp only [hg] at hjj
    have := c.injective (c.t₀ + j) (c.t₀ + j') (Nat.le_add_right _ _) (Nat.le_add_right _ _) hjj
    omega
  have hmem : ∀ j, g j ∈ fiberZZ P a := by
    intro j
    exact ⟨c.witness (c.t₀ + j), by simpa [hg] using c.mem (c.t₀ + j) (Nat.le_add_right _ _)⟩
  have hbd : ∀ j, j ≤ nn → |g j| ≤ (X : ℤ) := by
    intro j hj
    have he := abs_eval_le_of_natDegree_le_two c.q c.deg_le_two ((c.t₀ + j : ℕ) : ℤ)
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((c.t₀ + j : ℕ) : ℤ))] at he
    have hjm : ((c.t₀ + j : ℕ) : ℤ) + 1 ≤ (m : ℤ) := by
      have hnat : c.t₀ + j + 1 ≤ m := by omega
      calc ((c.t₀ + j : ℕ) : ℤ) + 1 = ((c.t₀ + j + 1 : ℕ) : ℤ) := by push_cast; ring
        _ ≤ (m : ℤ) := by exact_mod_cast hnat
    have hsq : (((c.t₀ + j : ℕ) : ℤ) + 1) ^ 2 ≤ (m : ℤ) ^ 2 := by
      have h0 : (0 : ℤ) ≤ ((c.t₀ + j : ℕ) : ℤ) + 1 := by positivity
      nlinarith [hjm, h0]
    calc |g j| = |c.q.eval ((c.t₀ + j : ℕ) : ℤ)| := by simp only [hg]
      _ ≤ Kz * (((c.t₀ + j : ℕ) : ℤ) + 1) ^ 2 := he
      _ ≤ Kz * (m : ℤ) ^ 2 := mul_le_mul_of_nonneg_left hsq hKz0
      _ = (Kn : ℤ) * (m : ℤ) ^ 2 := by rw [hKzn]
      _ = ((Kn * m ^ 2 : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (X : ℤ) := by exact_mod_cast hN1
  have hcount : nn + 1 ≤ fiberCountZZ (fiberZZ P a) X :=
    fiberCountZZ_ge_of_polyEnvelope (fiberZZ P a) g hinj hmem X nn hbd
  -- pass to ℝ : `κ·√X ≤ m − t₀ ≤ N(X)`
  set s : ℝ := Real.sqrt (X : ℝ) with hsdef
  set rK : ℝ := Real.sqrt (Kn : ℝ) with hrKdef
  have hs_nonneg : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = (X : ℝ) := Real.sq_sqrt (by positivity)
  have hrK_sq : rK ^ 2 = (Kn : ℝ) := Real.sq_sqrt (by positivity)
  have hrK_pos : (0 : ℝ) < rK := hrKpos
  have hsq2 : s ^ 2 < (rK * ((m : ℝ) + 1)) ^ 2 := by
    rw [hs_sq]
    have hcast : (rK * ((m : ℝ) + 1)) ^ 2 = (Kn : ℝ) * ((m : ℝ) + 1) ^ 2 := by rw [mul_pow, hrK_sq]
    rw [hcast]
    have hc2 : (Kn : ℝ) * ((m : ℝ) + 1) ^ 2 = ((Kn * (m + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hc2]; exact_mod_cast hXlt
  have hslt : s < rK * ((m : ℝ) + 1) := by
    have h0 : (0 : ℝ) ≤ rK * ((m : ℝ) + 1) := by positivity
    nlinarith [hsq2, h0, hs_nonneg]
  have hM' : s < rK * (m : ℝ) + rK := by nlinarith [hslt]
  have hs_bound : 2 * rK * ((c.t₀ : ℝ) + 1) ≤ s := by
    have hb0 : (0 : ℝ) ≤ 2 * rK * ((c.t₀ : ℝ) + 1) := by positivity
    have hbsq : (2 * rK * ((c.t₀ : ℝ) + 1)) ^ 2 ≤ (X : ℝ) := by
      have he : (2 * rK * ((c.t₀ : ℝ) + 1)) ^ 2 = 4 * (rK ^ 2) * ((c.t₀ : ℝ) + 1) ^ 2 := by ring
      rw [he, hrK_sq]
      have hc3 : 4 * (Kn : ℝ) * ((c.t₀ : ℝ) + 1) ^ 2 = ((4 * Kn * (c.t₀ + 1) ^ 2 : ℕ) : ℝ) := by
        push_cast; ring
      rw [hc3]; exact_mod_cast hX
    nlinarith [hbsq, hb0, hs_nonneg, hs_sq]
  have key : s ≤ 2 * rK * (m : ℝ) - 2 * rK * (c.t₀ : ℝ) := by nlinarith [hM', hs_bound]
  have hcast_sub : ((m - c.t₀ : ℕ) : ℝ) = (m : ℝ) - (c.t₀ : ℝ) := by
    rw [Nat.cast_sub (by omega : c.t₀ ≤ m)]
  have goal2 : 1 / (2 * rK) * s ≤ (m : ℝ) - (c.t₀ : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * rK)]
    nlinarith [key]
  have hcount' : ((m - c.t₀ : ℕ) : ℝ) ≤ (fiberCountZZ (fiberZZ P a) X : ℝ) := by
    have hnc : nn + 1 = m - c.t₀ := by omega
    rw [← hnc]; exact_mod_cast hcount
  calc 1 / (2 * rK) * s ≤ (m : ℝ) - (c.t₀ : ℝ) := goal2
    _ = ((m - c.t₀ : ℕ) : ℝ) := hcast_sub.symm
    _ ≤ (fiberCountZZ (fiberZZ P a) X : ℝ) := hcount'

/-! ## C4-1 / C4-2 : quadratic-form substitution algebra

A degree-≤2 form composed with an affine substitution `v ↦ a + c • v` is again a degree-≤2 form.
We build the substituted form explicitly (`scale`, `translate`, `compAffine`) with the evaluation
identities; these drive the closure lemmas below. -/

namespace QuadForm

/-- Scale the argument by `c`: `q.eval (c • v) = (q.scale c).eval v`. -/
def scale {n : ℕ} (q : QuadForm n) (c : ℚ) : QuadForm n := ⟨q.c, c • q.l, c ^ 2 • q.Q⟩

theorem eval_scale {n : ℕ} (q : QuadForm n) (c : ℚ) (v : Fin n → ℚ) :
    q.eval (c • v) = (q.scale c).eval v := by
  simp only [QuadForm.eval, scale, dotProduct_smul, smul_dotProduct, mulVec_smul, smul_mulVec,
    smul_eq_mul, smul_smul]
  ring

/-- Translate the argument by `a`: `q.eval (a + w) = (q.translate a).eval w`. -/
def translate {n : ℕ} (q : QuadForm n) (a : Fin n → ℚ) : QuadForm n :=
  ⟨q.c + q.l ⬝ᵥ a + a ⬝ᵥ (q.Q *ᵥ a), q.l + a ᵥ* q.Q + q.Q *ᵥ a, q.Q⟩

theorem eval_translate {n : ℕ} (q : QuadForm n) (a w : Fin n → ℚ) :
    q.eval (a + w) = (q.translate a).eval w := by
  simp only [QuadForm.eval, translate, mulVec_add, dotProduct_add, add_dotProduct]
  rw [Matrix.dotProduct_mulVec a q.Q w, dotProduct_comm w (q.Q *ᵥ a)]
  ring

/-- Affine substitution `v ↦ a + c • v`. -/
def compAffine {n : ℕ} (q : QuadForm n) (a : Fin n → ℚ) (c : ℚ) : QuadForm n :=
  (q.translate a).scale c

theorem eval_compAffine {n : ℕ} (q : QuadForm n) (a : Fin n → ℚ) (c : ℚ) (v : Fin n → ℚ) :
    (q.compAffine a c).eval v = q.eval (a + c • v) := by
  rw [compAffine, ← eval_scale, ← eval_translate]

end QuadForm

/-- `castQ` commutes with addition. -/
theorem castQ_add {n : ℕ} (u v : Fin n → ℤ) : castQ (u + v) = castQ u + castQ v := by
  funext i; simp only [castQ, Pi.add_apply]; push_cast; ring

/-- `castQ` commutes with integer scaling. -/
theorem castQ_smul {n : ℕ} (N : ℤ) (t : Fin n → ℤ) : castQ (N • t) = (N : ℚ) • castQ t := by
  funext i; simp only [castQ, Pi.smul_apply, smul_eq_mul]; push_cast; ring

/-! ### C4-1(i) : closure under affine input substitution -/

/-- C4-1(i), full form. If `f` has a full-residue normal form, so does `x ↦ f (ρ' + N • x)`
(same modulus; the coset polynomial is `q.scale N`). -/
theorem FullCosetNF.comp_affine {n : ℕ} {f : (Fin n → ℤ) → ℤ} (h : FullCosetNF f)
    (ρ' : Fin n → ℤ) (N : ℕ) (hN : 1 ≤ N) :
    FullCosetNF (fun x => f (ρ' + (N : ℤ) • x)) := by
  obtain ⟨M, hM, hf⟩ := h
  refine ⟨M, hM, fun σ => ?_⟩
  obtain ⟨q, hq⟩ := hf (ρ' + (N : ℤ) • σ)
  refine ⟨q.scale ((N : ℤ) : ℚ), fun t => ?_⟩
  show ((f (ρ' + (N : ℤ) • (σ + (M : ℤ) • t)) : ℤ) : ℚ) = _
  have harg : ρ' + (N : ℤ) • (σ + (M : ℤ) • t) = (ρ' + (N : ℤ) • σ) + (M : ℤ) • ((N : ℤ) • t) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [harg, hq ((N : ℤ) • t), castQ_smul, QuadForm.eval_scale]

/-- C4-1(i), weak form under the coset-meeting hypothesis `∃ s, ρ + M • s = ρ'`. If `f` is a weak
scalar coset form with data `(M, ρ, q)` on the coset that contains `ρ'`, then `x ↦ f (ρ' + N • x)` is
a weak scalar coset form (modulus `M`; the coset polynomial is `q.compAffine (castQ s) N`). -/
theorem WeakScalarCosetNF.comp_affine_of_mem {n : ℕ} {f : (Fin n → ℤ) → ℤ}
    {M : ℕ} {ρ : Fin n → ℤ} {q : QuadForm n} (hM : 1 ≤ M)
    (hf : ∀ t : Fin n → ℤ, (f (ρ + (M : ℤ) • t) : ℚ) = q.eval (castQ t))
    (ρ' : Fin n → ℤ) (N : ℕ) (hN : 1 ≤ N) (s : Fin n → ℤ)
    (hs : ρ + (M : ℤ) • s = ρ') :
    WeakScalarCosetNF (fun x => f (ρ' + (N : ℤ) • x)) := by
  refine ⟨M, 0, q.compAffine (castQ s) ((N : ℤ) : ℚ), hM, fun t => ?_⟩
  show ((f (ρ' + (N : ℤ) • ((0 : Fin n → ℤ) + (M : ℤ) • t)) : ℤ) : ℚ) = _
  have harg : ρ' + (N : ℤ) • ((0 : Fin n → ℤ) + (M : ℤ) • t)
      = ρ + (M : ℤ) • (s + (N : ℤ) • t) := by
    rw [← hs]; funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]; ring
  rw [harg, hf (s + (N : ℤ) • t), castQ_add, castQ_smul, QuadForm.eval_compAffine]

/-! ### C4-1(ii) : closure under output-coordinate projection -/

/-- C4-1(ii). A weak vector coset form projects to a weak scalar coset form in each output slot. -/
theorem WeakScalarCosetNF.proj {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : WeakVectorCosetNF f) (j : Fin m) :
    WeakScalarCosetNF (fun x => f x j) := by
  obtain ⟨M, ρ, q, hM, hq⟩ := h
  exact ⟨M, ρ, q j, hM, fun t => hq t j⟩

/-! ### C4-2 : nested-refinement template (m = 2) -/

/-- C4-2 (template, `m = 2`). If `g₀` is a weak scalar coset form with data `(M₀, ρ₀, q₀)` and the
`(ρ₀, M₀)`-restriction of `g₁` is a weak scalar coset form with data `(M₁, σ₁, q₁)`, then the pair
`x ↦ (g₀ x, g₁ x)` is a weak vector coset form. Common coset: `ρ₀ + M₀ • σ₁`, modulus `M₀·M₁`;
first slot uses `q₀.compAffine (castQ σ₁) M₁`, second uses `q₁` (via `ρ + M(σ + N t) = (ρ+Mσ)+MN t`). -/
theorem weakVectorCosetNF_of_nested {n : ℕ} (g₀ g₁ : (Fin n → ℤ) → ℤ)
    {M₀ : ℕ} {ρ₀ : Fin n → ℤ} {q₀ : QuadForm n} (hM₀ : 1 ≤ M₀)
    (h₀ : ∀ t : Fin n → ℤ, (g₀ (ρ₀ + (M₀ : ℤ) • t) : ℚ) = q₀.eval (castQ t))
    {M₁ : ℕ} {σ₁ : Fin n → ℤ} {q₁ : QuadForm n} (hM₁ : 1 ≤ M₁)
    (h₁ : ∀ t : Fin n → ℤ,
      (g₁ (ρ₀ + (M₀ : ℤ) • (σ₁ + (M₁ : ℤ) • t)) : ℚ) = q₁.eval (castQ t)) :
    WeakVectorCosetNF (fun x => (![g₀ x, g₁ x] : Fin 2 → ℤ)) := by
  refine ⟨M₀ * M₁, ρ₀ + (M₀ : ℤ) • σ₁,
    ![q₀.compAffine (castQ σ₁) ((M₁ : ℤ) : ℚ), q₁],
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), fun t j => ?_⟩
  have harg : (ρ₀ + (M₀ : ℤ) • σ₁) + ((M₀ * M₁ : ℕ) : ℤ) • t
      = ρ₀ + (M₀ : ℤ) • (σ₁ + (M₁ : ℤ) • t) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  fin_cases j
  · simp only [Fin.mk_zero, Matrix.cons_val_zero]
    rw [harg, h₀ (σ₁ + (M₁ : ℤ) • t), castQ_add, castQ_smul, QuadForm.eval_compAffine]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      Matrix.cons_val_fin_one]
    rw [harg, h₁ t]

/-! ## C4-4 lower half : the padding relation Σ(yᵢ−xᵢ)² + Σyⱼ² = 0

For `n ≤ m` the zero-padding `x ↦ (x, 0)` is the unique output of the degree-2 relation. -/

/-- Zero-padding `(Fin n → ℤ) → (Fin m → ℤ)` (`Fin.castLE` on the first `n`, `0` on the rest). -/
def pad {n m : ℕ} (h : n ≤ m) (x : Fin n → ℤ) : Fin m → ℤ :=
  fun j => if hj : (j : ℕ) < n then x ⟨j, hj⟩ else 0

/-- The degree-2 relation `Σⱼ (yⱼ − (pad x)ⱼ)² = 0` (= `Σ_{i<n}(yᵢ−xᵢ)² + Σ_{n≤j<m} yⱼ²`). -/
def padRel {n m : ℕ} (h : n ≤ m) : (Fin n → ℤ) → (Fin m → ℤ) → Prop :=
  fun x y => ∑ j : Fin m, (y j - pad h x j) ^ 2 = 0

/-- A sum of squares over ℤ vanishes iff `y = pad x`. -/
theorem padRel_iff {n m : ℕ} (h : n ≤ m) (x : Fin n → ℤ) (y : Fin m → ℤ) :
    padRel h x y ↔ y = pad h x := by
  unfold padRel
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  constructor
  · intro hj; funext j
    have h2 : y j - pad h x j = 0 := by
      have := hj j (Finset.mem_univ j)
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this
    linarith
  · intro hxy j _; rw [hxy]; ring

/-- C4-4 lower half. The padding relation is total, functional, and its unique output is `pad x`. -/
theorem padRel_spec {n m : ℕ} (h : n ≤ m) :
    RelTotal (padRel h) ∧ RelUnique (padRel h) ∧
      (∀ x y, padRel h x y ↔ y = pad h x) := by
  refine ⟨fun x => ⟨pad h x, (padRel_iff h x (pad h x)).mpr rfl⟩, ?_, padRel_iff h⟩
  intro x y y' hy hy'
  rw [(padRel_iff h x y).mp hy, (padRel_iff h x y').mp hy']

/-- C4-4 lower half. The zero-padding is injective. -/
theorem pad_injective {n m : ℕ} (h : n ≤ m) : Function.Injective (pad h) := by
  intro x x' hxx
  funext i
  have hi := congrFun hxx (Fin.castLE h i)
  simp only [pad, Fin.val_castLE] at hi
  rw [dif_pos i.isLt, dif_pos i.isLt] at hi
  simpa using hi

end DiophCompression.ResearchUpgrade
