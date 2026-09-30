/-
  DefiniteBinary.lean — s54.  R42-D1..D3: the positive definite targets with two output/witness
  coordinates, and the low-rank semidefinite weak normal form.

  * `binary_compiler_gen` (any `QuadraticGraphData n m r` with `OutWit m r ≃ Fin 2`, positive
    definite): an affine rational centre, the residual as an explicit `QuadForm` in the input
    (`residualForm`), and `Q(w) = α((w₁ + βw₂)² + Δw₂²)` with `α, Δ > 0`.
    `definite_binary_compiler` is the `(n, 1, 1)` instance (R42-D1).
  * `weakVectorCosetNF_of_binary` (R42-D2 core): either the residual vanishes on the lattice (then
    every solution is the centre and `f` is affine, `M = 1`), or at a base input `a₀` with an
    integer solution `z₀` the representation `(r₀, s₀)` of `R(a₀)/α` READ OFF `z₀` is fed to
    `NormLift.norm_section`; the resulting affine section passes through `z₀` exactly, a common
    denominator `M` makes it integral on `a₀ + Mℤⁿ`, and output-uniqueness identifies it with `f`.
  * `definiteWeakNF_oneOut_oneWit_holds` — the Prop recorded OPEN in `DefiniteReduction.lean`
    (s53) — is now PROVED for every `n`.  `definiteWeakNF_twoOut_zeroWit_holds` likewise.
  * `lowRankSemidefiniteWeakNF_holds` (R42-D3): semidefinite of either sign, `Q ≠ 0`, polar rank
    ≤ 2 ⇒ weak vector coset NF (sign flip via `negGraph`, whose polar rank is unchanged; exact
    witness compiler; then the binary engine, or `fullVectorCosetNF_of_defines` when d = 1).

  Not claimed: the general `DefiniteWeakNF` (rank ≥ 3), full-residue NF beyond rank one, or a
  modulus common to all residue classes.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.RationalCentre
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.SmallLeaves
import ResearchUpgrade.NormLift
import ResearchUpgrade.DefiniteReduction
import ResearchUpgrade.RankOneConfluence

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r) (e : OutWit m r ≃ Fin 2)

/-- The two coordinates. -/
def binK1 : OutWit m r := e.symm 0
def binK2 : OutWit m r := e.symm 1

theorem k1_ne_k2 : binK1 e ≠ binK2 e := by
  intro h
  have := congrArg e h
  simp [binK1, binK2] at this

/-- Rational coefficient of the output/witness form. -/
def binQ (k k' : OutWit m r) : ℚ := (D.P.Q (Sum.inr k) (Sum.inr k') : ℚ)

theorem sum_two (F : OutWit m r → ℚ) : ∑ k, F k = F (binK1 e) + F (binK2 e) := by
  rw [← e.symm.sum_comp, Fin.sum_univ_two]
  rfl

theorem zQuadQ_two (w : OutWit m r → ℚ) :
    D.zQuadQ w = D.binQ (binK1 e) (binK1 e) * w (binK1 e) ^ 2
      + (D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)) * w (binK1 e) * w (binK2 e)
      + D.binQ (binK2 e) (binK2 e) * w (binK2 e) ^ 2 := by
  unfold zQuadQ
  rw [sum_two e]
  rw [sum_two e (fun k' => w (binK1 e) * ((D.P.Q (Sum.inr (binK1 e)) (Sum.inr k') : ℚ) * w k')),
    sum_two e (fun k' => w (binK2 e) * ((D.P.Q (Sum.inr (binK2 e)) (Sum.inr k') : ℚ) * w k'))]
  simp only [binQ]
  ring

theorem zPolarQ_two (v w : OutWit m r → ℚ) :
    D.zPolarQ v w = 2 * D.binQ (binK1 e) (binK1 e) * v (binK1 e) * w (binK1 e)
      + (D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)) * (v (binK1 e) * w (binK2 e) + v (binK2 e) * w (binK1 e))
      + 2 * D.binQ (binK2 e) (binK2 e) * v (binK2 e) * w (binK2 e) := by
  unfold zPolarQ
  rw [sum_two e]
  rw [sum_two e (fun k' => v (binK1 e) * ((D.P.Q (Sum.inr (binK1 e)) (Sum.inr k') : ℚ) * w k')
      + w (binK1 e) * ((D.P.Q (Sum.inr (binK1 e)) (Sum.inr k') : ℚ) * v k')),
    sum_two e (fun k' => v (binK2 e) * ((D.P.Q (Sum.inr (binK2 e)) (Sum.inr k') : ℚ) * w k')
      + w (binK2 e) * ((D.P.Q (Sum.inr (binK2 e)) (Sum.inr k') : ℚ) * v k'))]
  simp only [binQ]
  ring

theorem zLinQ_two (a : Fin n → ℤ) (w : OutWit m r → ℚ) :
    D.zLinQ a w = (D.zLin a (binK1 e) : ℚ) * w (binK1 e) + (D.zLin a (binK2 e) : ℚ) * w (binK2 e) := by
  unfold zLinQ
  exact sum_two e _

/-- The test vector `w = e_{binK1}`. -/
def binVec (x y : ℚ) : OutWit m r → ℚ := fun k => if k = binK1 e then x else if k = binK2 e then y else 0

theorem vec1_k1 (x y : ℚ) : binVec e x y (binK1 e) = x := by simp [binVec]
theorem vec1_k2 (x y : ℚ) : binVec e x y (binK2 e) = y := by
  simp [binVec, (k1_ne_k2 e).symm]

variable {D e}

theorem alpha_pos (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    0 < D.binQ (binK1 e) (binK1 e) := by
  have h := hpos (binVec e 1 0) (by
    intro h0
    have := congrFun h0 (binK1 e)
    simp [vec1_k1] at this)
  rw [D.zQuadQ_two e, vec1_k1, vec1_k2] at h
  simpa using h

theorem disc_pos (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    0 < 4 * D.binQ (binK1 e) (binK1 e) * D.binQ (binK2 e) (binK2 e)
      - (D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)) ^ 2 := by
  have hα := alpha_pos (e := e) hpos
  set α := D.binQ (binK1 e) (binK1 e)
  set b := D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)
  set γ := D.binQ (binK2 e) (binK2 e)
  have h := hpos (binVec e (-b) (2 * α)) (by
    intro h0
    have := congrFun h0 (binK2 e)
    rw [vec1_k2] at this
    simp at this
    linarith)
  rw [D.zQuadQ_two e, vec1_k1, vec1_k2] at h
  have h' : 0 < α * (4 * α * γ - b ^ 2) := by nlinarith [h]
  exact pos_of_mul_pos_right h' hα.le


/-! ### Part 2 — binCentre, residual, diagonalisation -/

variable (D e)

def binAlp : ℚ := D.binQ (binK1 e) (binK1 e)
def binBet : ℚ := D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)
def binGam : ℚ := D.binQ (binK2 e) (binK2 e)
def binDel : ℚ := 4 * D.binAlp e * D.binGam e - D.binBet e ^ 2

def lconst (k : OutWit m r) : ℚ := (D.P.l (Sum.inr k) : ℚ)
def lslope (k : OutWit m r) (i : Fin n) : ℚ :=
  ((D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i) : ℤ) : ℚ)

theorem zLin_cast (a : Fin n → ℤ) (k : OutWit m r) :
    (D.zLin a k : ℚ) = D.lconst k + ∑ i, D.lslope k i * (a i : ℚ) := by
  simp only [zLin, lconst, lslope]
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Centre coefficients (Cramer's rule on the 2×2 polar system). -/
def cc0 (k : OutWit m r) : ℚ :=
  if k = binK1 e then (-2 * D.binGam e * D.lconst (binK1 e) + D.binBet e * D.lconst (binK2 e)) / D.binDel e
  else (D.binBet e * D.lconst (binK1 e) - 2 * D.binAlp e * D.lconst (binK2 e)) / D.binDel e

def cL (k : OutWit m r) (i : Fin n) : ℚ :=
  if k = binK1 e then (-2 * D.binGam e * D.lslope (binK1 e) i + D.binBet e * D.lslope (binK2 e) i) / D.binDel e
  else (D.binBet e * D.lslope (binK1 e) i - 2 * D.binAlp e * D.lslope (binK2 e) i) / D.binDel e

def binCentre (a : Fin n → ℤ) : OutWit m r → ℚ := fun k => D.cc0 e k + ∑ i, D.cL e k i * (a i : ℚ)

theorem lin_comb (A B δ l1 l2 : ℚ) (s1 s2 t : Fin n → ℚ) :
    (A * (l1 + ∑ i, s1 i * t i) + B * (l2 + ∑ i, s2 i * t i)) / δ
      = (A * l1 + B * l2) / δ + ∑ i, (A * s1 i + B * s2 i) / δ * t i := by
  have : ∑ i, (A * s1 i + B * s2 i) / δ * t i
      = (A * ∑ i, s1 i * t i + B * ∑ i, s2 i * t i) / δ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring

theorem centre_k1 (a : Fin n → ℤ) :
    D.binCentre e a (binK1 e) = (-2 * D.binGam e * D.zLin a (binK1 e) + D.binBet e * D.zLin a (binK2 e)) / D.binDel e := by
  rw [D.zLin_cast, D.zLin_cast, lin_comb]
  simp only [binCentre, cc0, cL, if_true]

theorem centre_k2 (a : Fin n → ℤ) :
    D.binCentre e a (binK2 e) = (D.binBet e * D.zLin a (binK1 e) + (-2 * D.binAlp e) * D.zLin a (binK2 e)) / D.binDel e := by
  rw [D.zLin_cast, D.zLin_cast, lin_comb]
  simp only [binCentre, cc0, cL, if_neg (k1_ne_k2 e).symm]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

theorem zPolarQ_two' (v w : OutWit m r → ℚ) :
    D.zPolarQ v w = 2 * D.binAlp e * v (binK1 e) * w (binK1 e)
      + D.binBet e * (v (binK1 e) * w (binK2 e) + v (binK2 e) * w (binK1 e))
      + 2 * D.binGam e * v (binK2 e) * w (binK2 e) := D.zPolarQ_two e v w

theorem zQuadQ_two' (w : OutWit m r → ℚ) :
    D.zQuadQ w = D.binAlp e * w (binK1 e) ^ 2 + D.binBet e * w (binK1 e) * w (binK2 e)
      + D.binGam e * w (binK2 e) ^ 2 := by
  rw [D.zQuadQ_two e]; simp only [binAlp, binBet, binGam]

theorem centre_isCentre (hdel : D.binDel e ≠ 0) (a : Fin n → ℤ) : D.IsCentre a (D.binCentre e a) := by
  intro w
  rw [D.zPolarQ_two' e, D.zLinQ_two e, D.centre_k1 e, D.centre_k2 e]
  have hd : D.binDel e = 4 * D.binAlp e * D.binGam e - D.binBet e ^ 2 := rfl
  generalize D.binDel e = δ at *
  generalize D.binAlp e = α at *
  generalize D.binBet e = b at *
  generalize D.binGam e = γ at *
  field_simp
  linear_combination ((D.zLin a (binK1 e) : ℚ) * w (binK1 e) + (D.zLin a (binK2 e) : ℚ) * w (binK2 e)) * hd

def binOuter (u v : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => u i * v j

theorem outer_form (u v t : Fin n → ℚ) : t ⬝ᵥ (binOuter u v *ᵥ t) = (u ⬝ᵥ t) * (v ⬝ᵥ t) := by
  simp only [binOuter, dotProduct, mulVec, Matrix.of_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

def binALin : Fin n → ℚ := fun i => (D.P.l (Sum.inl i) : ℚ)
def binAQuad : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => (D.P.Q (Sum.inl i) (Sum.inl j) : ℚ)

theorem aPart_cast (a : Fin n → ℤ) :
    (D.aPart a : ℚ) = (D.P.c : ℚ) + D.binALin ⬝ᵥ castQ a + castQ a ⬝ᵥ (D.binAQuad *ᵥ castQ a) := by
  simp only [aPart, binALin, binAQuad, dotProduct, mulVec, Matrix.of_apply, castQ, Finset.mul_sum]
  push_cast
  rfl

def vL (k : OutWit m r) : Fin n → ℚ := fun i => D.cL e k i

/-- The residual as an explicit quadratic form in the input. -/
def residualForm : QuadForm n where
  c := D.binAlp e * D.cc0 e (binK1 e) ^ 2 + D.binBet e * D.cc0 e (binK1 e) * D.cc0 e (binK2 e)
        + D.binGam e * D.cc0 e (binK2 e) ^ 2 - (D.P.c : ℚ)
  l := (2 * D.binAlp e * D.cc0 e (binK1 e) + D.binBet e * D.cc0 e (binK2 e)) • D.vL e (binK1 e)
        + (D.binBet e * D.cc0 e (binK1 e) + 2 * D.binGam e * D.cc0 e (binK2 e)) • D.vL e (binK2 e) - D.binALin
  Q := D.binAlp e • binOuter (D.vL e (binK1 e)) (D.vL e (binK1 e))
        + D.binBet e • binOuter (D.vL e (binK1 e)) (D.vL e (binK2 e))
        + D.binGam e • binOuter (D.vL e (binK2 e)) (D.vL e (binK2 e)) - D.binAQuad

theorem centre_eq (a : Fin n → ℤ) (k : OutWit m r) :
    D.binCentre e a k = D.cc0 e k + D.vL e k ⬝ᵥ castQ a := rfl

theorem residual_eq (a : Fin n → ℤ) :
    D.residual a (D.binCentre e a) = (D.residualForm e).eval (castQ a) := by
  rw [residual, D.zQuadQ_two e, D.aPart_cast, D.centre_eq e a (binK1 e), D.centre_eq e a (binK2 e)]
  simp only [QuadForm.eval, residualForm, add_dotProduct, sub_dotProduct, smul_dotProduct,
    add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul,
    outer_form, smul_eq_mul]
  simp only [binAlp, binBet, binGam]
  ring

theorem binDiag (hα : D.binAlp e ≠ 0) (w : OutWit m r → ℚ) :
    D.zQuadQ w = D.binAlp e * ((w (binK1 e) + D.binBet e / (2 * D.binAlp e) * w (binK2 e)) ^ 2
      + D.binDel e / (4 * D.binAlp e ^ 2) * w (binK2 e) ^ 2) := by
  rw [D.zQuadQ_two e]
  simp only [binDel, binAlp, binBet, binGam] at hα ⊢
  field_simp
  ring

variable {D e}

/-- **Generic binary compiler.** -/
theorem binary_compiler_gen (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ (α β Δ : ℚ) (c0 : OutWit m r → ℚ) (L : OutWit m r → Fin n → ℚ) (Rq : QuadForm n),
      0 < α ∧ 0 < Δ ∧
      (∀ a, D.IsCentre a (fun k => c0 k + ∑ i, L k i * (a i : ℚ))) ∧
      (∀ a, D.residual a (fun k => c0 k + ∑ i, L k i * (a i : ℚ)) = Rq.eval (castQ a)) ∧
      ∀ w : OutWit m r → ℚ,
        D.zQuadQ w = α * ((w (binK1 e) + β * w (binK2 e)) ^ 2 + Δ * w (binK2 e) ^ 2) := by
  have hα : 0 < D.binAlp e := alpha_pos (e := e) hpos
  have hδ : 0 < D.binDel e := disc_pos (e := e) hpos
  refine ⟨D.binAlp e, D.binBet e / (2 * D.binAlp e), D.binDel e / (4 * D.binAlp e ^ 2), D.cc0 e, D.cL e,
    D.residualForm e, hα, by positivity, fun a => D.centre_isCentre e hδ.ne' a,
    fun a => D.residual_eq e a, fun w => D.binDiag e hα.ne' w⟩

/-! ### Part 3 — the section engine (R42-D2 core) -/

theorem two_cases (e : OutWit m r ≃ Fin 2) (k : OutWit m r) : k = binK1 e ∨ k = binK2 e := by
  by_cases h : e k = 0
  · left
    rw [binK1, ← h, Equiv.symm_apply_apply]
  · right
    have h1 : e k = 1 := by
      apply Fin.ext
      have hlt := (e k).isLt
      have hne : (e k).val ≠ 0 := fun h' => h (Fin.ext h')
      simp only [Fin.val_one]
      omega
    rw [binK2, ← h1, Equiv.symm_apply_apply]

theorem solZ_of_norm {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    {z : OutWit m r → ℤ} (h : D.zQuadQ (toQ z - c) = D.residual a c) : D.SolZ a z := by
  have hcs := D.completeSquare hc (toQ z)
  rw [D.zQuadQ_toQ, D.zLinQ_toQ] at hcs
  have h0 : ((D.zQuad z + D.zLinEval a z + D.aPart a : ℤ) : ℚ) = 0 := by
    push_cast; linarith
  unfold SolZ
  rw [D.evalZ]
  exact_mod_cast h0

theorem exists_common_den {ι : Type*} [Fintype ι] (G : ι → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ g : ℤ, (M : ℚ) * G k = g := by
  classical
  set P : ℕ := ∏ k, (G k).den with hP
  refine ⟨P, Finset.prod_pos fun k _ => (G k).den_pos, fun k => ?_⟩
  have hdvd : (G k).den ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  refine ⟨(G k).num * ((P / (G k).den : ℕ) : ℤ), ?_⟩
  have hq : (P : ℚ) = ((P / (G k).den : ℕ) : ℚ) * (G k).den := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  have h := Rat.mul_den_eq_num (G k)
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [hq]
  linear_combination (((P / (G k).den : ℕ) : ℚ)) * h

variable (D e)

/-- The rational binCentre, extended to rational inputs through `castQ`. -/
theorem cen_add (c0 : OutWit m r → ℚ) (L : OutWit m r → Fin n → ℚ) (a0 : Fin n → ℤ)
    (M : ℕ) (t : Fin n → ℤ) (k : OutWit m r) :
    c0 k + ∑ i, L k i * ((a0 + (M : ℤ) • t) i : ℚ)
      = (c0 k + ∑ i, L k i * (a0 i : ℚ)) + (fun i => L k i) ⬝ᵥ castQ ((M : ℤ) • t) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, castQ]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib]
  ring

variable {D e}

/-- **R42-D2 core.**  Positive definite, output-and-witness space of dimension two: weak NF. -/
theorem weakVectorCosetNF_of_binary (e : OutWit m r ≃ Fin 2)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakVectorCosetNF f := by
  classical
  obtain ⟨α, β, Δ, c0, L, Rq, hα, hΔ, hC, hR, hdiag⟩ := binary_compiler_gen (D := D) (e := e) hpos
  have hsol : ∀ a, ∃ z : OutWit m r → ℤ, D.SolZ a z := by
    intro a
    obtain ⟨u, hu⟩ := (hf a (f a)).mpr rfl
    exact ⟨Sum.elim (f a) u, hu⟩
  have hout : ∀ a (z : OutWit m r → ℤ), D.SolZ a z → ∀ j, (f a j : ℚ) = (toQ z) (Sum.inl j) := by
    intro a z h j
    have := (hf a _).mp (D.graph_of_solZ h)
    rw [← this]; rfl
  have hnorm : ∀ a (z : OutWit m r → ℤ), D.SolZ a z →
      D.zQuadQ (toQ z - fun k => c0 k + ∑ i, L k i * (a i : ℚ)) = Rq.eval (castQ a) := by
    intro a z h
    rw [D.offCentre_norm (hC a) h, hR a]
  by_cases h0 : ∀ a, Rq.eval (castQ a) = 0
  · refine ⟨1, 0, fun j => ⟨c0 (Sum.inl j), fun i => L (Sum.inl j) i, 0⟩, le_rfl, fun t j => ?_⟩
    simp only [Nat.cast_one, one_smul, zero_add]
    obtain ⟨z, hz⟩ := hsol t
    have hw : (toQ z - fun k => c0 k + ∑ i, L k i * (t i : ℚ)) = 0 := by
      by_contra hne
      have := hpos _ hne
      rw [hnorm t z hz, h0 t] at this
      exact lt_irrefl _ this
    have hj := congrFun hw (Sum.inl j)
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hj
    rw [hout t z hz j, hj]
    simp [QuadForm.eval, dotProduct, castQ]
  · simp only [not_forall] at h0
    obtain ⟨a0, ha0⟩ := h0
    obtain ⟨z0, hz0⟩ := hsol a0
    set cen0 : OutWit m r → ℚ := fun k => c0 k + ∑ i, L k i * (a0 i : ℚ) with hcen0
    set w0 : OutWit m r → ℚ := toQ z0 - cen0 with hw0
    set r0 := w0 (binK1 e) + β * w0 (binK2 e) with hr0
    set s0 := w0 (binK2 e) with hs0
    have hbase : α * (r0 ^ 2 + Δ * s0 ^ 2) = Rq.eval (castQ a0) := by
      rw [← hdiag, ← hnorm a0 z0 hz0]
    have hc' : 0 < r0 ^ 2 + Δ * s0 ^ 2 := by
      have hnn : 0 ≤ r0 ^ 2 + Δ * s0 ^ 2 := by positivity
      rcases hnn.lt_or_eq with h | h
      · exact h
      · exfalso; apply ha0; rw [← hbase, ← h]; ring
    set T := Rq.translate (castQ a0) with hT
    set ell : Fin n → ℚ := (1 / (2 * α)) • T.l with hell
    set H : Matrix (Fin n) (Fin n) ℚ := (1 / α) • T.Q with hH
    have hTc : T.c = α * (r0 ^ 2 + Δ * s0 ^ 2) := by rw [hbase]; rfl
    have hshift : ∀ x : Fin n → ℚ, Rq.eval (castQ a0 + x)
        = α * ((r0 ^ 2 + Δ * s0 ^ 2) + 2 * (ell ⬝ᵥ x) + x ⬝ᵥ (H *ᵥ x)) := by
      intro x
      rw [QuadForm.eval_translate]
      show T.c + T.l ⬝ᵥ x + x ⬝ᵥ (T.Q *ᵥ x) = _
      rw [hTc, hell, hH, smul_dotProduct, smul_mulVec, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      field_simp
    have hrep : ∀ x : Fin n → ℤ, ∃ X Y : ℚ,
        (r0 ^ 2 + Δ * s0 ^ 2) + 2 * (ell ⬝ᵥ castQ x) + castQ x ⬝ᵥ (H *ᵥ castQ x)
          = X ^ 2 + Δ * Y ^ 2 := by
      intro x
      obtain ⟨z, hz⟩ := hsol (a0 + x)
      have h1 := hshift (castQ x)
      rw [← castQ_add] at h1
      have h2 := hnorm (a0 + x) z hz
      rw [hdiag] at h2
      refine ⟨_, _, mul_left_cancel₀ hα.ne' (h1.symm.trans h2.symm)⟩
    obtain ⟨rl, sl, hsec⟩ := NormLift.norm_section Δ r0 s0 hΔ hc' ell H hrep
    set G : OutWit m r → Fin n → ℚ := fun k i =>
      if k = binK1 e then L k i + rl i - β * sl i else L k i + sl i with hG
    obtain ⟨M, hM, hg⟩ := exists_common_den (fun p : OutWit m r × Fin n => G p.1 p.2)
    choose g hg using hg
    refine ⟨M, a0, fun j => ⟨(z0 (Sum.inl j) : ℚ), fun i => (g (Sum.inl j, i) : ℚ), 0⟩,
      hM, fun t j => ?_⟩
    set zt : OutWit m r → ℤ := fun k => z0 k + ∑ i, g (k, i) * t i with hzt
    set x : Fin n → ℚ := castQ ((M : ℤ) • t) with hx
    have hztq : ∀ k, toQ zt k = toQ z0 k + (fun i => G k i) ⬝ᵥ x := by
      intro k
      simp only [hzt, hx, toQ, dotProduct, castQ, Pi.smul_apply, smul_eq_mul]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hg (k, i)]
      ring
    have hdiff : ∀ k, (toQ zt - fun k => c0 k + ∑ i, L k i * ((a0 + (M : ℤ) • t) i : ℚ)) k
        = w0 k + (fun i => G k i) ⬝ᵥ x - (fun i => L k i) ⬝ᵥ x := by
      intro k
      simp only [Pi.sub_apply]
      rw [hztq k, cen_add c0 L a0 M t k, hw0, hcen0]
      simp only [Pi.sub_apply]
      rw [← hx]
      ring
    have hG1 : (fun i => G (binK1 e) i) = (fun i => L (binK1 e) i) + rl - β • sl := by
      funext i; simp [hG]
    have hG2 : (fun i => G (binK2 e) i) = (fun i => L (binK2 e) i) + sl := by
      funext i; simp [hG, (k1_ne_k2 e).symm]
    have hsolt : D.SolZ (a0 + (M : ℤ) • t) zt := by
      apply solZ_of_norm (hC _)
      rw [hR, hdiag, hdiff, hdiff, hG1, hG2]
      have hs := hsec x
      have hsh := hshift x
      rw [hx, ← castQ_add] at hsh
      rw [← hx] at hsh
      simp only [add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
      rw [hsh, hs, hr0, hs0]
      ring
    rw [hout _ zt hsolt j, hztq]
    simp only [QuadForm.eval, Matrix.zero_mulVec, dotProduct_zero, add_zero, toQ]
    congr 1
    simp only [dotProduct, hx, castQ, Pi.smul_apply, smul_eq_mul]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hg (Sum.inl j, i)]
    ring

/-- The `(1,1)` coordinates. -/
def eOW : OutWit 1 1 ≃ Fin 2 := finSumFinEquiv

def eTZ : OutWit 2 0 ≃ Fin 2 := Equiv.sumEmpty (Fin 2) (Fin 0)

theorem k1_eOW : binK1 eOW = (Sum.inl 0 : OutWit 1 1) := by decide
theorem k2_eOW : binK2 eOW = (Sum.inr 0 : OutWit 1 1) := by decide

/-- **R42-D1.**  One output, one witness, positive definite: an affine binCentre, a quadratic residual
and a fixed diagonalisation `Q(w) = α((y + βu)² + Δu²)` with `α, Δ > 0`. -/
theorem definite_binary_compiler {n : ℕ} (D : QuadraticGraphData n 1 1)
    (hpos : ∀ u : OutWit 1 1 → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ (α β Δ : ℚ) (c0 : OutWit 1 1 → ℚ) (L : OutWit 1 1 → Fin n → ℚ) (Rq : QuadForm n),
      0 < α ∧ 0 < Δ ∧
      (∀ a, D.IsCentre a (fun k => c0 k + ∑ i, L k i * (a i : ℚ))) ∧
      (∀ a, D.residual a (fun k => c0 k + ∑ i, L k i * (a i : ℚ)) = Rq.eval (castQ a)) ∧
      ∀ w : OutWit 1 1 → ℚ,
        D.zQuadQ w = α * ((w (Sum.inl 0) + β * w (Sum.inr 0)) ^ 2 + Δ * w (Sum.inr 0) ^ 2) := by
  have h := binary_compiler_gen (D := D) (e := eOW) hpos
  rwa [k1_eOW, k2_eOW] at h

/-- Positive definite with at most two output/witness coordinates: weak NF. -/
theorem weakNF_of_small {n m r' : ℕ} (D : QuadraticGraphData n m r') (hmr : m + r' ≤ 2)
    (hm : 0 < m) (hpos : ∀ u : OutWit m r' → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakVectorCosetNF f := by
  rcases Nat.lt_or_ge (m + r') 2 with h | h
  · obtain rfl : m = 1 := by omega
    obtain rfl : r' = 0 := by omega
    exact weakVectorCosetNF_of_fullVectorCosetNF (D.fullVectorCosetNF_of_defines hf)
  · have h2 : m + r' = 2 := by omega
    exact D.weakVectorCosetNF_of_binary (finSumFinEquiv.trans (finCongr h2)) hpos hf

theorem negGraph_zPolarQ {n m r : ℕ} (D : QuadraticGraphData n m r) (v w : OutWit m r → ℚ) :
    D.negGraph.zPolarQ v w = - D.zPolarQ v w := by
  simp only [zPolarQ, negGraph, Matrix.neg_apply, Int.cast_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem negGraph_polarRank {n m r : ℕ} (D : QuadraticGraphData n m r) :
    D.negGraph.polarRank = D.polarRank := by
  have hmap : D.negGraph.polarMapQ = -D.polarMapQ := by
    apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
    show D.negGraph.zPolarQ v w = -(D.zPolarQ v w)
    exact D.negGraph_zPolarQ v w
  unfold polarRank
  rw [hmap, LinearMap.range_neg]

end QuadraticGraphData

end DiophCompression.ResearchUpgrade

namespace DiophCompression.ResearchUpgrade

/-- **R42-D2.**  The first arithmetic residue, for every number of inputs. -/
theorem definiteWeakNF_oneOut_oneWit_holds : DefiniteWeakNF_oneOut_oneWit :=
  fun _ D _ hpos hf => D.weakVectorCosetNF_of_binary QuadraticGraphData.eOW hpos hf

/-- Two outputs, no witness, positive definite. -/
def DefiniteWeakNF_twoOut_zeroWit : Prop :=
  ∀ (n : ℕ) (D : QuadraticGraphData n 2 0) (f : (Fin n → ℤ) → (Fin 2 → ℤ)),
    (∀ u : OutWit 2 0 → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → D.Defines f → WeakVectorCosetNF f

theorem definiteWeakNF_twoOut_zeroWit_holds : DefiniteWeakNF_twoOut_zeroWit :=
  fun _ D _ hpos hf => D.weakVectorCosetNF_of_binary QuadraticGraphData.eTZ hpos hf


/-- Semidefinite (either sign), non-zero, polar rank at most two. -/
def LowRankSemidefiniteWeakNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
    ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
    D.polarRank ≤ 2 → D.Defines f → WeakVectorCosetNF f

/-- **R42-D3.** -/
theorem lowRankSemidefiniteWeakNF_holds : LowRankSemidefiniteWeakNF := by
  intro n m r D f hm hQ hsemi hrank hf
  have key : ∀ D' : QuadraticGraphData n m r, D'.Defines f → (∃ v, D'.zQuad v ≠ 0) →
      (∀ u, 0 ≤ D'.zQuadQ u) → D'.polarRank ≤ 2 → WeakVectorCosetNF f := by
    intro D' hf' hQ' hpos' hrank'
    obtain ⟨U, -, hdef', -, hposdef⟩ := D'.definite_reduction hm hf' hQ' hpos'
    have hml := D'.m_le_polarRank hm hf' hQ'
    exact QuadraticGraphData.weakNF_of_small (D'.compiledData U) (by omega) hm hposdef hdef'
  rcases hsemi with hpos | hneg
  · exact key D hf hQ hpos hrank
  · refine key D.negGraph (D.negGraph_defines hf) ?_ ?_ ?_
    · obtain ⟨v, hv⟩ := hQ
      exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
    · intro u; rw [D.negGraph_zQuadQ]; linarith [hneg u]
    · rw [D.negGraph_polarRank]; exact hrank

end DiophCompression.ResearchUpgrade
