/-
  VectorClassification.lean — s58.  GPT R46 Packet D1–D3 (GATE28): the multi-output characterization and its
  consequences.

  * `singleQuadratic_iff_commonSlope_of_TCER` (D1, [C]) — for m ≥ 2: SE₂ (original class) ⟺ one integer slope on all
    residue classes.  TCER is used only in the forward direction (`sealedCommonSlopeNF_of_TCER`); the reverse direction
    is the unconditional compiler `singleQuadratic_of_commonSlope`.
  * `sqFn_singleQuadratic`, `sqPadFn_not_commonSlope`, `sqPadFn_not_singleQuadratic_of_TCER` (D2) — a ↦ a² is SE₂ but,
    given TCER, a ↦ (a², 0) is not: adding a constant output does not preserve the class.
  * `parityFn_*`, `not_commonSlope_of_fullVectorCosetNF` (D2, control) — (2b − a)(2b + 3a − 1) = 0 defines an SE₂
    function with the full-residue NF and no common slope; "full NF ⇒ common slope" is false.
  * `commonSlope_range`, `commonSlope_injective_iff`, `commonSlope_injective_dim` (D3) — image and injectivity given a
    common-slope certificate; n ≤ m through the existing unconditional II-D.

  Statements frozen before proof (`~/lean/s58_evidence/freeze/G3_FREEZE_s58.lean`, ruling of Dr. Fukui
  2026-09-26 13:07).  Claim tags: [P] (std-3) except D1 and the TCER form of D2, [C].  Novelty of the characterization
  is NOT claimed here; it is to be checked against the literature.
-/
import ResearchUpgrade.CommonSlopeForward
import ResearchUpgrade.CommonSlopeCompiler

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial

/-- **D1.**  TCER ⇒ for m ≥ 2: `f` is SE₂-definable (original class) iff `f` has one integer slope on all residue
classes of one modulus. -/
theorem singleQuadratic_iff_commonSlope_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)), 2 ≤ m →
      (DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ CommonSlopeIntNF f) :=
  fun n m f hm => ⟨sealedCommonSlopeNF_of_TCER hT n m f hm, singleQuadratic_of_commonSlope⟩

/-- The scalar square `a ↦ a²`. -/
def sqFn : (Fin 1 → ℤ) → (Fin 1 → ℤ) := fun a _ => a 0 ^ 2

/-- The square padded by a constant output: `a ↦ (a², 0)`. -/
def sqPadFn : (Fin 1 → ℤ) → (Fin 2 → ℤ) := fun a => ![a 0 ^ 2, 0]

/-- **D2.**  `a ↦ a²` is SE₂-definable (unconditional). -/
theorem sqFn_singleQuadratic : DiophCompression.SingleQuadraticDefinableFunctionZZ sqFn := by
  refine singleQuadratic_of_poly (W := Fin 0)
    (X (Sum.inl (Fin.natAdd 1 0)) - X (Sum.inl (Fin.castAdd 1 0)) ^ 2) ?_ sqFn ?_
  · exact sc_td_sub ((sc_td_X _).trans (by norm_num)) (sc_td_sq (sc_td_X _))
  · intro a b
    simp only [map_sub, map_pow, eval_X, Sum.elim_inl, pairVec_left, pairVec_right]
    constructor
    · intro h
      exact ⟨fun i => i.elim0, by subst h; simp [sqFn]⟩
    · rintro ⟨-, h⟩
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      simp only [sqFn]
      linarith

/-- The input `(fun _ => x) + M • (fun _ => y)` on one coordinate. -/
theorem vc_one_add_smul (x y : ℤ) (M : ℕ) :
    ((fun _ => x) + (M : ℤ) • (fun _ => y) : Fin 1 → ℤ) = fun _ => x + (M : ℤ) * y := by
  funext i; simp

/-- **D2.**  `a ↦ (a², 0)` has no common slope (unconditional). -/
theorem sqPadFn_not_commonSlope : ¬ CommonSlopeIntNF sqPadFn := by
  rintro ⟨M, B, hM, h⟩
  have h0 := congrFun (h (fun _ => 0) (fun _ => 1)) 0
  have h1 := congrFun (h (fun _ => 1) (fun _ => 1)) 0
  rw [vc_one_add_smul] at h0 h1
  simp only [sqPadFn, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    Matrix.cons_val_zero] at h0 h1
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  nlinarith [h0, h1]

/-- **D2.**  TCER ⇒ `a ↦ (a², 0)` is NOT SE₂-definable, although `a ↦ a²` is: adding a constant output coordinate does
not preserve the class.  (The linear zero-padding `exists_graph_injective_pad` is a different operation.) -/
theorem sqPadFn_not_singleQuadratic_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ¬ DiophCompression.SingleQuadraticDefinableFunctionZZ sqPadFn := fun h =>
  sqPadFn_not_commonSlope ((singleQuadratic_iff_commonSlope_of_TCER hT 1 2 sqPadFn le_rfl).mp h)

/-- The scalar control: `f (2t) = t`, `f (2t + 1) = −3t − 1`. -/
def parityFn : (Fin 1 → ℤ) → (Fin 1 → ℤ) :=
  fun a _ => if a 0 % 2 = 0 then a 0 / 2 else (1 - 3 * a 0) / 2

theorem parityFn_apply (x : ℤ) (j : Fin 1) :
    parityFn (fun _ => x) j = if x % 2 = 0 then x / 2 else (1 - 3 * x) / 2 := rfl

/-- **D2, control.**  `(2b − a)(2b + 3a − 1) = 0` defines `parityFn`. -/
theorem parityFn_graph (a b : ℤ) :
    (2 * b - a) * (2 * b + 3 * a - 1) = 0 ↔ b = parityFn (fun _ => a) 0 := by
  rw [parityFn_apply, mul_eq_zero]
  split_ifs with h <;> omega

theorem parityFn_singleQuadratic : DiophCompression.SingleQuadraticDefinableFunctionZZ parityFn := by
  refine singleQuadratic_of_poly (W := Fin 0)
    ((C 2 * X (Sum.inl (Fin.natAdd 1 0)) - X (Sum.inl (Fin.castAdd 1 0)))
      * (C 2 * X (Sum.inl (Fin.natAdd 1 0)) + C 3 * X (Sum.inl (Fin.castAdd 1 0)) - 1)) ?_ parityFn ?_
  · refine le_trans (totalDegree_mul _ _) ?_
    have h1 := sc_td_sub (sc_td_CX (σ := Fin (1 + 1) ⊕ Fin 0) 2 (Sum.inl (Fin.natAdd 1 0)))
      (sc_td_X (Sum.inl (Fin.castAdd 1 0)))
    have h2 := sc_td_sub (sc_td_add (sc_td_CX (σ := Fin (1 + 1) ⊕ Fin 0) 2 (Sum.inl (Fin.natAdd 1 0)))
      (sc_td_CX 3 (Sum.inl (Fin.castAdd 1 0)))) (sc_td_one (σ := Fin (1 + 1) ⊕ Fin 0))
    omega
  · intro a b
    simp only [map_mul, map_sub, map_add, map_one, eval_C, eval_X, Sum.elim_inl, pairVec_left,
      pairVec_right]
    constructor
    · intro h
      refine ⟨fun i => i.elim0, (parityFn_graph (a 0) (b 0)).mpr ?_⟩
      rw [h]; rfl
    · rintro ⟨-, h⟩
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact (parityFn_graph (a 0) (b 0)).mp h

theorem parityFn_fullVectorCosetNF : FullVectorCosetNF parityFn := by
  refine ⟨2, by norm_num, fun ρ => ?_⟩
  by_cases hp : ρ 0 % 2 = 0
  · refine ⟨fun _ => ⟨((parityFn ρ 0 : ℤ) : ℚ), fun _ => 1, 0⟩, fun t j => ?_⟩
    have e : parityFn (ρ + ((2 : ℕ) : ℤ) • t) j = parityFn ρ 0 + t 0 := by
      simp only [parityFn, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_ofNat]
      split_ifs <;> omega
    rw [e]
    simp [QuadForm.eval, castQ, dotProduct]
  · refine ⟨fun _ => ⟨((parityFn ρ 0 : ℤ) : ℚ), fun _ => -3, 0⟩, fun t j => ?_⟩
    have e : parityFn (ρ + ((2 : ℕ) : ℤ) • t) j = parityFn ρ 0 - 3 * t 0 := by
      simp only [parityFn, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_ofNat]
      split_ifs <;> omega
    rw [e]
    simp [QuadForm.eval, castQ, dotProduct]
    ring

theorem parityFn_not_commonSlope : ¬ CommonSlopeIntNF parityFn := by
  rintro ⟨M, B, hM, h⟩
  have h0 := congrFun (h (fun _ => 0) (fun _ => 2)) 0
  have h1 := congrFun (h (fun _ => 1) (fun _ => 2)) 0
  simp only [parityFn, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one] at h0 h1
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  split_ifs at h0 h1 <;> omega

/-- **D2, negation control.**  "Full NF ⇒ common slope" fails for SE₂ functions (already for m = 1). -/
theorem not_commonSlope_of_fullVectorCosetNF :
    ¬ ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → FullVectorCosetNF f → CommonSlopeIntNF f :=
  fun H => parityFn_not_commonSlope (H 1 1 parityFn parityFn_singleQuadratic parityFn_fullVectorCosetNF)

/-- Every input is `ρ + M u` with `0 ≤ ρ < M` coordinatewise (Euclidean division, negative inputs included). -/
theorem cs_decomp {n M : ℕ} (hM : 1 ≤ M) (a : Fin n → ℤ) :
    ∃ (ρ : Fin n → Fin M) (u : Fin n → ℤ), a = (fun i => ((ρ i : ℕ) : ℤ)) + (M : ℤ) • u := by
  have hMpos : (0 : ℤ) < M := by exact_mod_cast (show 0 < M by omega)
  refine ⟨fun i => ⟨(a i % M).toNat, by
      have h1 := Int.emod_lt_of_pos (a i) hMpos
      have h2 := Int.emod_nonneg (a i) (ne_of_gt hMpos)
      omega⟩, fun i => a i / M, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.val_mk]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hMpos))]
  exact (Int.emod_add_ediv (a i) M).symm

/-- The decomposition `ρ + M u` is unique. -/
theorem cs_decomp_unique {n M : ℕ} (hM : 1 ≤ M) {ρ σ : Fin n → Fin M} {u v : Fin n → ℤ}
    (h : (fun i => ((ρ i : ℕ) : ℤ)) + (M : ℤ) • u = (fun i => ((σ i : ℕ) : ℤ)) + (M : ℤ) • v) :
    ρ = σ ∧ u = v := by
  have hMpos : (0 : ℤ) < M := by exact_mod_cast (show 0 < M by omega)
  have key : ∀ i, u i = v i ∧ ((ρ i : ℕ) : ℤ) = ((σ i : ℕ) : ℤ) := by
    intro i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have r1 : (((ρ i : ℕ) : ℤ) + (M : ℤ) * u i) / M = u i ∧
        (((ρ i : ℕ) : ℤ) + (M : ℤ) * u i) % M = ((ρ i : ℕ) : ℤ) :=
      (Int.ediv_emod_unique hMpos).mpr ⟨by ring, by positivity, by exact_mod_cast (ρ i).isLt⟩
    have r2 : (((ρ i : ℕ) : ℤ) + (M : ℤ) * u i) / M = v i ∧
        (((ρ i : ℕ) : ℤ) + (M : ℤ) * u i) % M = ((σ i : ℕ) : ℤ) :=
      (Int.ediv_emod_unique hMpos).mpr ⟨by linarith [hi], by positivity, by exact_mod_cast (σ i).isLt⟩
    exact ⟨r1.1.symm.trans r2.1, r1.2.symm.trans r2.2⟩
  exact ⟨funext fun i => Fin.ext (by exact_mod_cast (key i).2), funext fun i => (key i).1⟩

/-- **D3.**  Given a common-slope certificate, the image of `f` is the finite union `⋃_ρ (f ρ + B ℤⁿ)`. -/
theorem commonSlope_range {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {M : ℕ}
    {B : Matrix (Fin m) (Fin n) ℤ} (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t) :
    Set.range f = ⋃ ρ : Fin n → Fin M,
      Set.range fun t : Fin n → ℤ => f (fun i => ((ρ i : ℕ) : ℤ)) + B *ᵥ t := by
  ext y
  simp only [Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨ρ, u, rfl⟩ := cs_decomp hM a
    exact ⟨ρ, u, (hcs _ u).symm⟩
  · rintro ⟨ρ, t, rfl⟩
    exact ⟨_, hcs _ t⟩

/-- **D3.**  Given a common-slope certificate: `f` injective ⟺ `B` injective on `ℤⁿ` and distinct residues have
disjoint cosets. -/
theorem commonSlope_injective_iff {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {M : ℕ}
    {B : Matrix (Fin m) (Fin n) ℤ} (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t) :
    Function.Injective f ↔
      Function.Injective (fun t : Fin n → ℤ => B *ᵥ t) ∧
        ∀ ρ σ : Fin n → Fin M, ρ ≠ σ → ∀ t : Fin n → ℤ,
          f (fun i => ((ρ i : ℕ) : ℤ)) - f (fun i => ((σ i : ℕ) : ℤ)) ≠ B *ᵥ t := by
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  constructor
  · intro hinj
    refine ⟨fun t t' htt => ?_, fun ρ σ hne t hdiff => ?_⟩
    · have e : f (0 + (M : ℤ) • t) = f (0 + (M : ℤ) • t') := by
        rw [hcs, hcs]; simp only at htt; rw [htt]
      have e2 := hinj e
      funext i
      have hc := congrFun e2 i
      simp only [zero_add, Pi.smul_apply, smul_eq_mul] at hc
      exact mul_left_cancel₀ hM0 hc
    · have e : f (fun i => ((ρ i : ℕ) : ℤ)) = f ((fun i => ((σ i : ℕ) : ℤ)) + (M : ℤ) • t) := by
        rw [hcs, ← hdiff]; abel
      have e2 := hinj e
      have e3 : (fun i => ((ρ i : ℕ) : ℤ)) + (M : ℤ) • (0 : Fin n → ℤ)
          = (fun i => ((σ i : ℕ) : ℤ)) + (M : ℤ) • t := by
        rw [smul_zero, add_zero]; exact e2
      exact hne (cs_decomp_unique hM e3).1
  · rintro ⟨hB, hdisj⟩ a a' haa
    obtain ⟨ρ, u, rfl⟩ := cs_decomp hM a
    obtain ⟨σ, v, rfl⟩ := cs_decomp hM a'
    rw [hcs, hcs] at haa
    by_cases hρσ : ρ = σ
    · subst hρσ
      have huv : u = v := hB (add_left_cancel haa)
      rw [huv]
    · exfalso
      apply hdisj ρ σ hρσ (v - u)
      rw [Matrix.mulVec_sub]
      linear_combination haa

/-- **D3, corollary.**  A common-slope injective map `ℤⁿ → ℤᵐ` has `n ≤ m` (unconditional). -/
theorem commonSlope_injective_dim {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : CommonSlopeIntNF f) (hinj : Function.Injective f) : n ≤ m :=
  singleQuadratic_injective_dimension_sharp (singleQuadratic_of_commonSlope h) hinj

end DiophCompression.ResearchUpgrade
