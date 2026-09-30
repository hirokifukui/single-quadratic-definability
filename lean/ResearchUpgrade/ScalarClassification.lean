/-
  ScalarClassification.lean — s59.  GPT R47 Packets B1, B2, C4, D1 (GATE29): the scalar classification on the
  ORIGINAL class `SingleQuadraticDefinableFunctionZZ`.

  * `commonSlope_of_TCER_of_two_le_polarRank` (B1, [C]) — any m > 0, Q ≠ 0, polar rank ≥ 2 ⇒ one integer slope
    (the m ≥ 2 hypothesis of R47 only produced Q ≠ 0 and polar rank ≥ 2).
  * `scalar_commonSlope_or_rn_of_TCER`, `sealed_scalar_commonSlope_or_rn_of_TCER` (B2, [C]) — a scalar function has a
    common slope or an explicit witness-free single quadratic graph (Q ≡ 0 via the linear branch; polar rank one via
    the witness-radical compiler).
  * `zeroWitness_of_globalQuadratic`, `zeroWitness_of_parityAffine`, `singleQuadratic_of_scalarFamilies` (C4, [P]) —
    the reverse direction, witness-free for families Q and H.
  * `sealed_scalarFamilies_of_TCER`, `scalar_singleQuadratic_iff_of_TCER` (D1, [C]) — TCER ⇒ (SE₂ ⟺ common slope ∨
    global rational quadratic ∨ parity-affine), for every number of inputs.
  * `commonSlopeIntNF_of_zero_outputs` [P], `singleQuadratic_iff_commonSlope_of_TCER_of_ne_one` [C] — all m ≠ 1.

  Statements frozen before proof (`~/lean/s59_evidence/freeze/H2_FREEZE_s59.lean` 910bbc1b, ruling of Dr. Fukui
  2026-09-27 15:56).  TCER is an explicit hypothesis, never an axiom, and is used only in the forward direction.
  The three-family statement follows GPT R47 SCALAR_CLASSIFICATION_ROUTE §0; novelty is not claimed here.
-/
import ResearchUpgrade.ScalarRoots

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial

theorem commonSlope_of_TCER_of_two_le_polarRank (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) → 2 ≤ D.polarRank → D.Defines f → CommonSlopeIntNF f := by
  intro n m r D f hm hQ hrank hf
  rcases D.branch_exhaustive with h1 | ⟨x, hx0, hxr⟩ | ⟨hqa, hsd | hsd' | ⟨hp, hq⟩⟩
  · exfalso
    obtain ⟨v, hv⟩ := hQ
    apply hv
    have h := h1 (toQ v)
    simp only [QuadraticGraphData.zQuadQ, toQ] at h
    simp only [QuadraticGraphData.zQuad]
    exact_mod_cast h
  · rcases Nat.lt_or_ge 2 D.polarRank with h3 | h2
    · exact absurd hf (isotropic_three_le_polarRank_not_defines n m r D f hm ⟨x, hx0, hxr⟩ h3)
    · exact isotropicRankTwoCommonSlope_holds n m r D f hm ⟨x, hx0, hxr⟩ h2 hf
  · exact semidefiniteCommonSlopeNF_of_TCER hT n m r D f hm hQ (Or.inl hsd) hrank hf
  · exact semidefiniteCommonSlopeNF_of_TCER hT n m r D f hm hQ (Or.inr hsd') hrank hf
  · exact anisotropicIndefiniteCommonSlope_holds n m r D f hm hqa hp hq hf

theorem scalar_commonSlope_or_rn_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n r : ℕ) (D : QuadraticGraphData n 1 r) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), D.Defines f →
      CommonSlopeIntNF f ∨ ∃ (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ),
        ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = scalarOut f x := by
  classical
  intro n r D f hf
  by_cases hz : ∀ x : OutWit 1 r → ℚ, D.zQuadQ x = 0
  · right
    have hpol := D.zPolar_eq_zero_of_zQuadQ_zero hz
    refine ⟨D.lbA, D.lbBeta, D.lbD, D.lbE, D.lbPhi, D.lbG, fun x y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · exact congrFun ((hf x _).mp (D.graph_of_rn_linear hpol hf hy)) 0
    · rw [hy]; exact D.rn_of_sol_linear hpol hf x
  have hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0 := D.exists_int_zQuad_ne_zero hz
  rcases Nat.lt_or_ge 1 D.polarRank with h2 | h1
  · exact Or.inl (commonSlope_of_TCER_of_two_le_polarRank hT n 1 r D f Nat.one_pos hQ h2 hf)
  right
  have hne : ∃ w₀ : OutWit 1 r → ℚ, D.polarMapQ w₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hz
    intro x
    apply D.zQuadQ_eq_zero_of_inRadicalQ
    intro w
    show D.polarMapQ x w = 0
    rw [h x]; rfl
  have hrank : D.polarRank = 1 := by
    obtain ⟨w₀, hw₀⟩ := hne
    have hpos : 0 < D.polarRank := by
      unfold QuadraticGraphData.polarRank
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      exact ⟨⟨D.polarMapQ w₀, LinearMap.mem_range_self _ _⟩, fun h => hw₀ (congrArg Subtype.val h)⟩
    omega
  have hT' : D.Total := fun a => ⟨f a, (hf a (f a)).mpr rfl⟩
  have hOU := D.outputUnique_of_defines hf
  obtain ⟨u, hu⟩ := (hf 0 (f 0)).mpr rfl
  have hz0 : D.SolZ 0 (Sum.elim (f 0) u) := hu
  obtain ⟨w₀, hw₀⟩ := hne
  have hcodim : ∀ x : OutWit 1 r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀) := by
    intro x
    have hv0 : (⟨D.polarMapQ w₀, LinearMap.mem_range_self _ _⟩ : LinearMap.range D.polarMapQ) ≠ 0 := by
      intro h; exact hw₀ (congrArg Subtype.val h)
    have h1 : Module.finrank ℚ (LinearMap.range D.polarMapQ) = 1 := hrank
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv0).mp h1
      ⟨D.polarMapQ x, LinearMap.mem_range_self _ _⟩
    have hc' : c • D.polarMapQ w₀ = D.polarMapQ x := congrArg Subtype.val hc
    refine ⟨c, fun w => ?_⟩
    show D.polarMapQ (x - c • w₀) w = 0
    rw [map_sub, map_smul, hc', sub_self]
    rfl
  have hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x :=
    fun x hx => D.witnessDir_inRadicalQ Nat.one_pos hOU hQ hz0 hcodim hx
  have hD' := D.noWitnessData_defines hOU hT' hQ hrad hf
  refine ⟨D.noWitnessData.coefA, D.noWitnessData.coefBeta, D.noWitnessData.coefD, D.noWitnessData.coefE,
    D.noWitnessData.coefPhi, D.noWitnessData.coefG, fun x y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · exact congrFun ((hD' x _).mp (D.noWitnessData.graph_of_rn hy)) 0
  · rw [hy]; exact D.noWitnessData.rn_of_sol hD' x

theorem sealed_scalar_commonSlope_or_rn_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n : ℕ) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), DiophCompression.SingleQuadraticDefinableFunctionZZ f →
      CommonSlopeIntNF f ∨ ∃ (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ),
        ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = scalarOut f x := by
  intro n f hf
  obtain ⟨r, D, hD⟩ := graphData_of_singleQuadraticDefinable hf
  exact scalar_commonSlope_or_rn_of_TCER hT n r D f hD

theorem zeroWitness_of_globalQuadratic {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : GlobalQuadratic (scalarOut f)) :
    ∃ P : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ, P.totalDegree ≤ 2 ∧
      ∀ (a : Fin n → ℤ) (b : Fin 1 → ℤ), b = f a ↔ MvPolynomial.eval (Sum.elim (pairVec a b) 0) P = 0 := by
  classical
  obtain ⟨q, hq⟩ := h
  let xs : Option (Fin n ⊕ Fin n × Fin n) → ℚ := fun o =>
    match o with
    | none => q.c
    | some (Sum.inl i) => q.l i
    | some (Sum.inr ij) => q.Q ij.1 ij.2
  obtain ⟨N, hN, hG⟩ := cr_exists_common_den xs
  choose G hG using hG
  have hc : (G none : ℚ) = N * q.c := hG none
  have hl : ∀ i, (G (some (Sum.inl i)) : ℚ) = N * q.l i := fun i => hG (some (Sum.inl i))
  have hQ : ∀ i j, (G (some (Sum.inr (i, j))) : ℚ) = N * q.Q i j := fun i j => hG (some (Sum.inr (i, j)))
  let A : Fin n → MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ := fun i => X (Sum.inl (Fin.castAdd 1 i))
  let Bv : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ := X (Sum.inl (Fin.natAdd n 0))
  refine ⟨C (N : ℤ) * Bv - (C (G none) + ∑ i, C (G (some (Sum.inl i))) * A i
      + ∑ i, ∑ j, C (G (some (Sum.inr (i, j)))) * (A i * A j)), ?_, ?_⟩
  · have hAA : ∀ i j, (C (G (some (Sum.inr (i, j)))) * (A i * A j)).totalDegree ≤ 2 := by
      intro i j
      simp only [A]
      refine le_trans (totalDegree_mul _ _) ?_
      have h1 := totalDegree_C (σ := Fin (n + 1) ⊕ Fin 0) (G (some (Sum.inr (i, j))))
      have h2 : (X (Sum.inl (Fin.castAdd 1 i)) * X (Sum.inl (Fin.castAdd 1 j)) :
          MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ).totalDegree ≤ 2 := by
        refine le_trans (totalDegree_mul _ _) ?_
        have := sc_td_X (σ := Fin (n + 1) ⊕ Fin 0) (Sum.inl (Fin.castAdd 1 i))
        have := sc_td_X (σ := Fin (n + 1) ⊕ Fin 0) (Sum.inl (Fin.castAdd 1 j))
        omega
      omega
    simp only [A, Bv]
    refine sc_td_sub (le_trans (sc_td_CX _ _) (by norm_num)) (sc_td_add (sc_td_add ?_ ?_) ?_)
    · rw [totalDegree_C]; norm_num
    · exact sc_td_sum _ fun i => le_trans (sc_td_CX _ _) (by norm_num)
    · exact sc_td_sum _ fun i => sc_td_sum _ fun j => hAA i j
  · intro a b
    have hev : MvPolynomial.eval (Sum.elim (pairVec a b) 0) (C (N : ℤ) * Bv - (C (G none)
        + ∑ i, C (G (some (Sum.inl i))) * A i + ∑ i, ∑ j, C (G (some (Sum.inr (i, j)))) * (A i * A j)))
        = (N : ℤ) * b 0 - (G none + ∑ i, G (some (Sum.inl i)) * a i
          + ∑ i, ∑ j, G (some (Sum.inr (i, j))) * (a i * a j)) := by
      simp only [A, Bv, map_mul, map_sub, map_add, map_sum, eval_C, eval_X, Sum.elim_inl, pairVec_left,
        pairVec_right]
    rw [hev]
    have hqa : (scalarOut f a : ℚ) = q.c + ∑ i, q.l i * (a i : ℚ) + ∑ i, ∑ j, q.Q i j * ((a i : ℚ) * (a j : ℚ)) := by
      rw [hq a]
      simp only [QuadForm.eval, dotProduct, castQ, Matrix.mulVec, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hcast : (((N : ℤ) * b 0 - (G none + ∑ i, G (some (Sum.inl i)) * a i
          + ∑ i, ∑ j, G (some (Sum.inr (i, j))) * (a i * a j)) : ℤ) : ℚ)
        = (N : ℚ) * ((b 0 : ℚ) - (scalarOut f a : ℚ)) := by
      have e1 : ∑ i, ((G (some (Sum.inl i)) : ℤ) : ℚ) * (a i : ℚ) = (N : ℚ) * ∑ i, q.l i * (a i : ℚ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hl]; ring
      have e2 : ∑ i, ∑ j, ((G (some (Sum.inr (i, j))) : ℤ) : ℚ) * ((a i : ℚ) * (a j : ℚ))
          = (N : ℚ) * ∑ i, ∑ j, q.Q i j * ((a i : ℚ) * (a j : ℚ)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hQ]; ring
      push_cast
      rw [e1, e2, hc, hqa]
      ring
    constructor
    · intro hb
      have : ((((N : ℤ) * b 0 - (G none + ∑ i, G (some (Sum.inl i)) * a i
          + ∑ i, ∑ j, G (some (Sum.inr (i, j))) * (a i * a j)) : ℤ) : ℚ)) = 0 := by
        rw [hcast, hb]; simp [scalarOut]
      exact_mod_cast this
    · intro h0
      have h1 : (N : ℚ) * ((b 0 : ℚ) - (scalarOut f a : ℚ)) = 0 := by
        rw [← hcast]; exact_mod_cast h0
      have h2 : (b 0 : ℚ) = (scalarOut f a : ℚ) := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hNQ
        · linarith
      have h3 : b 0 = scalarOut f a := by exact_mod_cast h2
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact h3

theorem zeroWitness_of_parityAffine {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : ParityAffineNF (scalarOut f)) :
    ∃ P : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ, P.totalDegree ≤ 2 ∧
      ∀ (a : Fin n → ℤ) (b : Fin 1 → ℤ), b = f a ↔ MvPolynomial.eval (Sum.elim (pairVec a b) 0) P = 0 := by
  classical
  obtain ⟨p, q, c, c', hpq, -, hcc, hF⟩ := h
  let A : Fin n → MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ := fun i => X (Sum.inl (Fin.castAdd 1 i))
  let Bv : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ := X (Sum.inl (Fin.natAdd n 0))
  refine ⟨(C 2 * Bv - (∑ i, C (p i) * A i + C c)) * (C 2 * Bv - (∑ i, C (q i) * A i + C c')), ?_, ?_⟩
  · have hc0 : ∀ z : ℤ, (C z : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ).totalDegree ≤ 1 := by
      intro z; rw [totalDegree_C]; norm_num
    have h1 := sc_td_sub (sc_td_CX (σ := Fin (n + 1) ⊕ Fin 0) 2 (Sum.inl (Fin.natAdd n 0)))
      (sc_td_add (sc_td_sum _ fun i => sc_td_CX (p i) (Sum.inl (Fin.castAdd 1 i))) (hc0 c))
    have h2 := sc_td_sub (sc_td_CX (σ := Fin (n + 1) ⊕ Fin 0) 2 (Sum.inl (Fin.natAdd n 0)))
      (sc_td_add (sc_td_sum _ fun i => sc_td_CX (q i) (Sum.inl (Fin.castAdd 1 i))) (hc0 c'))
    simp only [A, Bv]
    refine le_trans (totalDegree_mul _ _) ?_
    omega
  · intro a b
    have hev : MvPolynomial.eval (Sum.elim (pairVec a b) 0)
        ((C 2 * Bv - (∑ i, C (p i) * A i + C c)) * (C 2 * Bv - (∑ i, C (q i) * A i + C c')))
        = (2 * b 0 - (p ⬝ᵥ a + c)) * (2 * b 0 - (q ⬝ᵥ a + c')) := by
      simp only [A, Bv, map_mul, map_sub, map_add, map_sum, eval_C, eval_X, Sum.elim_inl, pairVec_left,
        pairVec_right, dotProduct]
    rw [hev]
    have hdiff : (2 : ℤ) ∣ p ⬝ᵥ a - q ⬝ᵥ a := by
      rw [← sub_dotProduct]
      exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (by simpa using hpq i) _
    have hb : b = f a ↔ b 0 = scalarOut f a := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; funext j; have hj : j = 0 := Subsingleton.elim j 0; subst hj; exact h
    rw [hb]
    obtain ⟨h1, h2⟩ := hF a
    constructor
    · intro hb0
      by_cases hd : (2 : ℤ) ∣ p ⬝ᵥ a + c
      · have := h1 hd; rw [hb0, this]; ring
      · have := h2 hd; rw [hb0, this]; ring
    · intro h0
      rcases mul_eq_zero.mp h0 with h0 | h0
      · have hd : (2 : ℤ) ∣ p ⬝ᵥ a + c := ⟨b 0, by linarith⟩
        have := h1 hd; linarith
      · have hd : ¬ (2 : ℤ) ∣ p ⬝ᵥ a + c := by
          intro hd; apply hcc
          have hq2 : (2 : ℤ) ∣ q ⬝ᵥ a + c' := ⟨b 0, by linarith⟩
          have e : c - c' = (p ⬝ᵥ a + c) - (q ⬝ᵥ a + c') - (p ⬝ᵥ a - q ⬝ᵥ a) := by ring
          rw [e]; exact dvd_sub (dvd_sub hd hq2) hdiff
        have := h2 hd; linarith

theorem singleQuadratic_of_scalarFamilies {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : CommonSlopeIntNF f ∨ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f)) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f := by
  have conv : ∀ P : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ, P.totalDegree ≤ 2 →
      (∀ (a : Fin n → ℤ) (b : Fin 1 → ℤ), b = f a ↔ MvPolynomial.eval (Sum.elim (pairVec a b) 0) P = 0) →
      DiophCompression.SingleQuadraticDefinableFunctionZZ f := by
    intro P hP hrep
    refine singleQuadratic_of_poly (W := Fin 0) P hP f (fun a b => ⟨fun hb => ⟨0, (hrep a b).mp hb⟩, ?_⟩)
    rintro ⟨w, hw⟩
    have hw0 : w = 0 := funext fun i => i.elim0
    rw [hw0] at hw
    exact (hrep a b).mpr hw
  rcases h with h | h | h
  · exact singleQuadratic_of_commonSlope h
  · obtain ⟨P, hP, hrep⟩ := zeroWitness_of_globalQuadratic h; exact conv P hP hrep
  · obtain ⟨P, hP, hrep⟩ := zeroWitness_of_parityAffine h; exact conv P hP hrep

theorem sealed_scalarFamilies_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n : ℕ) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), DiophCompression.SingleQuadraticDefinableFunctionZZ f →
      CommonSlopeIntNF f ∨ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f) := by
  intro n f hf
  rcases sealed_scalar_commonSlope_or_rn_of_TCER hT n f hf with h | ⟨a, β, d, E, φ, g, hR⟩
  · exact Or.inl h
  · exact Or.inr (rn_classify a β d E φ g hR)

theorem scalar_singleQuadratic_iff_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n : ℕ) (f : (Fin n → ℤ) → (Fin 1 → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔
        (CommonSlopeIntNF f ∨ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f)) :=
  fun n f => ⟨sealed_scalarFamilies_of_TCER hT n f, singleQuadratic_of_scalarFamilies⟩

theorem commonSlopeIntNF_of_zero_outputs {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) : CommonSlopeIntNF f :=
  ⟨1, 0, le_rfl, fun _ _ => funext fun j => j.elim0⟩

theorem singleQuadratic_iff_commonSlope_of_TCER_of_ne_one (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)), m ≠ 1 →
      (DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ CommonSlopeIntNF f) := by
  intro n m f hm
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 0 := by omega
    exact ⟨fun _ => commonSlopeIntNF_of_zero_outputs f, singleQuadratic_of_commonSlope⟩
  · exact singleQuadratic_iff_commonSlope_of_TCER hT n m f h

end DiophCompression.ResearchUpgrade
