/-
  WitnessCount.lean — s60.  GPT R48 Packet B (GATE30): short consequences of the R48 classification.

  * `SingleQuadraticWithWitnessesZZ` (the sealed predicate with the number r of witnesses fixed),
    `singleQuadratic_iff_exists_witnesses`, `graphData_of_witnesses` [P].
  * `scalar_rn_of_polarRank_le_one` [P] — the TCER-free branches of the scalar classification (Q ≡ 0, polar rank one).
  * `zeroWitness_iff` [P] (B1) — without witnesses a scalar function is SE₂ iff it is a global rational quadratic or
    parity-affine.  No TCER.
  * `UniqueWitnessSingleQuadraticZZ`, `existsUnique_of_uniqueWitness`, `uniqueWitness_of_commonSlope`,
    `uniqueWitness_of_zeroWitness` [P], `singleQuadratic_iff_uniqueWitness_of_TCER` [C] (B2) — every SE₂ function has a
    presentation with unique witnesses (TCER in the forward direction only).  Not a claim about every presentation.
  * `floorThird`, `floorThirdPoly`, `floorThird_oneWitness`, `floorThirdPoly_two_witnesses`, `floorThird_not_zeroWitness`,
    `floorThird_min_witnesses` [P] (B3, B4) — a ↦ ⌊a/3⌋ needs exactly one witness in the single-quadratic format.

  Statements frozen before proof (`~/lean/s60_evidence/freeze/H4_FREEZE_s60.lean` 557ff43b, ruling of Dr. Fukui
  2026-09-28 13:00).  TCER is an explicit hypothesis, never an axiom.  The statements follow GPT R48 CLAUDE_R48_NEXT_TASKS
  B1–B4 and TWO_SHORT_COROLLARIES_R48; novelty is not claimed here.
-/
import ResearchUpgrade.SlopeStructure

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial

def SingleQuadraticWithWitnessesZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (r : ℕ) : Prop :=
  ∃ P : MPUP.Poly (n + m) r, P.totalDegree ≤ 2 ∧ DiophCompression.RepresentsZZ P (DiophCompression.graphVecZZ f)

theorem singleQuadratic_iff_exists_witnesses {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ ∃ r, SingleQuadraticWithWitnessesZZ f r :=
  ⟨fun h => h, fun h => h⟩

theorem graphData_of_witnesses {n m r : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : SingleQuadraticWithWitnessesZZ f r) : ∃ D : QuadraticGraphData n m r, D.Defines f := by
  classical
  obtain ⟨P, hdeg, hrep⟩ := h
  set P' : MvPolynomial (Vars n m r) ℤ := rename unsplit P with hP'
  have hdeg' : P'.totalDegree ≤ 2 := le_trans (totalDegree_rename_le _ _) hdeg
  obtain ⟨q, hq⟩ := IntQuad.isQuadRep_of_totalDegree_le_two P' hdeg'
  refine ⟨⟨q⟩, ?_⟩
  intro a b
  have hval : ∀ u : Fin r → ℤ,
      (⟨q⟩ : QuadraticGraphData n m r).P.eval (pt a b u)
        = DiophCompression.evalAtZZ P (pairVec a b) u := by
    intro u
    show q.eval (pt a b u) = _
    rw [hq (pt a b u), hP', eval_rename, pt_comp_unsplit]
    rfl
  constructor
  · rintro ⟨u, hu⟩
    have hu' : (⟨q⟩ : QuadraticGraphData n m r).P.eval (pt a b u) = 0 := hu
    rw [hval u] at hu'
    exact (mem_graphVecZZ_pairVec f a b).mp ((hrep (pairVec a b)).mpr ⟨u, hu'⟩)
  · intro hb
    obtain ⟨u, hu⟩ := (hrep (pairVec a b)).mp ((mem_graphVecZZ_pairVec f a b).mpr hb)
    refine ⟨u, ?_⟩
    show (⟨q⟩ : QuadraticGraphData n m r).P.eval (pt a b u) = 0
    rw [hval u]
    exact hu

theorem scalar_rn_of_polarRank_le_one :
    ∀ (n r : ℕ) (D : QuadraticGraphData n 1 r) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), D.Defines f → D.polarRank ≤ 1 →
      ∃ (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ),
        ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = scalarOut f x := by
  classical
  intro n r D f hf hr1
  by_cases hz : ∀ x : OutWit 1 r → ℚ, D.zQuadQ x = 0
  · have hpol := D.zPolar_eq_zero_of_zQuadQ_zero hz
    refine ⟨D.lbA, D.lbBeta, D.lbD, D.lbE, D.lbPhi, D.lbG, fun x y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · exact congrFun ((hf x _).mp (D.graph_of_rn_linear hpol hf hy)) 0
    · rw [hy]; exact D.rn_of_sol_linear hpol hf x
  have hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0 := D.exists_int_zQuad_ne_zero hz
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

theorem zeroWitness_iff {n : ℕ} (f : (Fin n → ℤ) → (Fin 1 → ℤ)) :
    SingleQuadraticWithWitnessesZZ f 0 ↔ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f) := by
  classical
  constructor
  · intro h
    obtain ⟨D, hD⟩ := graphData_of_witnesses h
    have hr : D.polarRank ≤ 1 := by have := D.polarRank_le; omega
    obtain ⟨a, β, d, E, φ, g, hR⟩ := scalar_rn_of_polarRank_le_one n 0 D f hD hr
    exact rn_classify a β d E φ g hR
  · intro h
    have conv : ∀ P : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ, P.totalDegree ≤ 2 →
        (∀ (a : Fin n → ℤ) (b : Fin 1 → ℤ), b = f a ↔ MvPolynomial.eval (Sum.elim (pairVec a b) 0) P = 0) →
        SingleQuadraticWithWitnessesZZ f 0 := by
      intro P hP hrep
      refine ⟨P, hP, fun v => ?_⟩
      have hvp : v = pairVec (fun i => v (Fin.castAdd 1 i)) (fun j => v (Fin.natAdd n j)) := by
        funext k
        induction k using Fin.addCases with
        | left i => simp
        | right j => simp
      show (fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd 1 i)) ↔ _
      rw [hrep, ← hvp]
      unfold DiophCompression.evalAtZZ
      constructor
      · intro h0; exact ⟨0, h0⟩
      · rintro ⟨y, hy⟩
        have hy0 : y = 0 := funext fun i => i.elim0
        rw [hy0] at hy; exact hy
    rcases h with h | h
    · obtain ⟨P, hP, hrep⟩ := zeroWitness_of_globalQuadratic h; exact conv P hP hrep
    · obtain ⟨P, hP, hrep⟩ := zeroWitness_of_parityAffine h; exact conv P hP hrep

def UniqueWitnessSingleQuadraticZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ r, ∃ P : MPUP.Poly (n + m) r, P.totalDegree ≤ 2 ∧ DiophCompression.RepresentsZZ P (DiophCompression.graphVecZZ f) ∧
    ∀ (v : Fin (n + m) → ℤ) (y y' : Fin r → ℤ),
      DiophCompression.evalAtZZ P v y = 0 → DiophCompression.evalAtZZ P v y' = 0 → y = y'

theorem existsUnique_of_uniqueWitness {n m r : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (P : MPUP.Poly (n + m) r)
    (hrep : DiophCompression.RepresentsZZ P (DiophCompression.graphVecZZ f))
    (hu : ∀ (v : Fin (n + m) → ℤ) (y y' : Fin r → ℤ),
      DiophCompression.evalAtZZ P v y = 0 → DiophCompression.evalAtZZ P v y' = 0 → y = y')
    (a : Fin n → ℤ) :
    ∃! p : (Fin m → ℤ) × (Fin r → ℤ), DiophCompression.evalAtZZ P (pairVec a p.1) p.2 = 0 := by
  obtain ⟨u, hu0⟩ := (hrep (pairVec a (f a))).mp ((mem_graphVecZZ_pairVec f a (f a)).mpr rfl)
  refine ⟨(f a, u), hu0, ?_⟩
  rintro ⟨b, w⟩ hw
  change DiophCompression.evalAtZZ P (pairVec a b) w = 0 at hw
  have hb : b = f a := (mem_graphVecZZ_pairVec f a b).mp ((hrep (pairVec a b)).mpr ⟨w, hw⟩)
  subst hb
  exact Prod.ext rfl (hu _ _ _ hw hu0)

theorem uniqueWitness_of_commonSlope {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : CommonSlopeIntNF f) :
    UniqueWitnessSingleQuadraticZZ f := by
  classical
  obtain ⟨M, B, β, hM, hgraph, huniq, -⟩ := commonSlope_posDef_presentation h
  have hcard : Fintype.card (Fin n ⊕ (Fin n → Fin M)) = n + M ^ n := by
    simp [Fintype.card_sum]
  let eqv : (Fin n ⊕ (Fin n → Fin M)) ≃ Fin (n + M ^ n) := Fintype.equivFinOfCardEq hcard
  have hv : ∀ (v : Fin (n + m) → ℤ) (y : Fin (n + M ^ n) → ℤ),
      DiophCompression.evalAtZZ (MvPolynomial.rename (Sum.map id eqv) (slopeEncoder M B β)) v y
        = MvPolynomial.eval (Sum.elim v (y ∘ eqv)) (slopeEncoder M B β) := by
    intro v y
    unfold DiophCompression.evalAtZZ
    rw [MvPolynomial.eval_rename]
    have hx : (Sum.elim v y) ∘ (Sum.map id eqv) = Sum.elim v (y ∘ eqv) := by
      funext x; rcases x with x | w <;> rfl
    rw [hx]
  have hc : ∀ z : Fin (n + M ^ n) → ℤ,
      z ∘ eqv = Sum.elim (fun i => z (eqv (Sum.inl i))) (fun ρ => z (eqv (Sum.inr ρ))) := by
    intro z; funext x; rcases x with i | ρ <;> rfl
  have hvp : ∀ v : Fin (n + m) → ℤ,
      v = pairVec (fun i => v (Fin.castAdd m i)) (fun j => v (Fin.natAdd n j)) := by
    intro v
    funext k
    induction k using Fin.addCases with
    | left i => simp
    | right j => simp
  refine ⟨n + M ^ n, MvPolynomial.rename (Sum.map id eqv) (slopeEncoder M B β),
    le_trans (MvPolynomial.totalDegree_rename_le _ _) (slopeEncoder_totalDegree _ _ _), ?_, ?_⟩
  · intro v
    show (fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd m i)) ↔ _
    rw [hgraph, ← hvp v]
    constructor
    · rintro ⟨u, e, h0⟩
      refine ⟨(Sum.elim u e) ∘ eqv.symm, ?_⟩
      have hce : ((Sum.elim u e) ∘ eqv.symm) ∘ eqv = Sum.elim u e := by funext x; simp
      rw [hv, hce]; exact h0
    · rintro ⟨y, hy⟩
      refine ⟨fun i => y (eqv (Sum.inl i)), fun ρ => y (eqv (Sum.inr ρ)), ?_⟩
      rw [hv, hc] at hy
      exact hy
  · intro v y y' hy hy'
    rw [hv, hc, hvp v] at hy hy'
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ _ _ hy hy'
    funext k
    obtain ⟨x, rfl⟩ := eqv.surjective k
    rcases x with i | ρ
    · exact congrFun h1 i
    · exact congrFun h2 ρ

theorem uniqueWitness_of_zeroWitness {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : SingleQuadraticWithWitnessesZZ f 0) :
    UniqueWitnessSingleQuadraticZZ f := by
  obtain ⟨P, hP, hrep⟩ := h
  exact ⟨0, P, hP, hrep, fun _ _ _ _ _ => funext fun i => i.elim0⟩

theorem singleQuadratic_iff_uniqueWitness_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ UniqueWitnessSingleQuadraticZZ f := by
  intro n m f
  constructor
  · intro hf
    by_cases hm : m = 1
    · subst hm
      rcases sealed_scalarFamilies_of_TCER hT n f hf with h | h | h
      · exact uniqueWitness_of_commonSlope h
      · exact uniqueWitness_of_zeroWitness ((zeroWitness_iff f).mpr (Or.inl h))
      · exact uniqueWitness_of_zeroWitness ((zeroWitness_iff f).mpr (Or.inr h))
    · exact uniqueWitness_of_commonSlope ((singleQuadratic_iff_commonSlope_of_TCER_of_ne_one hT n m f hm).mp hf)
  · rintro ⟨r, P, hP, hrep, -⟩
    exact ⟨r, P, hP, hrep⟩

def floorThird : (Fin 1 → ℤ) → (Fin 1 → ℤ) := fun a _ => a 0 / 3

noncomputable def floorThirdPoly : MPUP.Poly (1 + 1) 1 :=
  (C 3 * X (Sum.inl 1) - X (Sum.inl 0) + 1) ^ 2 + X (Sum.inr 0) ^ 2 - 1

theorem floorThirdPoly_eval (v : Fin (1 + 1) → ℤ) (y : Fin 1 → ℤ) :
    DiophCompression.evalAtZZ floorThirdPoly v y = (3 * v 1 - v 0 + 1) ^ 2 + y 0 ^ 2 - 1 := by
  unfold DiophCompression.evalAtZZ floorThirdPoly
  simp

theorem floorThird_oneWitness : SingleQuadraticWithWitnessesZZ floorThird 1 := by
  refine ⟨floorThirdPoly, ?_, fun v => ?_⟩
  · unfold floorThirdPoly
    exact sc_td_sub (sc_td_add (sc_td_sq (sc_td_add (sc_td_sub (sc_td_CX 3 _) (sc_td_X _)) sc_td_one))
      (sc_td_sq (sc_td_X _))) (le_trans sc_td_one (by norm_num))
  · show (fun j => v (Fin.natAdd 1 j)) = floorThird (fun i => v (Fin.castAdd 1 i)) ↔ _
    have e0 : (Fin.castAdd 1 (0 : Fin 1) : Fin (1 + 1)) = 0 := rfl
    have e1 : (Fin.natAdd 1 (0 : Fin 1) : Fin (1 + 1)) = 1 := rfl
    have hL : (fun j => v (Fin.natAdd 1 j)) = floorThird (fun i => v (Fin.castAdd 1 i)) ↔ v 1 = v 0 / 3 := by
      constructor
      · intro h; have := congrFun h 0; simpa [floorThird, e0, e1] using this
      · intro h; funext j; have hj : j = 0 := Subsingleton.elim j 0; subst hj; simpa [floorThird, e0, e1] using h
    rw [hL]
    simp only [floorThirdPoly_eval]
    constructor
    · intro h
      by_cases h1 : v 0 % 3 = 1
      · refine ⟨fun _ => 1, ?_⟩
        have : 3 * v 1 - v 0 + 1 = 0 := by omega
        rw [this]; norm_num
      · refine ⟨fun _ => 0, ?_⟩
        have : 3 * v 1 - v 0 + 1 = 1 ∨ 3 * v 1 - v 0 + 1 = -1 := by omega
        rcases this with h' | h' <;> rw [h'] <;> norm_num
    · rintro ⟨y, hy⟩
      have hsq : (3 * v 1 - v 0 + 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0)]
      have hlo : -1 ≤ 3 * v 1 - v 0 + 1 := by nlinarith
      have hhi : 3 * v 1 - v 0 + 1 ≤ 1 := by nlinarith
      omega

theorem floorThirdPoly_two_witnesses :
    DiophCompression.evalAtZZ floorThirdPoly (pairVec (fun _ => 1) (fun _ => 0)) (fun _ => 1) = 0 ∧
    DiophCompression.evalAtZZ floorThirdPoly (pairVec (fun _ => 1) (fun _ => 0)) (fun _ => -1) = 0 := by
  have e0 : pairVec (fun _ : Fin 1 => (1 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) 0 = 1 := rfl
  have e1 : pairVec (fun _ : Fin 1 => (1 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) 1 = 0 := rfl
  simp only [floorThirdPoly_eval, e0, e1]
  norm_num

theorem floorThird_not_zeroWitness : ¬ SingleQuadraticWithWitnessesZZ floorThird 0 := by
  intro h
  have hF : ∀ x : ℤ, scalarOut floorThird (fun _ => x) = x / 3 := fun x => rfl
  rcases (zeroWitness_iff floorThird).mp h with ⟨q, hq⟩ | ⟨p, q, c, c', -, ⟨i, hi⟩, -, hpar⟩
  · have hv : ∀ x : ℤ, ((x / 3 : ℤ) : ℚ) = q.c + q.l 0 * x + q.Q 0 0 * (x * x) := by
      intro x
      rw [← hF x, hq]
      simp [QuadForm.eval, dotProduct, castQ, Matrix.mulVec]
      ring
    have h0 := hv 0; have h1 := hv 1; have h2 := hv 2; have h3 := hv 3
    norm_num at h0 h1 h2 h3
    linarith
  · have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    have hd : ∀ x : ℤ, p ⬝ᵥ (fun _ => x) = p 0 * x := fun x => by simp [dotProduct]
    have hA := hpar (fun _ => 0); have hB := hpar (fun _ => 1)
    have hC := hpar (fun _ => 6); have hD := hpar (fun _ => 7)
    simp only [hd, hF] at hA hB hC hD
    norm_num at hA hB hC hD
    rcases Int.emod_two_eq_zero_or_one c with hc | hc
    · have e1 : (2 : ℤ) ∣ c := Int.dvd_of_emod_eq_zero hc
      have e2 : (2 : ℤ) ∣ p 0 * 6 + c := by
        rcases e1 with ⟨k, hk⟩; exact ⟨p 0 * 3 + k, by rw [hk]; ring⟩
      have a1 := hA.1 e1; have a2 := hC.1 e2
      omega
    · have e1 : (2 : ℤ) ∣ p 0 + c := by omega
      have e2 : (2 : ℤ) ∣ p 0 * 7 + c := by omega
      have a1 := hB.1 e1; have a2 := hD.1 e2
      omega

theorem floorThird_min_witnesses :
    SingleQuadraticWithWitnessesZZ floorThird 1 ∧ ¬ SingleQuadraticWithWitnessesZZ floorThird 0 :=
  ⟨floorThird_oneWitness, floorThird_not_zeroWitness⟩

end DiophCompression.ResearchUpgrade
