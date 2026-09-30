/-
  DiophCompression/ComputableFunctions.lean — APAL Structural Theory Gate 2, kernel item 必須C
  (session 25, 2026-09-01, claude.ai direct, 0 CC).
  Total-function hierarchy: Fun(PP_2) ⊆ TotComp unconditionally (search on the graph system, Nat.rfind on a
  primitive-recursive checker), TotComp ⊆ Fun(PP_2) under DPRM_ZZ, Fun(PP_2) = Fun(SE_4) by Skolem reduction,
  Fun(PP_2) closed under composition (intermediate vector as fresh witnesses), Fun(SE_2) ⊊ TotComp via x³.
  Statements frozen in frozen_statements/ComputableFunctions_STATEMENTS.lean.
-/
import DiophCompression.ComputabilityFragments

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions -/

/-- TotComp: `f : ℤⁿ → ℤᵐ` is (total) computable. -/
def TotalComputableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop := Computable f

/-- Fun(PP_2): the graph of `f` is defined by a quadratic pp-system with integer witnesses. -/
def PPQuadraticDefinableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  WithinPPZZ 2 (graphVecZZ f)

/-- Fun(SE_4): the graph of `f` is defined by a single equation of total degree ≤ 4. -/
def SingleQuarticDefinableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  WithinSingleEquationZZ 4 (graphVecZZ f)

/-! ### Search on a Diophantine graph -/

/-- Boolean check: decode `c` as `(b, y)` and test `P(a ++ b, y) = 0`. -/
noncomputable def graphCheck {n m r : ℕ} (P : Poly (n + m) r) (a : Fin n → ℤ) (c : ℕ) : Bool :=
  match @Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable c with
  | none => false
  | some bp => solTest P (Fin.append a bp.1) bp.2

/-- Output projection of a decoded pair `(b, y) ↦ b` (default `0`). -/
noncomputable def graphOut (m r : ℕ) (c : ℕ) : Fin m → ℤ :=
  match @Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable c with
  | none => 0
  | some bp => bp.1

theorem primrec_append_coord {n m : ℕ} (i : Fin (n + m)) :
    Primrec fun p : (Fin n → ℤ) × (Fin m → ℤ) => Fin.append p.1 p.2 i := by
  refine Fin.addCases (motive := fun i => Primrec fun p : (Fin n → ℤ) × (Fin m → ℤ) => Fin.append p.1 p.2 i)
    (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]
    exact Primrec.fin_app.comp Primrec.fst (Primrec.const i)
  · simp only [Fin.append_right]
    exact Primrec.fin_app.comp Primrec.snd (Primrec.const i)

theorem primrecPred_graphTest {n m r : ℕ} (P : Poly (n + m) r) :
    PrimrecPred fun q : ((Fin n → ℤ) × ℕ) × ((Fin m → ℤ) × (Fin r → ℤ)) =>
      evalAtZZ P (Fin.append q.1.1 q.2.1) q.2.2 = 0 := by
  have h := primrec_eval_of_coords P
    (fun q : ((Fin n → ℤ) × ℕ) × ((Fin m → ℤ) × (Fin r → ℤ)) => Sum.elim (Fin.append q.1.1 q.2.1) q.2.2)
    (fun i => by
      rcases i with i | i
      · exact (primrec_append_coord i).comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      · exact Primrec.fin_app.comp (Primrec.snd.comp Primrec.snd) (Primrec.const i))
  exact Primrec.eq.comp h (Primrec.const 0)

theorem primrec₂_graphCheck {n m r : ℕ} (P : Poly (n + m) r) : Primrec₂ (graphCheck P) := by
  have h := Primrec.option_casesOn (α := (Fin n → ℤ) × ℕ) (β := (Fin m → ℤ) × (Fin r → ℤ)) (σ := Bool)
    (o := fun p => @Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable p.2)
    (f := fun _ => false) (g := fun p bp => solTest P (Fin.append p.1 bp.1) bp.2)
    (Primrec.decode.comp Primrec.snd) (Primrec.const false)
    ((primrecPred_graphTest P).decide.to₂)
  refine h.of_eq ?_
  rintro ⟨a, c⟩
  simp only [graphCheck]
  rcases @Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable c with _ | bp <;> rfl

theorem primrec_graphOut (m r : ℕ) : Primrec (graphOut m r) := by
  have h := Primrec.option_casesOn (α := ℕ) (β := (Fin m → ℤ) × (Fin r → ℤ)) (σ := Fin m → ℤ)
    (o := fun c => @Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable c)
    (f := fun _ => (0 : Fin m → ℤ)) (g := fun _ bp => bp.1)
    Primrec.decode (Primrec.const 0) (Primrec.fst.comp Primrec.snd).to₂
  refine h.of_eq fun c => ?_
  simp only [graphOut]
  rcases @Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable c with _ | bp <;> rfl

theorem graphCheck_true_iff {n m r : ℕ} (P : Poly (n + m) r) (a : Fin n → ℤ) (c : ℕ) :
    graphCheck P a c = true ↔ ∃ bp : (Fin m → ℤ) × (Fin r → ℤ),
      @Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable c = some bp ∧
        evalAtZZ P (Fin.append a bp.1) bp.2 = 0 := by
  unfold graphCheck
  rcases hdec : (@Encodable.decode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable c) with _ | bp
  · simp
  · simp [solTest]

/-- Unconditional: a total function with a Diophantine graph is computable. -/
theorem computable_of_withinDiophZZ_graph {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (h : WithinDiophZZ (graphVecZZ f)) : Computable f := by
  obtain ⟨r, P, hrep⟩ := h
  have hrf : Partrec fun a : Fin n → ℤ => Nat.rfind fun c => (Part.some (graphCheck P a c) : Part Bool) :=
    Partrec.rfind (primrec₂_graphCheck P).to_comp.partrec
  have hpart : Partrec fun a : Fin n → ℤ =>
      (Nat.rfind fun c => (Part.some (graphCheck P a c) : Part Bool)).map (graphOut m r) :=
    hrf.map ((primrec_graphOut m r).comp Primrec.snd).to₂.to_comp
  refine hpart.of_eq_tot fun a => ?_
  have hmem : Fin.append a (f a) ∈ graphVecZZ f := (mem_graphVecZZ_append f a (f a)).2 rfl
  obtain ⟨y, hy⟩ := (hrep _).1 hmem
  have hc : graphCheck P a (@Encodable.encode ((Fin m → ℤ) × (Fin r → ℤ)) Primcodable.toEncodable (f a, y))
      = true :=
    (graphCheck_true_iff P a _).2 ⟨(f a, y), @Encodable.encodek _ Primcodable.toEncodable _, hy⟩
  have hdom : (Nat.rfind fun c => (Part.some (graphCheck P a c) : Part Bool)).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨_, Part.mem_some_iff.mpr hc.symm, fun {_} _ => trivial⟩
  rw [Part.mem_map_iff]
  refine ⟨(Nat.rfind _).get hdom, Part.get_mem hdom, ?_⟩
  have hspec := Nat.rfind_spec (Part.get_mem hdom)
  have htrue : graphCheck P a ((Nat.rfind _).get hdom) = true := (Part.mem_some_iff.mp hspec).symm
  obtain ⟨bp, hdec, hz⟩ := (graphCheck_true_iff P a _).1 htrue
  have hb : bp.1 = f a := (mem_graphVecZZ_append f a bp.1).1 ((hrep _).2 ⟨bp.2, hz⟩)
  unfold graphOut
  rw [hdec]
  exact hb

/-! ### Computable functions have recursive graphs -/

theorem computablePred_graphVecZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (hf : Computable f) :
    ComputablePred fun v => v ∈ graphVecZZ f := by
  have hL : Primrec fun v : Fin (n + m) → ℤ => fun i => v (Fin.castAdd m i) := by
    refine Primrec.fin_curry.2 ?_
    refine Primrec.fin_app.comp Primrec.fst ?_
    refine Primrec.fin_val_iff.1 ?_
    exact (Primrec.fin_val.comp Primrec.snd).of_eq fun _ => rfl
  have hR : Primrec fun v : Fin (n + m) → ℤ => fun j => v (Fin.natAdd n j) := by
    refine Primrec.fin_curry.2 ?_
    refine Primrec.fin_app.comp Primrec.fst ?_
    refine Primrec.fin_val_iff.1 ?_
    exact (Primrec.nat_add.comp (Primrec.const n) (Primrec.fin_val.comp Primrec.snd)).of_eq fun _ => rfl
  have hdec : Computable fun v : Fin (n + m) → ℤ =>
      decide ((fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd m i))) :=
    ((Primrec.eq (α := Fin m → ℤ)).decide.to_comp).comp hR.to_comp (hf.comp hL.to_comp)
  refine ComputablePred.computable_iff.2 ⟨_, hdec, ?_⟩
  funext v
  simp [graphVecZZ]

/-! ### Composition: intermediate vector as fresh witnesses -/

section Composition

variable {n m l r₁ r₂ : ℕ}

def slotB (m r₁ r₂ : ℕ) (j : Fin m) : Fin (m + r₁ + r₂) := Fin.castAdd r₂ (Fin.castAdd r₁ j)
def slotY₁ (m r₁ r₂ : ℕ) (t : Fin r₁) : Fin (m + r₁ + r₂) := Fin.castAdd r₂ (Fin.natAdd m t)
def slotY₂ (m r₁ r₂ : ℕ) (t : Fin r₂) : Fin (m + r₁ + r₂) := Fin.natAdd (m + r₁) t

/-- Variable map for the first system: inputs of `f` stay inputs, outputs of `f` become witnesses. -/
def compφ₁ (n m l r₁ r₂ : ℕ) : Fin (n + m) ⊕ Fin r₁ → Fin (n + l) ⊕ Fin (m + r₁ + r₂)
  | Sum.inl x => Fin.addCases (fun i => Sum.inl (Fin.castAdd l i)) (fun j => Sum.inr (slotB m r₁ r₂ j)) x
  | Sum.inr t => Sum.inr (slotY₁ m r₁ r₂ t)

/-- Variable map for the second system: inputs of `g` are the witness slots, outputs stay outputs. -/
def compφ₂ (n m l r₁ r₂ : ℕ) : Fin (m + l) ⊕ Fin r₂ → Fin (n + l) ⊕ Fin (m + r₁ + r₂)
  | Sum.inl x => Fin.addCases (fun j => Sum.inr (slotB m r₁ r₂ j)) (fun q => Sum.inl (Fin.natAdd n q)) x
  | Sum.inr t => Sum.inr (slotY₂ m r₁ r₂ t)

theorem compφ₁_elim (v : Fin (n + l) → ℤ) (w : Fin (m + r₁ + r₂) → ℤ) :
    Sum.elim v w ∘ compφ₁ n m l r₁ r₂ =
      Sum.elim (Fin.append (fun i => v (Fin.castAdd l i)) (fun j => w (slotB m r₁ r₂ j)))
        (fun t => w (slotY₁ m r₁ r₂ t)) := by
  funext x
  rcases x with x | t
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · simp [compφ₁, Fin.append_left]
    · simp [compφ₁, Fin.append_right]
  · rfl

theorem compφ₂_elim (v : Fin (n + l) → ℤ) (w : Fin (m + r₁ + r₂) → ℤ) :
    Sum.elim v w ∘ compφ₂ n m l r₁ r₂ =
      Sum.elim (Fin.append (fun j => w (slotB m r₁ r₂ j)) (fun q => v (Fin.natAdd n q)))
        (fun t => w (slotY₂ m r₁ r₂ t)) := by
  funext x
  rcases x with x | t
  · refine Fin.addCases (fun j => ?_) (fun q => ?_) x
    · simp [compφ₂, Fin.append_left]
    · simp [compφ₂, Fin.append_right]
  · rfl

theorem evalAtZZ_rename_compφ₁ (Q : Poly (n + m) r₁) (v : Fin (n + l) → ℤ) (w : Fin (m + r₁ + r₂) → ℤ) :
    evalAtZZ (rename (compφ₁ n m l r₁ r₂) Q) v w =
      evalAtZZ Q (Fin.append (fun i => v (Fin.castAdd l i)) (fun j => w (slotB m r₁ r₂ j)))
        (fun t => w (slotY₁ m r₁ r₂ t)) := by
  simp only [evalAtZZ, eval_rename, compφ₁_elim]

theorem evalAtZZ_rename_compφ₂ (Q : Poly (m + l) r₂) (v : Fin (n + l) → ℤ) (w : Fin (m + r₁ + r₂) → ℤ) :
    evalAtZZ (rename (compφ₂ n m l r₁ r₂) Q) v w =
      evalAtZZ Q (Fin.append (fun j => w (slotB m r₁ r₂ j)) (fun q => v (Fin.natAdd n q)))
        (fun t => w (slotY₂ m r₁ r₂ t)) := by
  simp only [evalAtZZ, eval_rename, compφ₂_elim]

/-- The composed system: both systems renamed, outputs of `f` = inputs of `g` = fresh witnesses. -/
noncomputable def compSys {m₁ m₂ : ℕ} (S₁ : PolySystem (n + m) r₁ m₁) (S₂ : PolySystem (m + l) r₂ m₂) :
    PolySystem (n + l) (m + r₁ + r₂) (m₁ + m₂) :=
  Fin.append (fun i => rename (compφ₁ n m l r₁ r₂) (S₁ i)) (fun j => rename (compφ₂ n m l r₁ r₂) (S₂ j))

theorem compSys_sol_iff {m₁ m₂ : ℕ} (S₁ : PolySystem (n + m) r₁ m₁) (S₂ : PolySystem (m + l) r₂ m₂)
    (v : Fin (n + l) → ℤ) (w : Fin (m + r₁ + r₂) → ℤ) :
    (∀ i, evalAtZZ (compSys S₁ S₂ i) v w = 0) ↔
      (∀ i, evalAtZZ (S₁ i) (Fin.append (fun i => v (Fin.castAdd l i)) (fun j => w (slotB m r₁ r₂ j)))
          (fun t => w (slotY₁ m r₁ r₂ t)) = 0) ∧
      (∀ j, evalAtZZ (S₂ j) (Fin.append (fun j => w (slotB m r₁ r₂ j)) (fun q => v (Fin.natAdd n q)))
          (fun t => w (slotY₂ m r₁ r₂ t)) = 0) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := h (Fin.castAdd m₂ i)
      simpa only [compSys, Fin.append_left, evalAtZZ_rename_compφ₁] using this
    · have := h (Fin.natAdd m₁ j)
      simpa only [compSys, Fin.append_right, evalAtZZ_rename_compφ₂] using this
  · rintro ⟨h₁, h₂⟩ i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [compSys, Fin.append_left, evalAtZZ_rename_compφ₁] using h₁ i
    · simpa only [compSys, Fin.append_right, evalAtZZ_rename_compφ₂] using h₂ j

end Composition

/-! ### Theorems (frozen) -/

/-- Unconditional: a PP_2-definable total function is computable (search on the graph system). -/
theorem ppQuadratic_total_function_computable {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (h : PPQuadraticDefinableFunctionZZ f) : TotalComputableFunctionZZ f :=
  computable_of_withinDiophZZ_graph f (withinDiophZZ_of_withinPPZZ h)

/-- Unconditional: an SE_2-definable total function is computable. -/
theorem singleQuadratic_total_function_computable {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (h : SingleQuadraticDefinableFunctionZZ f) : TotalComputableFunctionZZ f :=
  computable_of_withinDiophZZ_graph f (withinDiophZZ_of_withinSingleEquationZZ h)

/-- Conditional on DPRM: every total computable function is PP_2-definable. -/
theorem computable_total_function_ppQuadratic_of_DPRM (hD : DPRM_ZZ) {n m : ℕ}
    (f : (Fin n → ℤ) → (Fin m → ℤ)) (h : TotalComputableFunctionZZ f) :
    PPQuadraticDefinableFunctionZZ f :=
  withinPPZZ_two_of_withinDiophZZ (hD _ _ (computablePred_graphVecZZ f h).to_re)

/-- Conditional on DPRM: Fun(PP_2) = TotComp. -/
theorem ppQuadratic_functions_eq_totalComputable_of_DPRM (hD : DPRM_ZZ) {n m : ℕ}
    (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    PPQuadraticDefinableFunctionZZ f ↔ TotalComputableFunctionZZ f :=
  ⟨ppQuadratic_total_function_computable f, computable_total_function_ppQuadratic_of_DPRM hD f⟩

/-- Unconditional: Fun(PP_2) = Fun(SE_4) (Skolem degree reduction). -/
theorem ppQuadratic_functions_eq_singleQuartic {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f :=
  ⟨fun h => withinSingleEquationZZ_double_of_withinPPZZ h,
   fun h => withinPPZZ_two_of_withinDiophZZ (withinDiophZZ_of_withinSingleEquationZZ h)⟩

/-- Unconditional: PP_2-definable functions are closed under composition (intermediate vector as
    fresh witnesses). -/
theorem ppQuadratic_functions_closed_under_composition {n m l : ℕ}
    (f : (Fin n → ℤ) → (Fin m → ℤ)) (g : (Fin m → ℤ) → (Fin l → ℤ))
    (hf : PPQuadraticDefinableFunctionZZ f) (hg : PPQuadraticDefinableFunctionZZ g) :
    PPQuadraticDefinableFunctionZZ (g ∘ f) := by
  obtain ⟨r₁, m₁, S₁, hdeg₁, hrep₁⟩ := hf
  obtain ⟨r₂, m₂, S₂, hdeg₂, hrep₂⟩ := hg
  refine ⟨m + r₁ + r₂, m₁ + m₂, compSys S₁ S₂, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [compSys, Fin.append_left]
      exact (totalDegree_rename_le _ _).trans (hdeg₁ i)
    · simp only [compSys, Fin.append_right]
      exact (totalDegree_rename_le _ _).trans (hdeg₂ j)
  · intro v
    have hv : v ∈ graphVecZZ (g ∘ f) ↔
        (fun q => v (Fin.natAdd n q)) = g (f (fun i => v (Fin.castAdd l i))) := Iff.rfl
    rw [hv]
    constructor
    · intro hcg
      obtain ⟨y₁, hy₁⟩ := (hrep₁ _).1 ((mem_graphVecZZ_append f _ (f _)).2 rfl)
      obtain ⟨y₂, hy₂⟩ := (hrep₂ _).1 ((mem_graphVecZZ_append g _ _).2 hcg)
      refine ⟨Fin.append (Fin.append (f (fun i => v (Fin.castAdd l i))) y₁) y₂, (compSys_sol_iff S₁ S₂ v _).2 ⟨?_, ?_⟩⟩
      · simpa only [slotB, slotY₁, Fin.append_left, Fin.append_right] using hy₁
      · simpa only [slotB, slotY₂, Fin.append_left, Fin.append_right] using hy₂
    · rintro ⟨w, hw⟩
      obtain ⟨h₁, h₂⟩ := (compSys_sol_iff S₁ S₂ v w).1 hw
      have hb := (mem_graphVecZZ_append f _ _).1 ((hrep₁ _).2 ⟨_, h₁⟩)
      have hc := (mem_graphVecZZ_append g _ _).1 ((hrep₂ _).2 ⟨_, h₂⟩)
      exact hc.trans (congrArg g hb)

/-- Unconditional: Fun(SE_2) ⊊ TotComp — `x ↦ x³` is computable and not SE_2-definable. -/
theorem singleQuadratic_functions_proper_subset_totalComputable :
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f →
      TotalComputableFunctionZZ f) ∧
    ∃ f : (Fin 1 → ℤ) → (Fin 1 → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f := by
  refine ⟨fun f h => singleQuadratic_total_function_computable f h,
    fun a (_ : Fin 1) => (a 0) ^ 3, ?_, ?_⟩
  · refine (Primrec.fin_curry.2 ?_).to_comp
    exact (primrec_int_pow 3).comp (Primrec.fin_app.comp Primrec.fst (Primrec.const 0))
  · intro h
    refine cubic_graph_not_withinSingleEquationZZ 0 ?_
    rw [powerGraphZZ, ← graphVecZZ_one_eq_graphZZ]
    exact h

/-- The function phase diagram (DPRM): TotComp = Fun(PP_2) = Fun(SE_4), Fun(SE_2) ⊊ TotComp,
    and Fun(PP_2) is composition-closed. -/
theorem function_phase_diagram (hD : DPRM_ZZ) :
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f) ∧
    (∃ f : (Fin 1 → ℤ) → (Fin 1 → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f) ∧
    (∀ {n m l : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (g : (Fin m → ℤ) → (Fin l → ℤ)),
      PPQuadraticDefinableFunctionZZ f → PPQuadraticDefinableFunctionZZ g →
        PPQuadraticDefinableFunctionZZ (g ∘ f)) :=
  ⟨fun f => (ppQuadratic_functions_eq_totalComputable_of_DPRM hD f).symm,
   fun f => ppQuadratic_functions_eq_singleQuartic f,
   singleQuadratic_functions_proper_subset_totalComputable.2,
   fun f g hf hg => ppQuadratic_functions_closed_under_composition f g hf hg⟩

#print axioms DiophCompression.computable_of_withinDiophZZ_graph
#print axioms DiophCompression.computablePred_graphVecZZ
#print axioms DiophCompression.compSys_sol_iff
#print axioms DiophCompression.ppQuadratic_total_function_computable
#print axioms DiophCompression.singleQuadratic_total_function_computable
#print axioms DiophCompression.computable_total_function_ppQuadratic_of_DPRM
#print axioms DiophCompression.ppQuadratic_functions_eq_totalComputable_of_DPRM
#print axioms DiophCompression.ppQuadratic_functions_eq_singleQuartic
#print axioms DiophCompression.ppQuadratic_functions_closed_under_composition
#print axioms DiophCompression.singleQuadratic_functions_proper_subset_totalComputable
#print axioms DiophCompression.function_phase_diagram

end DiophCompression
