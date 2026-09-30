/-
  frozen_statements/ResearchUpgrade_STATEMENTS.lean — r40 statement freeze (s49, 2026-09-13, agora).

  The s48 research results: the thirteen Lean roots that submission/native/PAPER_CLAIMS.tsv cites
  from the THIRD library `ResearchUpgrade` (sources lean/ResearchUpgrade/, namespace
  DiophCompression.ResearchUpgrade).  The names are the ones listed in
  lean/scripts/paper_claim_extra_roots.txt and each was checked against
  logs/ru_axioms.log of the r40 clean room before this file was written.

  Every statement below is the production statement VERBATIM (declaration keyword up to the first
  `:=`); bodies are `sorry`.  This file is the frozen contract, not a build target: it is never
  compiled — tools/statement_diff.py locates the production declaration of the same name and
  compares the statement text, and tools/paper_claims_check.py takes its root list from here.

  Production provenance, per block:
    DimensionII_D.lean   : QuadraticGraphData.dim_le_of_defines
    Summit.lean          : QuadraticGraphData.summit_of_defines, dim_le_of_summit,
                           dim_le_of_defines_via_summit
    FidelityBridge.lean  : singleQuadratic_injective_dimension_sharp, singleQuadratic_sharp_iff,
                           atomGraphZZ_le_one, not_atomGraphZZ_two, atomGraphZZ_capacity_eq_one,
                           natInput_intInput_separation_at_two
    PadGraph.lean        : exists_graph_injective_pad
    ParityWitness.lean   : parity_exists_unique, parity_not_quadratic
-/
import ResearchUpgrade.DimensionII_D
import ResearchUpgrade.Summit
import ResearchUpgrade.FidelityBridge
import ResearchUpgrade.PadGraph
import ResearchUpgrade.ParityWitness

namespace DiophCompression.ResearchUpgrade

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### II-D and the summit, stated on the graph data -/

namespace QuadraticGraphData

theorem dim_le_of_defines {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hinj : Function.Injective f) : n ≤ m := by sorry

theorem summit_of_defines {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f ∨ WeakVectorCosetNF f := by sorry

end QuadraticGraphData

/-! ### The summit disjunction as the single branch boundary -/

theorem dim_le_of_summit {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hsum : LinearGrowth f ∨ WeakVectorCosetNF f) (hinj : Function.Injective f) : n ≤ m := by sorry

theorem dim_le_of_defines_via_summit {n m r : ℕ} (D : QuadraticGraphData n m r)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) : n ≤ m := by
  sorry

/-! ### The fidelity bridge onto the sealed predicate -/

theorem singleQuadratic_injective_dimension_sharp {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : DiophCompression.SingleQuadraticDefinableFunctionZZ f)
    (hinj : Function.Injective f) : n ≤ m := by sorry

theorem singleQuadratic_sharp_iff (n m : ℕ) :
    (∃ f : (Fin n → ℤ) → (Fin m → ℤ),
        DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ Function.Injective f) ↔ n ≤ m := by
  sorry

/-! ### The r39 Appendix-B open problem: ca(SE₂) = 1 -/

theorem atomGraphZZ_le_one : ∀ n, DiophCompression.AtomGraphZZ 2 n → n ≤ 1 := by sorry

theorem atomGraphZZ_capacity_eq_one :
    DiophCompression.AtomGraphZZ 1 1 ∧ ∀ n, DiophCompression.AtomGraphZZ 2 n → n ≤ 1 := by sorry

theorem not_atomGraphZZ_two : ¬ DiophCompression.AtomGraphZZ 2 2 := by sorry

/-! ### The ℕ / ℤ boundary (regression control #25, as a theorem) -/

theorem natInput_intInput_separation_at_two :
    DiophCompression.AtomGraphZ 2 2 ∧ ¬ DiophCompression.AtomGraphZZ 2 2 := by sorry

/-! ### Sharpness: the bound is attained for every n ≤ m -/

theorem exists_graph_injective_pad (n m : ℕ) (h : n ≤ m) :
    ∃ (D : QuadraticGraphData n m 0) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      D.Defines f ∧ Function.Injective f := by sorry

/-! ### The parity witness: output-unique, not a rational quadratic -/

theorem parity_exists_unique (a : ℤ) :
    ∃! b : ℤ, 4 * b ^ 2 - (4 * a + 2) * b + (a ^ 2 + a) = 0 := by sorry

theorem parity_not_quadratic {f : ℤ → ℤ}
    (hf : ∀ a : ℤ, 4 * (f a) ^ 2 - (4 * a + 2) * (f a) + (a ^ 2 + a) = 0) :
    ¬ ∃ c₀ c₁ c₂ : ℚ, ∀ a : ℤ, ((f a : ℚ)) = c₀ + c₁ * (a : ℚ) + c₂ * (a : ℚ) ^ 2 := by sorry

end DiophCompression.ResearchUpgrade

/-! ## r41/s52/s53 extension (s53, 2026-09-16, agora; Dr. Fukui ruling "すべてok").
Statements of every `theorem`/`def` in the sixteen modules below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [r41] ResearchUpgrade/AffineNormalForm.lean  md5 5b71c271d4607d223704eadd7dc4bbd2
def FullVectorCosetNF {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop := sorry

theorem weakVectorCosetNF_of_fullVectorCosetNF {n m : ℕ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : FullVectorCosetNF f) : WeakVectorCosetNF f := by sorry

theorem fullVectorCosetNF_of_m_zero {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) :
    FullVectorCosetNF f := by sorry

theorem affine_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    ∀ (a : Fin n → ℤ) (j : Fin m),
      ((f a j : ℤ) : ℚ) = c₀ (Sum.inl j) + ∑ i, (a i : ℚ) * cs i (Sum.inl j) := by sorry

theorem fullVectorCosetNF_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    FullVectorCosetNF f := by sorry

theorem fullVectorCosetNF_of_isotropic_fallback
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    WeakVectorCosetNF f := by sorry

-- [r41] ResearchUpgrade/FourSquareSlack.lean  md5 afd2fc5e361ebfd2e6da1d69ba1573ab
theorem exists_four_squares {N : ℤ} (hN : 0 ≤ N) :
    ∃ u : Fin 4 → ℤ, ∑ i, (u i) ^ 2 = N := by sorry

def lin (a : Fin n → ℤ) (j : Fin m) : ℤ := sorry

def Sol (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin 4 → ℤ) : Prop := sorry

def Graph (a : Fin n → ℤ) (b : Fin m → ℤ) : Prop := sorry

def Total : Prop := sorry

def OutputUnique : Prop := sorry

theorem k_pos : 0 < F.k := by sorry

theorem R_nonneg (hT : F.Total) (a : Fin n → ℤ) : 0 ≤ F.R a := by sorry

theorem sum_le_of_termwise {a : Fin n → ℤ} {b : Fin m → ℤ}
    (h : ∀ j, (F.k * b j - F.lin a j) ^ 2 ≤ F.k ^ 2) :
    (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ (m : ℤ) * F.k ^ 2 := by sorry

theorem R_lt (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique) (a : Fin n → ℤ) :
    F.R a < (m : ℤ) * F.k ^ 2 := by sorry

theorem residual_bounded (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique) (a : Fin n → ℤ) :
    0 ≤ F.R a ∧ F.R a < (m : ℤ) * F.k ^ 2 := by sorry

theorem m_zero_counterexample :
    ∃ F : Family 1 0, F.Total ∧ F.OutputUnique ∧ ¬ ∀ a, F.R a < (0 : ℤ) * F.k ^ 2 := by sorry

theorem line_coeffs_zero {α β γ C : ℤ} (h : ∀ t : ℤ, |γ + β * t + α * t ^ 2| ≤ C) :
    α = 0 ∧ β = 0 := by sorry

theorem eval_smul {n : ℕ} (P : IntQuad (Fin n)) (v : Fin n → ℤ) (t : ℤ) :
    P.eval (t • v) = P.c + (P.l ⬝ᵥ v) * t + (v ⬝ᵥ (P.Q *ᵥ v)) * t ^ 2 := by sorry

theorem const_of_bounded {n : ℕ} (P : IntQuad (Fin n)) {C : ℤ}
    (h : ∀ x : Fin n → ℤ, |P.eval x| ≤ C) (x : Fin n → ℤ) : P.eval x = P.c := by sorry

theorem R_const (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique)
    {P : IntQuad (Fin n)} (hR : ∀ a, F.R a = P.eval a) (a : Fin n → ℤ) :
    F.R a = F.R 0 := by sorry

theorem lin_translate (a t : Fin n → ℤ) (j : Fin m) :
    F.lin (a + F.k • t) j = F.lin a j + F.k * ∑ i, F.B j i * t i := by sorry

theorem graph_translate (hconst : ∀ a, F.R a = F.R 0)
    {a : Fin n → ℤ} {b : Fin m → ℤ} (h : F.Graph a b) (t : Fin n → ℤ) :
    F.Graph (a + F.k • t) (fun j => b j + ∑ i, F.B j i * t i) := by sorry

theorem output_translate (hU : F.OutputUnique) (hconst : ∀ a, F.R a = F.R 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a, F.Graph a (f a)) (a t : Fin n → ℤ) :
    f (a + F.k • t) = fun j => f a j + ∑ i, F.B j i * t i := by sorry

theorem fullVectorCosetNF_of_constant_residual (hU : F.OutputUnique)
    (hconst : ∀ a, F.R a = F.R 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a, F.Graph a (f a)) :
    FullVectorCosetNF f := by sorry

theorem fullVectorCosetNF_of_intQuad_residual (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique)
    {P : IntQuad (Fin n)} (hR : ∀ a, F.R a = P.eval a)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a, F.Graph a (f a)) :
    FullVectorCosetNF f := by sorry

theorem sq_le_one_iff (x : ℤ) : x ^ 2 ≤ 1 ↔ -1 ≤ x ∧ x ≤ 1 := by sorry

def Ex : Family 1 1 := sorry

theorem Ex_sol_iff (a b : Fin 1 → ℤ) (u : Fin 4 → ℤ) :
    Ex.Sol a b u ↔ (3 * b 0 - a 0) ^ 2 + ∑ i, (u i) ^ 2 = 1 := by sorry

theorem Ex_total : Ex.Total := by sorry

theorem Ex_outputUnique : Ex.OutputUnique := by sorry

theorem Ex_value (a b : Fin 1 → ℤ) : Ex.Graph a b ↔ b 0 = (a 0 + 1) / 3 := by sorry

theorem Ex_witness_not_unique :
    ∃ (a b : Fin 1 → ℤ) (u u' : Fin 4 → ℤ), u ≠ u' ∧ Ex.Sol a b u ∧ Ex.Sol a b u' := by sorry

theorem Ex_not_global_quadratic :
    ¬ ∃ c₀ c₁ c₂ : ℚ, ∀ a : ℤ, (((a + 1) / 3 : ℤ) : ℚ) = c₀ + c₁ * (a : ℚ) + c₂ * (a : ℚ) ^ 2 := by sorry

theorem Ex_fullVectorCosetNF :
    FullVectorCosetNF (fun a : Fin 1 → ℤ => fun _ : Fin 1 => (a 0 + 1) / 3) := by sorry

-- [r41] ResearchUpgrade/Reduction.lean  md5 4e03aba9e7268ca630e38e76a9ba2638
def GeneralWeakNF : Prop := sorry

def SemidefiniteWeakNF : Prop := sorry

theorem weakVectorCosetNF_of_isotropicBranch
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    WeakVectorCosetNF f := by sorry

theorem weakVectorCosetNF_of_quotientAnisotropicBranch
    (hm : 0 < m) (hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0)
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {pp qq : OutWit m r → ℚ} (hpp : 0 < D.zQuadQ pp) (hqq : D.zQuadQ qq < 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    WeakVectorCosetNF f := by sorry

theorem weakVectorCosetNF_of_semidefiniteWeakNF (H : SemidefiniteWeakNF)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakVectorCosetNF f := by sorry

theorem generalWeakNF_iff_semidefiniteWeakNF : GeneralWeakNF ↔ SemidefiniteWeakNF := by sorry

-- [r41] ResearchUpgrade/Controls.lean  md5 1eba8c0fe6cdb291c483b1725fd2a9fb
theorem eq_zero_of_abs_mul_nat_bounded {x c : ℝ} (h : ∀ N : ℕ, |x| * (N : ℝ) ≤ c) : x = 0 := by sorry

theorem real_line_coeffs_zero {α β γ C : ℝ}
    (h : ∀ t : ℤ, |γ + β * (t : ℝ) + α * (t : ℝ) ^ 2| ≤ C) : α = 0 ∧ β = 0 := by sorry

noncomputable def sqrt2Floor : (Fin 1 → ℤ) → ℤ := sorry

theorem sqrt2Floor_bound (x : Fin 1 → ℤ) : |sqrt2Floor x| ≤ 2 * |x 0| + 1 := by sorry

theorem sqrt2Floor_not_weakScalarCosetNF : ¬ WeakScalarCosetNF sqrt2Floor := by sorry

-- [r41] ResearchUpgrade/ReverseCompiler.lean  md5 0b1f8063d47d40ea2789d404ff9d96a6
noncomputable def IntQuad.toMv (q : IntQuad ι) : MvPolynomial ι ℤ := sorry

theorem IntQuad.eval_toMv (q : IntQuad ι) (x : ι → ℤ) :
    MvPolynomial.eval x q.toMv = q.eval x := by sorry

theorem IntQuad.totalDegree_toMv (q : IntQuad ι) : q.toMv.totalDegree ≤ 2 := by sorry

theorem intQuad_iff_totalDegree_le_two (g : (ι → ℤ) → ℤ) :
    (∃ q : IntQuad ι, ∀ x, q.eval x = g x) ↔
      (∃ P : MvPolynomial ι ℤ, P.totalDegree ≤ 2 ∧ ∀ x, MvPolynomial.eval x P = g x) := by sorry

-- [r41] ResearchUpgrade/RankOne.lean  md5 638d196c959c42ed10c98a3dc9abb8ae
noncomputable def outIndicator {m r : ℕ} (j : Fin m) : OutWit m r → ℚ := sorry

theorem outCoord_w₀_ne_zero
    (hm : 0 < m) (hOU : D.OutputUnique) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀)) :
    ∃ j : Fin m, w₀ (Sum.inl j) ≠ 0 := by sorry

theorem m_le_one_of_polarRankOne
    (hOU : D.OutputUnique) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀)) :
    m ≤ 1 := by sorry

theorem witnessDir_inRadicalQ
    (hm : 0 < m) (hOU : D.OutputUnique) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀))
    {x : OutWit m r → ℚ} (hx : ∀ j : Fin m, x (Sum.inl j) = 0) :
    D.InRadicalQ x := by sorry

theorem weakVectorCosetNF_of_polarRankOne_m_zero
    {D' : QuadraticGraphData n 0 r} {f : (Fin n → ℤ) → (Fin 0 → ℤ)} :
    WeakVectorCosetNF f := by sorry

def RankOneNoWitnessCompiler : Prop := sorry

-- [s52] ResearchUpgrade/WitnessInvariance.lean  md5 da22f8eb4c1578afa35f6d54e8e645ed
theorem zQuadQ_eq_zero_of_inRadicalQ {v : OutWit m r → ℚ} (hv : D.InRadicalQ v) :
    D.zQuadQ v = 0 := by sorry

theorem eval_witness_invariant
    (hm : 0 < m) (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit m r → ℚ, (∀ j : Fin m, x (Sum.inl j) = 0) → D.InRadicalQ x)
    (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) :
    D.P.eval (pt a b u) = D.P.eval (pt a b (0 : Fin r → ℤ)) := by sorry

theorem eval_witness_invariant_one {n r : ℕ} (D : QuadraticGraphData n 1 r)
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x)
    (a : Fin n → ℤ) (b : Fin 1 → ℤ) (u : Fin r → ℤ) :
    D.P.eval (pt a b u) = D.P.eval (pt a b (0 : Fin r → ℤ)) := by sorry

-- [s52] ResearchUpgrade/NoWitnessCompiler.lean  md5 2a72fd14eb175f0703f821ce34d1b596
theorem eval_zeroWitness_eq_Pn (x : Fin n → ℤ) (y : ℤ) :
    D.P.eval (pt x (fun _ => y) (0 : Fin r → ℤ))
      = Pn (D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)))
           (fun i => D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0))
                   + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i))
           (D.P.l (Sum.inr (Sum.inl 0)))
           (fun i j => D.P.Q (Sum.inl i) (Sum.inl j))
           (fun i => D.P.l (Sum.inl i))
           D.P.c x y := by sorry

def inclNoWit : Vars n 1 0 → Vars n 1 r := sorry

def noWitnessData : QuadraticGraphData n 1 0 := sorry

theorem noWitnessData_eval (x : Fin n → ℤ) (y : ℤ) (u : Fin 0 → ℤ) :
    (D.noWitnessData).P.eval (pt x (fun _ => y) u)
      = D.P.eval (pt x (fun _ => y) (0 : Fin r → ℤ)) := by sorry

theorem noWitnessData_graph_iff
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x)
    (a : Fin n → ℤ) (b : Fin 1 → ℤ) :
    D.Graph a b ↔ (D.noWitnessData).Graph a b := by sorry

theorem noWitnessData_defines
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x)
    {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) :
    (D.noWitnessData).Defines f := by sorry

theorem noWitnessData_total
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x) :
    (D.noWitnessData).Total := by sorry

theorem noWitnessData_outputUnique
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x) :
    (D.noWitnessData).OutputUnique := by sorry

-- [s52] ResearchUpgrade/RankOneConfluence.lean  md5 1442bea5f254e1c1bcf285ea30cba548
theorem fullVectorCosetNF_of_scalar {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : FullCosetNF (scalarOut f)) : FullVectorCosetNF f := by sorry

theorem fullVectorCosetNF_of_defines {n : ℕ} (D : QuadraticGraphData n 1 0)
    {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) : FullVectorCosetNF f := by sorry

theorem fullVectorCosetNF_of_polarRankOne {n m r : ℕ} (D : QuadraticGraphData n m r)
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    FullVectorCosetNF f := by sorry

-- [s52] ResearchUpgrade/FamilySE2Bridge.lean  md5 9552b5748d9a4ae53ec3c049b1010b81
def familyData : QuadraticGraphData n m 4 := sorry

theorem familyData_zQuad (z : OutWit m 4 → ℤ) :
    (F.familyData PR).zQuad z
      = F.k ^ 2 * (∑ j, z (Sum.inl j) ^ 2) + ∑ i, z (Sum.inr i) ^ 2 := by sorry

theorem familyData_zLin_out (a : Fin n → ℤ) (j : Fin m) :
    (F.familyData PR).zLin a (Sum.inl j) = -2 * F.k * F.lin a j := by sorry

theorem familyData_zLin_wit (a : Fin n → ℤ) (i : Fin 4) :
    (F.familyData PR).zLin a (Sum.inr i) = 0 := by sorry

theorem familyData_aPart (a : Fin n → ℤ) :
    (F.familyData PR).aPart a = (∑ j, F.lin a j ^ 2) - PR.eval a := by sorry

theorem familyData_eval (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin 4 → ℤ) :
    (F.familyData PR).P.eval (pt a b u)
      = ((∑ j, (F.k * b j - F.lin a j) ^ 2) + (∑ i, u i ^ 2)) - PR.eval a := by sorry

theorem familyData_sol_iff (hR : ∀ a, F.R a = PR.eval a)
    (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin 4 → ℤ) :
    (F.familyData PR).Sol a b u ↔ F.Sol a b u := by sorry

theorem familyData_graph_iff (hR : ∀ a, F.R a = PR.eval a)
    (a : Fin n → ℤ) (b : Fin m → ℤ) :
    (F.familyData PR).Graph a b ↔ F.Graph a b := by sorry

theorem familyData_total (hR : ∀ a, F.R a = PR.eval a) (hT : F.Total) :
    (F.familyData PR).Total := by sorry

theorem familyData_outputUnique (hR : ∀ a, F.R a = PR.eval a) (hU : F.OutputUnique) :
    (F.familyData PR).OutputUnique := by sorry

theorem familyData_defines (hR : ∀ a, F.R a = PR.eval a)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a b, F.Graph a b ↔ b = f a) :
    (F.familyData PR).Defines f := by sorry

def ExResidual : IntQuad (Fin 1) := sorry

theorem ExResidual_eval (a : Fin 1 → ℤ) : ExResidual.eval a = 1 := by sorry

theorem Ex_hR : ∀ a, Ex.R a = ExResidual.eval a := by sorry

theorem Ex_bridge (a b : Fin 1 → ℤ) :
    (Ex.familyData ExResidual).Graph a b ↔ Ex.Graph a b := by sorry

theorem Ex_bridge_value (a b : Fin 1 → ℤ) :
    (Ex.familyData ExResidual).Graph a b ↔ b 0 = (a 0 + 1) / 3 := by sorry

-- [s52] ResearchUpgrade/BoxCriterion.lean  md5 30cc71048248da314006f6f7b2f79b13
theorem graph_iff_box (a : Fin n → ℤ) (b : Fin m → ℤ) :
    F.Graph a b ↔ (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a := by sorry

theorem not_graph_of_neg {a : Fin n → ℤ} (h : F.R a < 0) (b : Fin m → ℤ) : ¬ F.Graph a b := by sorry

theorem total_and_outputUnique_iff :
    (F.Total ∧ F.OutputUnique)
      ↔ ∀ a : Fin n → ℤ, ∃! b : Fin m → ℤ, (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a := by sorry

theorem box_coord_bound {a : Fin n → ℤ} {b : Fin m → ℤ}
    (h : (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a) (j : Fin m) :
    (F.k * b j - F.lin a j) ^ 2 ≤ F.R a := by sorry

theorem graph_shift {a a' : Fin n → ℤ} (d : Fin m → ℤ)
    (hlin : ∀ j, F.lin a' j = F.lin a j + F.k * d j) (hR : F.R a' = F.R a) (b : Fin m → ℤ) :
    F.Graph a' (b + d) ↔ F.Graph a b := by sorry

theorem defines_of_box_unique
    (h : ∀ a : Fin n → ℤ, ∃! b : Fin m → ℤ, (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a)
    (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : ∀ a, (∑ j, (F.k * f a j - F.lin a j) ^ 2) ≤ F.R a) :
    ∀ a b, F.Graph a b ↔ b = f a := by sorry

theorem Ex_box (a b : Fin 1 → ℤ) :
    Ex.Graph a b ↔ (∑ j, (Ex.k * b j - Ex.lin a j) ^ 2) ≤ Ex.R a := by sorry

-- [s52] ResearchUpgrade/N4Control.lean  md5 ec91bf60f939f3b82dacd8af26576d76
def D3 : QuadraticGraphData 1 1 0 := sorry

theorem D3_eval (a b : Fin 1 → ℤ) (u : Fin 0 → ℤ) :
    D3.P.eval (pt a b u) = (2 * b 0 - a 0) * (2 * b 0 + 3 * a 0 - 1) := by sorry

theorem D3_sol_iff (a b : Fin 1 → ℤ) (u : Fin 0 → ℤ) :
    D3.Sol a b u ↔ (2 * b 0 = a 0 ∨ 2 * b 0 = 1 - 3 * a 0) := by sorry

theorem D3_graph_iff (a b : Fin 1 → ℤ) :
    D3.Graph a b ↔ (2 * b 0 = a 0 ∨ 2 * b 0 = 1 - 3 * a 0) := by sorry

def f3 : (Fin 1 → ℤ) → (Fin 1 → ℤ) := sorry

theorem D3_defines : D3.Defines f3 := by sorry

theorem D3_total : D3.Total := by sorry

theorem D3_outputUnique : D3.OutputUnique := by sorry

theorem f3_even (t : ℤ) : f3 (fun _ => 2 * t) 0 = t := by sorry

theorem f3_odd (t : ℤ) : f3 (fun _ => 2 * t + 1) 0 = -3 * t - 1 := by sorry

theorem D3_no_uniform_translation :
    ¬ ∃ (M : ℤ) (s : ℤ), 1 ≤ M ∧
      ∀ a : Fin 1 → ℤ, f3 (fun j => a j + M) 0 = f3 a 0 + s := by sorry

theorem D3_completed_square (a b : ℚ) :
    4 * (b + (2 * a - 1) / 4) ^ 2 - (4 * a - 1) ^ 2 / 4
      = -3 * a ^ 2 + 4 * a * b + a + 4 * b ^ 2 - 2 * b := by sorry

theorem D3_residual_not_constant :
    ∃ a a' : ℚ, (4 * a - 1) ^ 2 / 4 ≠ (4 * a' - 1) ^ 2 / 4 := by sorry

theorem D3_double_centre_not_integral (a : ℤ) :
    ¬ ∃ z : ℤ, (z : ℚ) = -(2 * (a : ℚ) - 1) / 2 := by sorry

theorem D3_slope_even (t : ℤ) :
    f3 (fun _ => 2 * t + 2) 0 - f3 (fun _ => 2 * t) 0 = 1 := by sorry

theorem D3_slope_odd (t : ℤ) :
    f3 (fun _ => 2 * t + 3) 0 - f3 (fun _ => 2 * t + 1) 0 = -3 := by sorry

theorem D3_fullVectorCosetNF : FullVectorCosetNF f3 := by sorry

-- [s52] ResearchUpgrade/SaturatedLattice.lean  md5 5b29184db1aeb10385d485dc9d820753
def Saturated (N : Submodule ℤ (Fin r → ℤ)) : Prop := sorry

theorem smith_isUnit_of_saturated {N : Submodule ℤ (Fin r → ℤ)} (hsat : Saturated N)
    {n : ℕ} (snf : Module.Basis.SmithNormalForm N (Fin r) n) (i : Fin n) :
    IsUnit (snf.a i) := by sorry

-- [s53] ResearchUpgrade/RankExcessCompiler.lean  md5 f6b407f388f855cd48c5f5715661720c
def IntQuad.pull {ι κ : Type*} [Fintype ι] [Fintype κ] (P : IntQuad ι) (M : Matrix ι κ ℤ) :
    IntQuad κ := sorry

theorem IntQuad.eval_pull {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : IntQuad ι) (M : Matrix ι κ ℤ) (y : κ → ℤ) :
    (P.pull M).eval y = P.eval (M *ᵥ y) := by sorry

noncomputable def polarRank : ℕ := sorry

theorem finrank_outWit : Module.finrank ℚ (OutWit m r → ℚ) = m + r := by sorry

theorem polarRank_le : D.polarRank ≤ m + r := by sorry

def outProjQ : (OutWit m r → ℚ) →ₗ[ℚ] (Fin m → ℚ) := sorry

theorem ker_polar_le_ker_outProjQ (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    LinearMap.ker D.polarMapQ ≤ LinearMap.ker (outProjQ (m := by sorry

theorem m_le_polarRank (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) : m ≤ D.polarRank := by sorry

def witQ (u : Fin r → ℤ) : OutWit m r → ℚ := sorry

theorem witQ_add (u u' : Fin r → ℤ) : witQ (m := by sorry

theorem witQ_zsmul (c : ℤ) (u : Fin r → ℤ) : witQ (m := by sorry

theorem witQ_zero : witQ (m := by sorry

theorem inRadicalQ_add {v w : OutWit m r → ℚ} (hv : D.InRadicalQ v) (hw : D.InRadicalQ w) :
    D.InRadicalQ (v + w) := by sorry

theorem inRadicalQ_smul (lam : ℚ) {v : OutWit m r → ℚ} (hv : D.InRadicalQ v) :
    D.InRadicalQ (lam • v) := by sorry

def witRadLattice : Submodule ℤ (Fin r → ℤ) := sorry

theorem mem_witRadLattice {u : Fin r → ℤ} :
    u ∈ D.witRadLattice ↔ D.InRadicalQ (witQ (m := by sorry

theorem witRadLattice_saturated : SaturatedLattice.Saturated D.witRadLattice := by sorry

theorem eval_add_radWit (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (a : Fin n → ℤ) (b : Fin m → ℤ) (u u' : Fin r → ℤ) (hu' : u' ∈ D.witRadLattice) :
    D.P.eval (pt a b (u + u')) = D.P.eval (pt a b u) := by sorry

theorem witQ_injective : Function.Injective (witQ (m := by sorry

def witQHom : (Fin r → ℤ) →+ (OutWit m r → ℚ) := sorry

theorem witQ_sum {k : ℕ} (c : Fin k → ℤ) (v : Fin k → Fin r → ℤ) :
    witQ (m := by sorry

theorem snf_mem (i : Fin k) : S.bM (S.f i) ∈ D.witRadLattice := by sorry

theorem snf_span {u : Fin r → ℤ} (hu : u ∈ D.witRadLattice) :
    ∃ c : Fin k → ℤ, u = ∑ i, c i • S.bM (S.f i) := by sorry

noncomputable def snfSpanQ : (Fin k → ℚ) →ₗ[ℚ] (OutWit m r → ℚ) := sorry

theorem snfSpanQ_injective : Function.Injective (D.snfSpanQ S) := by sorry

theorem range_snfSpanQ (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    LinearMap.range (D.snfSpanQ S) = LinearMap.ker D.polarMapQ := by sorry

theorem polarRank_add_snfRank (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    D.polarRank + k = m + r := by sorry

def WitnessCompiler
    (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) : Prop := sorry

theorem exists_witnessCompiler (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    ∃ U, D.WitnessCompiler U := by sorry

noncomputable def substMap
    (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) :
    (Vars n m (D.polarRank - m) → ℤ) →ₗ[ℤ] (Vars n m r → ℤ) := sorry

noncomputable def compiledData
    (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) :
    QuadraticGraphData n m (D.polarRank - m) := sorry

theorem compiledData_eval (a : Fin n → ℤ) (b : Fin m → ℤ) (v : Fin (D.polarRank - m) → ℤ) :
    (D.compiledData U).P.eval (pt a b v) = D.P.eval (pt a b (U (Sum.elim v 0))) := by sorry

theorem compiledData_graph_iff (hU : D.WitnessCompiler U) (a : Fin n → ℤ) (b : Fin m → ℤ) :
    D.Graph a b ↔ (D.compiledData U).Graph a b := by sorry

theorem compiledData_defines (hU : D.WitnessCompiler U) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) : (D.compiledData U).Defines f := by sorry

theorem compiledData_total (hU : D.WitnessCompiler U) (hT : D.Total) :
    (D.compiledData U).Total := by sorry

theorem compiledData_outputUnique (hU : D.WitnessCompiler U) (hOU : D.OutputUnique) :
    (D.compiledData U).OutputUnique := by sorry

theorem compiledData_totalDegree_le_two :
    ∃ Pm : MvPolynomial (Vars n m (D.polarRank - m)) ℤ, Pm.totalDegree ≤ 2 ∧
      ∀ x, MvPolynomial.eval x Pm = (D.compiledData U).P.eval x := by sorry

theorem rankExcess_compiler (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    m ≤ D.polarRank ∧ D.polarRank ≤ m + r ∧
    ∃ U, D.WitnessCompiler U ∧
      (∀ a b, D.Graph a b ↔ (D.compiledData U).Graph a b) ∧
      (D.compiledData U).Defines f ∧
      ∃ Pm : MvPolynomial (Vars n m (D.polarRank - m)) ℤ, Pm.totalDegree ≤ 2 ∧
        ∀ x, MvPolynomial.eval x Pm = (D.compiledData U).P.eval x := by sorry

-- [s53] ResearchUpgrade/RankExcessControl.lean  md5 8dcd7d411bf22cde2927c6bfeefb88a0
def sEx : Vars 1 1 2 → ℤ := sorry

def tEx : Vars 1 1 2 → ℤ := sorry

def exD : QuadraticGraphData 1 1 2 := sorry

theorem exD_eval (a : Fin 1 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    exD.P.eval (pt a b u) = (b 0 - a 0) ^ 2 + (u 0 + u 1) ^ 2 := by sorry

theorem exD_graph_iff (a b : Fin 1 → ℤ) : exD.Graph a b ↔ b = a := by sorry

theorem exD_defines : exD.Defines id := by sorry

theorem exD_zQuad_ne_zero : ∃ v : OutWit 1 2 → ℤ, exD.zQuad v ≠ 0 := by sorry

theorem exD_zPolarQ (v w : OutWit 1 2 → ℚ) :
    exD.zPolarQ v w = 2 * (v (Sum.inl 0) * w (Sum.inl 0))
      + 2 * ((v (Sum.inr 0) + v (Sum.inr 1)) * (w (Sum.inr 0) + w (Sum.inr 1))) := by sorry

def eRad : OutWit 1 2 → ℚ := sorry

theorem exD_ker_eq : LinearMap.ker exD.polarMapQ = ℚ ∙ eRad := by sorry

theorem exD_polarRank : exD.polarRank = 2 := by sorry

theorem exD_compiled_witnessCount : exD.polarRank - 1 = 1 := by sorry

theorem exD_rankExcess :
    ∃ U, exD.WitnessCompiler U ∧
      (∀ a b, exD.Graph a b ↔ (exD.compiledData U).Graph a b) ∧
      (exD.compiledData U).Defines id := by sorry

def UEx : ((Fin 1 ⊕ Fin 1) → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) := sorry

theorem exD_eval_UEx (a b : Fin 1 → ℤ) (v w : Fin 1 → ℤ) :
    exD.P.eval (pt a b (UEx (Sum.elim v w))) = (b 0 - a 0) ^ 2 + (v 0) ^ 2 := by sorry

def oneWitD : QuadraticGraphData 1 1 1 := sorry

theorem oneWitD_eval (a b v : Fin 1 → ℤ) :
    oneWitD.P.eval (pt a b v) = (b 0 - a 0) ^ 2 + (v 0) ^ 2 := by sorry

theorem exD_graph_iff_oneWit (a b : Fin 1 → ℤ) : exD.Graph a b ↔ oneWitD.Graph a b := by sorry

def noWitD : QuadraticGraphData 1 1 0 := sorry

theorem noWitD_eval (a b : Fin 1 → ℤ) (u : Fin 0 → ℤ) :
    noWitD.P.eval (pt a b u) = b 0 - a 0 := by sorry

theorem noWitD_graph_iff (a b : Fin 1 → ℤ) : noWitD.Graph a b ↔ b = a := by sorry

theorem sameGraph_three_witnessCounts (a b : Fin 1 → ℤ) :
    (exD.Graph a b ↔ oneWitD.Graph a b) ∧ (exD.Graph a b ↔ noWitD.Graph a b) := by sorry

-- [s53] ResearchUpgrade/DefiniteReduction.lean  md5 71b707f200da18f6fd41d9be8ab531ed
def DefiniteWeakNF : Prop := sorry

def DefiniteWeakNF_oneOut_oneWit : Prop := sorry

theorem definiteWeakNF_oneOut_oneWit_of_definiteWeakNF (H : DefiniteWeakNF) :
    DefiniteWeakNF_oneOut_oneWit := by sorry

theorem toQ_zsmul (c : ℤ) (z : OutWit m r → ℤ) : toQ (c • z) = (c : ℚ) • toQ z := by sorry

theorem toQ_add' (z z' : OutWit m r → ℤ) : toQ (z + z') = toQ z + toQ z' := by sorry

theorem zQuad_zsmul (c : ℤ) (z : OutWit m r → ℤ) : D.zQuad (c • z) = c ^ 2 * D.zQuad z := by sorry

theorem zLinEval_zsmul (a : Fin n → ℤ) (c : ℤ) (z : OutWit m r → ℤ) :
    D.zLinEval a (c • z) = c * D.zLinEval a z := by sorry

theorem two_zQuad_eq (z : OutWit m r → ℤ) :
    2 * D.zQuad z = D.P.eval (Sum.elim 0 ((2 : ℤ) • z)) - 2 * D.P.eval (Sum.elim 0 z)
      + D.P.eval (Sum.elim 0 ((0 : ℤ) • z)) := by sorry

theorem zPolar_eq (v w : OutWit m r → ℤ) :
    D.zPolar v w = D.zQuad (v + w) - D.zQuad v - D.zQuad w := by sorry

theorem inRadicalQ_of_int {v : OutWit m r → ℚ} (h : ∀ x : OutWit m r → ℤ, D.zPolarQ v (toQ x) = 0) :
    D.InRadicalQ v := by sorry

def ExactWitnessCompiler : Prop := sorry

theorem exists_exactWitnessCompiler (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    ∃ U, D.ExactWitnessCompiler U := by sorry

def outMap (z : OutWit m (D.polarRank - m) → ℤ) : OutWit m r → ℤ := sorry

theorem outMap_add (z z' : OutWit m (D.polarRank - m) → ℤ) :
    D.outMap U (z + z') = D.outMap U z + D.outMap U z' := by sorry

theorem outMap_zsmul (c : ℤ) (z : OutWit m (D.polarRank - m) → ℤ) :
    D.outMap U (c • z) = c • D.outMap U z := by sorry

theorem compiled_evalZero (z : OutWit m (D.polarRank - m) → ℤ) :
    (D.compiledData U).P.eval (Sum.elim 0 z) = D.P.eval (Sum.elim 0 (D.outMap U z)) := by sorry

theorem compiled_zQuad (z : OutWit m (D.polarRank - m) → ℤ) :
    (D.compiledData U).zQuad z = D.zQuad (D.outMap U z) := by sorry

theorem compiled_zPolar (z z' : OutWit m (D.polarRank - m) → ℤ) :
    (D.compiledData U).zPolar z z' = D.zPolar (D.outMap U z) (D.outMap U z') := by sorry

theorem compiled_intRadical_eq_zero (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) {z : OutWit m (D.polarRank - m) → ℤ}
    (hz : ∀ z', (D.compiledData U).zPolar z z' = 0) : z = 0 := by sorry

theorem compiledData_nondegQ (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) : (D.compiledData U).NondegQ := by sorry

theorem compiledData_polarRank (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) : (D.compiledData U).polarRank = D.polarRank := by sorry

theorem compiledData_posDef (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) :
    ∀ u : OutWit m (D.polarRank - m) → ℚ, u ≠ 0 → 0 < (D.compiledData U).zQuadQ u := by sorry

theorem definite_reduction (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) :
    ∃ U, D.ExactWitnessCompiler U ∧ (D.compiledData U).Defines f ∧
      (D.compiledData U).polarRank = D.polarRank ∧
      ∀ u : OutWit m (D.polarRank - m) → ℚ, u ≠ 0 → 0 < (D.compiledData U).zQuadQ u := by sorry

theorem semidefiniteWeakNF_iff_definiteWeakNF : SemidefiniteWeakNF ↔ DefiniteWeakNF := by sorry

theorem generalWeakNF_iff_definiteWeakNF : GeneralWeakNF ↔ DefiniteWeakNF := by sorry

theorem exD_semidefinite : ∀ u : OutWit 1 2 → ℚ, 0 ≤ exD.zQuadQ u := by sorry

theorem exD_definite_reduction :
    ∃ U, exD.ExactWitnessCompiler U ∧ (exD.compiledData U).Defines id ∧
      (exD.compiledData U).polarRank = 2 ∧
      ∀ u : OutWit 1 (exD.polarRank - 1) → ℚ, u ≠ 0 → 0 < (exD.compiledData U).zQuadQ u := by sorry

-- s53 (second freeze, same ruling): R41-C1 standalone and R41-D1 sealed bridge.
-- [s53] ResearchUpgrade/SaturatedExtension.lean  md5 4275bc8cc33cf607519ec848bfe94c82
def intPart (K : Submodule ℚ (Fin r → ℚ)) : Submodule ℤ (Fin r → ℤ) := sorry

def latticeQ (u : Fin r → ℤ) : Fin r → ℚ := sorry

theorem mem_intPart {K : Submodule ℚ (Fin r → ℚ)} {u : Fin r → ℤ} :
    u ∈ intPart K ↔ latticeQ u ∈ K := by sorry

theorem latticeQ_injective : Function.Injective (latticeQ (r := by sorry

theorem latticeQ_zsmul (c : ℤ) (u : Fin r → ℤ) : latticeQ (c • u) = (c : ℚ) • latticeQ u := by sorry

theorem latticeQ_sum {k : ℕ} (c : Fin k → ℤ) (v : Fin k → Fin r → ℤ) :
    latticeQ (∑ i, c i • v i) = ∑ i, (c i : ℚ) • latticeQ (v i) := by sorry

theorem intPart_saturated (K : Submodule ℚ (Fin r → ℚ)) : Saturated (intPart K) := by sorry

theorem snf_mem_of_saturated (hsat : Saturated N) (i : Fin k) : S.bM (S.f i) ∈ N := by sorry

theorem snf_span_of {u : Fin r → ℤ} (hu : u ∈ N) :
    ∃ c : Fin k → ℤ, u = ∑ i, c i • S.bM (S.f i) := by sorry

noncomputable def spanQ : (Fin k → ℚ) →ₗ[ℚ] (Fin r → ℚ) := sorry

theorem spanQ_injective : Function.Injective (spanQ S) := by sorry

theorem range_spanQ (K : Submodule ℚ (Fin r → ℚ)) {k : ℕ}
    (S : Module.Basis.SmithNormalForm (intPart K) (Fin r) k) :
    LinearMap.range (spanQ S) = K := by sorry

theorem snfRank_eq (K : Submodule ℚ (Fin r → ℚ)) {k : ℕ}
    (S : Module.Basis.SmithNormalForm (intPart K) (Fin r) k) :
    k = Module.finrank ℚ K := by sorry

theorem finrank_intPart (K : Submodule ℚ (Fin r → ℚ)) :
    Module.finrank ℤ (intPart K) = Module.finrank ℚ K := by sorry

theorem exists_unimodular_extension (K : Submodule ℚ (Fin r → ℚ)) :
    ∃ U : ((Fin (r - Module.finrank ℚ K) ⊕ Fin (Module.finrank ℚ K)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ),
      (∀ w, U (Sum.elim 0 w) ∈ intPart K) ∧ (∀ u ∈ intPart K, ∃ w, u = U (Sum.elim 0 w)) := by sorry

theorem intPart_bot : intPart (⊥ : Submodule ℚ (Fin r → ℚ)) = ⊥ ∧
    Module.finrank ℚ (⊥ : Submodule ℚ (Fin r → ℚ)) = 0 := by sorry

theorem intPart_top : intPart (⊤ : Submodule ℚ (Fin r → ℚ)) = ⊤ ∧
    Module.finrank ℚ (⊤ : Submodule ℚ (Fin r → ℚ)) = r := by sorry

-- [s53] ResearchUpgrade/FamilySealedBridge.lean  md5 c8cf4bf146fe345583aa9671c97b2e43
theorem QuadraticGraphData.singleQuadraticDefinable_of_defines {n m r : ℕ}
    (D : QuadraticGraphData n m r) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f := by sorry

theorem familyData_totalDegree_le_two :
    ∃ P : MvPolynomial (Vars n m 4) ℤ, P.totalDegree ≤ 2 ∧
      ∀ x, MvPolynomial.eval x P = (F.familyData PR).P.eval x := by sorry

theorem singleQuadraticDefinable_of_family (hR : ∀ a, F.R a = PR.eval a)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a b, F.Graph a b ↔ b = f a) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f := by sorry

theorem Ex_singleQuadraticDefinable :
    DiophCompression.SingleQuadraticDefinableFunctionZZ
      (fun a : Fin 1 → ℤ => fun _ : Fin 1 => (a 0 + 1) / 3) := by sorry

/-! ## s54 extension (s54, 2026-09-16, agora; Dr. Fukui ruling "全てやる方向で").
Statements of every `theorem`/`def` in the three modules below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s54] ResearchUpgrade/NormLift.lean  md5 560389caf524dcb0dc21be9947f5629e
theorem exists_int_scale {n : ℕ} (x : Fin n → ℚ) :
    ∃ (d : ℕ) (y : Fin n → ℤ), 0 < d ∧ castQ y = (d : ℚ) • x := by sorry

theorem exists_int_scale_matrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ) :
    ∃ (N : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), 0 < N ∧
      ∀ i j, (A i j : ℚ) = (N : ℚ) ^ 2 * T i j := by sorry

theorem castQ_zero {n : ℕ} : castQ (0 : Fin n → ℤ) = 0 := by sorry

theorem square_values_rigidity {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ)
    (hsq : ∀ v : Fin n → ℤ, IsSquare (castQ v ⬝ᵥ (T *ᵥ castQ v))) :
    ∃ h : Fin n → ℚ, ∀ x : Fin n → ℚ, x ⬝ᵥ (T *ᵥ x) = (h ⬝ᵥ x) ^ 2 := by sorry

theorem castQ_intSmul {n : ℕ} (t : ℤ) (v : Fin n → ℤ) : castQ (t • v) = (t : ℚ) • castQ v := by sorry

theorem direction_discriminant_square {n : ℕ} (D c : ℚ) (hD : 0 < D) (ell : Fin n → ℚ)
    (H : Matrix (Fin n) (Fin n) ℚ)
    (hrep : ∀ x : Fin n → ℤ, ∃ X Y : ℚ,
      c + 2 * (ell ⬝ᵥ castQ x) + castQ x ⬝ᵥ (H *ᵥ castQ x) = X ^ 2 + D * Y ^ 2)
    (v : Fin n → ℤ) :
    IsSquare ((c * (castQ v ⬝ᵥ (H *ᵥ castQ v)) - (ell ⬝ᵥ castQ v) ^ 2) / D) := by sorry

def discMatrix {n : ℕ} (D c : ℚ) (ell : Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ := sorry

theorem discMatrix_form {n : ℕ} (D c : ℚ) (hD : D ≠ 0) (ell : Fin n → ℚ)
    (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    x ⬝ᵥ (discMatrix D c ell H *ᵥ x) = (c * (x ⬝ᵥ (H *ᵥ x)) - (ell ⬝ᵥ x) ^ 2) / D := by sorry

theorem norm_identity (D r0 s0 L K Q : ℚ) (hc : r0 ^ 2 + D * s0 ^ 2 ≠ 0)
    (hx : (r0 ^ 2 + D * s0 ^ 2) * Q - L ^ 2 = D * K ^ 2) :
    (r0 ^ 2 + D * s0 ^ 2) + 2 * L + Q
      = (r0 + 1 / (r0 ^ 2 + D * s0 ^ 2) * (r0 * L - D * s0 * K)) ^ 2
        + D * (s0 + 1 / (r0 ^ 2 + D * s0 ^ 2) * (s0 * L + r0 * K)) ^ 2 := by sorry

theorem norm_section {n : ℕ} (D r0 s0 : ℚ) (hD : 0 < D) (hc : 0 < r0 ^ 2 + D * s0 ^ 2)
    (ell : Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ)
    (hrep : ∀ x : Fin n → ℤ, ∃ X Y : ℚ,
      (r0 ^ 2 + D * s0 ^ 2) + 2 * (ell ⬝ᵥ castQ x) + castQ x ⬝ᵥ (H *ᵥ castQ x) = X ^ 2 + D * Y ^ 2) :
    ∃ rl sl : Fin n → ℚ, ∀ x : Fin n → ℚ,
      (r0 ^ 2 + D * s0 ^ 2) + 2 * (ell ⬝ᵥ x) + x ⬝ᵥ (H *ᵥ x)
        = (r0 + rl ⬝ᵥ x) ^ 2 + D * (s0 + sl ⬝ᵥ x) ^ 2 := by sorry

-- [s54] ResearchUpgrade/DefiniteBinary.lean  md5 dbb89079afcc36299a92600433e100dd
def binK1 : OutWit m r := sorry

def binK2 : OutWit m r := sorry

theorem k1_ne_k2 : binK1 e ≠ binK2 e := by sorry

def binQ (k k' : OutWit m r) : ℚ := sorry

theorem sum_two (F : OutWit m r → ℚ) : ∑ k, F k = F (binK1 e) + F (binK2 e) := by sorry

theorem zQuadQ_two (w : OutWit m r → ℚ) :
    D.zQuadQ w = D.binQ (binK1 e) (binK1 e) * w (binK1 e) ^ 2
      + (D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)) * w (binK1 e) * w (binK2 e)
      + D.binQ (binK2 e) (binK2 e) * w (binK2 e) ^ 2 := by sorry

theorem zPolarQ_two (v w : OutWit m r → ℚ) :
    D.zPolarQ v w = 2 * D.binQ (binK1 e) (binK1 e) * v (binK1 e) * w (binK1 e)
      + (D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)) * (v (binK1 e) * w (binK2 e) + v (binK2 e) * w (binK1 e))
      + 2 * D.binQ (binK2 e) (binK2 e) * v (binK2 e) * w (binK2 e) := by sorry

theorem zLinQ_two (a : Fin n → ℤ) (w : OutWit m r → ℚ) :
    D.zLinQ a w = (D.zLin a (binK1 e) : ℚ) * w (binK1 e) + (D.zLin a (binK2 e) : ℚ) * w (binK2 e) := by sorry

def binVec (x y : ℚ) : OutWit m r → ℚ := sorry

theorem vec1_k1 (x y : ℚ) : binVec e x y (binK1 e) = x := by sorry

theorem vec1_k2 (x y : ℚ) : binVec e x y (binK2 e) = y := by sorry

theorem alpha_pos (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    0 < D.binQ (binK1 e) (binK1 e) := by sorry

theorem disc_pos (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    0 < 4 * D.binQ (binK1 e) (binK1 e) * D.binQ (binK2 e) (binK2 e)
      - (D.binQ (binK1 e) (binK2 e) + D.binQ (binK2 e) (binK1 e)) ^ 2 := by sorry

def binAlp : ℚ := sorry

def binBet : ℚ := sorry

def binGam : ℚ := sorry

def binDel : ℚ := sorry

def lconst (k : OutWit m r) : ℚ := sorry

def lslope (k : OutWit m r) (i : Fin n) : ℚ := sorry

theorem zLin_cast (a : Fin n → ℤ) (k : OutWit m r) :
    (D.zLin a k : ℚ) = D.lconst k + ∑ i, D.lslope k i * (a i : ℚ) := by sorry

def cc0 (k : OutWit m r) : ℚ := sorry

def cL (k : OutWit m r) (i : Fin n) : ℚ := sorry

def binCentre (a : Fin n → ℤ) : OutWit m r → ℚ := sorry

theorem lin_comb (A B δ l1 l2 : ℚ) (s1 s2 t : Fin n → ℚ) :
    (A * (l1 + ∑ i, s1 i * t i) + B * (l2 + ∑ i, s2 i * t i)) / δ
      = (A * l1 + B * l2) / δ + ∑ i, (A * s1 i + B * s2 i) / δ * t i := by sorry

theorem centre_k1 (a : Fin n → ℤ) :
    D.binCentre e a (binK1 e) = (-2 * D.binGam e * D.zLin a (binK1 e) + D.binBet e * D.zLin a (binK2 e)) / D.binDel e := by sorry

theorem centre_k2 (a : Fin n → ℤ) :
    D.binCentre e a (binK2 e) = (D.binBet e * D.zLin a (binK1 e) + (-2 * D.binAlp e) * D.zLin a (binK2 e)) / D.binDel e := by sorry

theorem zPolarQ_two' (v w : OutWit m r → ℚ) :
    D.zPolarQ v w = 2 * D.binAlp e * v (binK1 e) * w (binK1 e)
      + D.binBet e * (v (binK1 e) * w (binK2 e) + v (binK2 e) * w (binK1 e))
      + 2 * D.binGam e * v (binK2 e) * w (binK2 e) := by sorry

theorem zQuadQ_two' (w : OutWit m r → ℚ) :
    D.zQuadQ w = D.binAlp e * w (binK1 e) ^ 2 + D.binBet e * w (binK1 e) * w (binK2 e)
      + D.binGam e * w (binK2 e) ^ 2 := by sorry

theorem centre_isCentre (hdel : D.binDel e ≠ 0) (a : Fin n → ℤ) : D.IsCentre a (D.binCentre e a) := by sorry

def binOuter (u v : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ := sorry

theorem outer_form (u v t : Fin n → ℚ) : t ⬝ᵥ (binOuter u v *ᵥ t) = (u ⬝ᵥ t) * (v ⬝ᵥ t) := by sorry

def binALin : Fin n → ℚ := sorry

def binAQuad : Matrix (Fin n) (Fin n) ℚ := sorry

theorem aPart_cast (a : Fin n → ℤ) :
    (D.aPart a : ℚ) = (D.P.c : ℚ) + D.binALin ⬝ᵥ castQ a + castQ a ⬝ᵥ (D.binAQuad *ᵥ castQ a) := by sorry

def vL (k : OutWit m r) : Fin n → ℚ := sorry

def residualForm : QuadForm n := sorry

theorem centre_eq (a : Fin n → ℤ) (k : OutWit m r) :
    D.binCentre e a k = D.cc0 e k + D.vL e k ⬝ᵥ castQ a := by sorry

theorem residual_eq (a : Fin n → ℤ) :
    D.residual a (D.binCentre e a) = (D.residualForm e).eval (castQ a) := by sorry

theorem binDiag (hα : D.binAlp e ≠ 0) (w : OutWit m r → ℚ) :
    D.zQuadQ w = D.binAlp e * ((w (binK1 e) + D.binBet e / (2 * D.binAlp e) * w (binK2 e)) ^ 2
      + D.binDel e / (4 * D.binAlp e ^ 2) * w (binK2 e) ^ 2) := by sorry

theorem binary_compiler_gen (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ (α β Δ : ℚ) (c0 : OutWit m r → ℚ) (L : OutWit m r → Fin n → ℚ) (Rq : QuadForm n),
      0 < α ∧ 0 < Δ ∧
      (∀ a, D.IsCentre a (fun k => c0 k + ∑ i, L k i * (a i : ℚ))) ∧
      (∀ a, D.residual a (fun k => c0 k + ∑ i, L k i * (a i : ℚ)) = Rq.eval (castQ a)) ∧
      ∀ w : OutWit m r → ℚ,
        D.zQuadQ w = α * ((w (binK1 e) + β * w (binK2 e)) ^ 2 + Δ * w (binK2 e) ^ 2) := by sorry

theorem two_cases (e : OutWit m r ≃ Fin 2) (k : OutWit m r) : k = binK1 e ∨ k = binK2 e := by sorry

theorem solZ_of_norm {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    {z : OutWit m r → ℤ} (h : D.zQuadQ (toQ z - c) = D.residual a c) : D.SolZ a z := by sorry

theorem exists_common_den {ι : Type*} [Fintype ι] (G : ι → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ g : ℤ, (M : ℚ) * G k = g := by sorry

theorem cen_add (c0 : OutWit m r → ℚ) (L : OutWit m r → Fin n → ℚ) (a0 : Fin n → ℤ)
    (M : ℕ) (t : Fin n → ℤ) (k : OutWit m r) :
    c0 k + ∑ i, L k i * ((a0 + (M : ℤ) • t) i : ℚ)
      = (c0 k + ∑ i, L k i * (a0 i : ℚ)) + (fun i => L k i) ⬝ᵥ castQ ((M : ℤ) • t) := by sorry

theorem weakVectorCosetNF_of_binary (e : OutWit m r ≃ Fin 2)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakVectorCosetNF f := by sorry

def eOW : OutWit 1 1 ≃ Fin 2 := sorry

def eTZ : OutWit 2 0 ≃ Fin 2 := sorry

theorem k1_eOW : binK1 eOW = (Sum.inl 0 : OutWit 1 1) := by sorry

theorem k2_eOW : binK2 eOW = (Sum.inr 0 : OutWit 1 1) := by sorry

theorem definite_binary_compiler {n : ℕ} (D : QuadraticGraphData n 1 1)
    (hpos : ∀ u : OutWit 1 1 → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ (α β Δ : ℚ) (c0 : OutWit 1 1 → ℚ) (L : OutWit 1 1 → Fin n → ℚ) (Rq : QuadForm n),
      0 < α ∧ 0 < Δ ∧
      (∀ a, D.IsCentre a (fun k => c0 k + ∑ i, L k i * (a i : ℚ))) ∧
      (∀ a, D.residual a (fun k => c0 k + ∑ i, L k i * (a i : ℚ)) = Rq.eval (castQ a)) ∧
      ∀ w : OutWit 1 1 → ℚ,
        D.zQuadQ w = α * ((w (Sum.inl 0) + β * w (Sum.inr 0)) ^ 2 + Δ * w (Sum.inr 0) ^ 2) := by sorry

theorem weakNF_of_small {n m r' : ℕ} (D : QuadraticGraphData n m r') (hmr : m + r' ≤ 2)
    (hm : 0 < m) (hpos : ∀ u : OutWit m r' → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakVectorCosetNF f := by sorry

theorem negGraph_zPolarQ {n m r : ℕ} (D : QuadraticGraphData n m r) (v w : OutWit m r → ℚ) :
    D.negGraph.zPolarQ v w = - D.zPolarQ v w := by sorry

theorem negGraph_polarRank {n m r : ℕ} (D : QuadraticGraphData n m r) :
    D.negGraph.polarRank = D.polarRank := by sorry

theorem definiteWeakNF_oneOut_oneWit_holds : DefiniteWeakNF_oneOut_oneWit := by sorry

def DefiniteWeakNF_twoOut_zeroWit : Prop := sorry

theorem definiteWeakNF_twoOut_zeroWit_holds : DefiniteWeakNF_twoOut_zeroWit := by sorry

def LowRankSemidefiniteWeakNF : Prop := sorry

theorem lowRankSemidefiniteWeakNF_holds : LowRankSemidefiniteWeakNF := by sorry

-- [s54] ResearchUpgrade/FourSquareFinite.lean  md5 2058bb3299e8abf48858fa89478e43fb
def dlt (k e : ℤ) : ℤ := sorry

def dist0 {m : ℕ} (k : ℤ) (η : Fin m → ℤ) : ℤ := sorry

def gap {m : ℕ} (k : ℤ) (η : Fin m → ℤ) : ℤ := sorry

def nearest (k e : ℤ) : ℤ := sorry

theorem dlt_nonneg : 0 ≤ dlt k e := by sorry

theorem two_dlt_le : 2 * dlt k e ≤ k := by sorry

theorem nearest_err : (k * nearest k e - e) ^ 2 = dlt k e ^ 2 := by sorry

theorem other_err : (k * (1 - nearest k e) - e) ^ 2 = (k - dlt k e) ^ 2 := by sorry

theorem dlt_le_err (s : ℤ) : dlt k e ^ 2 ≤ (k * s - e) ^ 2 := by sorry

theorem other_le_err (s : ℤ) (hs : s ≠ nearest k e) : (k - dlt k e) ^ 2 ≤ (k * s - e) ^ 2 := by sorry

theorem term_le_sq : k * (k - 2 * dlt k e) ≤ k * k := by sorry

theorem nearest_ne_other (k e : ℤ) : 1 - nearest k e ≠ nearest k e := by sorry

theorem gap_le {m : ℕ} (k : ℤ) (η : Fin m → ℤ) (j : Fin m) :
    gap k η ≤ k * (k - 2 * dlt k (η j)) := by sorry

theorem exists_term_le_gap {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) : ∃ j, k * (k - 2 * dlt k (η j)) ≤ gap k η := by sorry

theorem exists_term_eq_gap {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) : ∃ j, gap k η = k * (k - 2 * dlt k (η j)) := by sorry

def nearVec (k : ℤ) (η : Fin m → ℤ) : Fin m → ℤ := sorry

theorem nearVec_err : ∑ j, (k * nearVec k η j - η j) ^ 2 = dist0 k η := by sorry

theorem dist0_le (s : Fin m → ℤ) : dist0 k η ≤ ∑ j, (k * s j - η j) ^ 2 := by sorry

theorem far_of_ne (s : Fin m → ℤ) (hs : s ≠ nearVec k η) :
    ∃ j, dist0 k η + k * (k - 2 * dlt k (η j)) ≤ ∑ j, (k * s j - η j) ^ 2 := by sorry

theorem second_point (j : Fin m) :
    ∑ i, (k * Function.update (nearVec k η) j (1 - nearest k (η j)) i - η i) ^ 2
      = dist0 k η + k * (k - 2 * dlt k (η j)) := by sorry

theorem existsUnique_iff_gap {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) (R0 : ℤ) :
    (∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) ↔
      dist0 k η ≤ R0 ∧ R0 < dist0 k η + gap k η := by sorry

theorem nearest_mem {m : ℕ} {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) {R0 : ℤ}
    (h : ∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) :
    ∑ j, (k * nearest k (η j) - η j) ^ 2 ≤ R0 := by sorry

def boxFinset (m : ℕ) (R0 : ℤ) : Finset (Fin m → ℤ) := sorry

theorem mem_boxFinset_iff {m : ℕ} {R0 : ℤ} {s : Fin m → ℤ} :
    s ∈ boxFinset m R0 ↔
      ∀ j, -((R0.natAbs : ℤ) + 1) ≤ s j ∧ s j ≤ (R0.natAbs : ℤ) + 1 := by sorry

theorem mem_boxFinset_of_le {m : ℕ} {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) {R0 : ℤ} {s : Fin m → ℤ}
    (h : ∑ j, (k * s j - η j) ^ 2 ≤ R0) : s ∈ boxFinset m R0 := by sorry

theorem existsUnique_iff_card {m : ℕ} {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) (R0 : ℤ) :
    (∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) ↔
      ((boxFinset m R0).filter fun s => ∑ j, (k * s j - η j) ^ 2 ≤ R0).card = 1 := by sorry

theorem dist0_single {m : ℕ} (k : ℤ) (j0 : Fin m) (h : ℤ) (hk : 0 ≤ k) :
    dist0 k (fun j => if j = j0 then h else 0) = dlt k h ^ 2 := by sorry

theorem full_residue_iff {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) (R0 : ℤ) :
    (∀ η : Fin m → ℤ, (∀ j, 0 ≤ η j ∧ η j < k) →
        ∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) ↔
      k % 2 = 1 ∧ (m : ℤ) * ((k - 1) / 2) ^ 2 ≤ R0 ∧ R0 < ((k + 1) / 2) ^ 2 := by sorry

theorem full_residue_k3_m3 : ∀ η : Fin 3 → ℤ, (∀ j, 0 ≤ η j ∧ η j < 3) →
    ∃! s : Fin 3 → ℤ, ∑ j, (3 * s j - η j) ^ 2 ≤ 3 := by sorry

theorem not_full_residue_k3_m4 (R0 : ℤ) : ¬ ∀ η : Fin 4 → ℤ, (∀ j, 0 ≤ η j ∧ η j < 3) →
    ∃! s : Fin 4 → ℤ, ∑ j, (3 * s j - η j) ^ 2 ≤ R0 := by sorry

theorem full_residue_k5_m2 : ∀ η : Fin 2 → ℤ, (∀ j, 0 ≤ η j ∧ η j < 5) →
    ∃! s : Fin 2 → ℤ, ∑ j, (5 * s j - η j) ^ 2 ≤ 8 := by sorry

theorem IntQuad.eval_eq_c_iff {n : ℕ} (P : IntQuad (Fin n)) :
    (∀ x, P.eval x = P.c) ↔ (∀ i, P.l i = 0) ∧ ∀ i j, P.Q i j + P.Q j i = 0 := by sorry

def resid (ρ : Fin n → Fin F.k.toNat) (j : Fin m) : ℤ := sorry

theorem resid_bounds (ρ : Fin n → Fin F.k.toNat) (j : Fin m) :
    0 ≤ F.resid ρ j ∧ F.resid ρ j < F.k := by sorry

def rep (a : Fin n → ℤ) : Fin n → Fin F.k.toNat := sorry

theorem resid_rep (a : Fin n → ℤ) (j : Fin m) : F.resid (F.rep a) j = F.lin a j % F.k := by sorry

theorem shift_existsUnique {m : ℕ} (k : ℤ) (L : Fin m → ℤ) (R0 : ℤ) :
    (∃! b : Fin m → ℤ, ∑ j, (k * b j - L j) ^ 2 ≤ R0) ↔
      ∃! s : Fin m → ℤ, ∑ j, (k * s j - L j % k) ^ 2 ≤ R0 := by sorry

theorem R_const_c (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a) (x : Fin n → ℤ) : P.eval x = P.c := by sorry

theorem total_and_outputUnique_iff_finite (hm : 0 < m) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a) :
    (F.Total ∧ F.OutputUnique) ↔
      ((∀ i, P.l i = 0) ∧ (∀ i j, P.Q i j + P.Q j i = 0) ∧
        ∀ ρ : Fin n → Fin F.k.toNat,
          ∃! s : Fin m → ℤ, ∑ j, (F.k * s j - F.resid ρ j) ^ 2 ≤ P.c) := by sorry

theorem total_and_outputUnique_iff_thresholds (hm : 0 < m) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a) :
    (F.Total ∧ F.OutputUnique) ↔
      ((∀ i, P.l i = 0) ∧ (∀ i j, P.Q i j + P.Q j i = 0) ∧
        ∀ ρ : Fin n → Fin F.k.toNat,
          FourSquareFinite.dist0 F.k (F.resid ρ) ≤ P.c ∧
            P.c < FourSquareFinite.dist0 F.k (F.resid ρ) + FourSquareFinite.gap F.k (F.resid ρ)) := by sorry

theorem graph_iff_table (hm : 0 < m) {P : IntQuad (Fin n)} (hR : ∀ a, F.R a = P.eval a)
    (hT : F.Total) (hU : F.OutputUnique) (a : Fin n → ℤ) (b : Fin m → ℤ) :
    F.Graph a b ↔
      b = fun j => F.lin a j / F.k + FourSquareFinite.nearest F.k (F.lin a j % F.k) := by sorry

theorem total_and_outputUnique_iff_of_surjective (hm : 0 < m) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a)
    (hsurj : ∀ η : Fin m → ℤ, (∀ j, 0 ≤ η j ∧ η j < F.k) → ∃ ρ, F.resid ρ = η) :
    (F.Total ∧ F.OutputUnique) ↔
      ((∀ i, P.l i = 0) ∧ (∀ i j, P.Q i j + P.Q j i = 0) ∧
        F.k % 2 = 1 ∧ (m : ℤ) * ((F.k - 1) / 2) ^ 2 ≤ P.c ∧ P.c < ((F.k + 1) / 2) ^ 2) := by sorry

def ExNeg : Family 1 1 := sorry

theorem ExNeg_box (a b : Fin 1 → ℤ) : ExNeg.Graph a b ↔ (2 * b 0) ^ 2 ≤ a 0 * (a 0 - 1) := by sorry

theorem ExNeg_representatives (a0 : ℤ) (h : a0 = 0 ∨ a0 = 1) :
    ∃! b : Fin 1 → ℤ, ExNeg.Graph (fun _ => a0) b := by sorry

theorem ExNeg_not_outputUnique : ¬ ExNeg.OutputUnique := by sorry

theorem ExNeg_residual_not_const : ¬ ∀ a, ExNeg.R a = ExNeg.R 0 := by sorry

theorem Ex_total_outputUnique_via_finite : Ex.Total ∧ Ex.OutputUnique := by sorry

/-! ## s54b extension (s54, 2026-09-16, agora; Dr. Fukui ruling "未完を全部終えて").
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s54] ResearchUpgrade/R42Completion.lean  md5 4646e9b918fd5499fa21737cfe63aee0
theorem fullVectorCosetNF_of_polarRank_eq_one {n m r : ℕ} (D : QuadraticGraphData n m r)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) (hrank : D.polarRank = 1)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : FullVectorCosetNF f := by sorry

theorem definite_binary_compiler_solutions {n : ℕ} (D : QuadraticGraphData n 1 1)
    (hpos : ∀ u : OutWit 1 1 → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ (α β Δ : ℚ) (c0 : OutWit 1 1 → ℚ) (L : OutWit 1 1 → Fin n → ℚ) (Rq : QuadForm n),
      0 < α ∧ 0 < Δ ∧
      (∀ a, D.IsCentre a (fun k => c0 k + ∑ i, L k i * (a i : ℚ))) ∧
      (∀ a, D.residual a (fun k => c0 k + ∑ i, L k i * (a i : ℚ)) = Rq.eval (castQ a)) ∧
      (∀ w : OutWit 1 1 → ℚ,
        D.zQuadQ w = α * ((w (Sum.inl 0) + β * w (Sum.inr 0)) ^ 2 + Δ * w (Sum.inr 0) ^ 2)) ∧
      ∀ (a : Fin n → ℤ) (z : OutWit 1 1 → ℤ),
        D.SolZ a z ↔ ∃ x y : ℚ, Rq.eval (castQ a) = α * (x ^ 2 + Δ * y ^ 2) ∧
          (z (Sum.inl 0) : ℚ) = (c0 (Sum.inl 0) + ∑ i, L (Sum.inl 0) i * (a i : ℚ)) + (x - β * y) ∧
          (z (Sum.inr 0) : ℚ) = (c0 (Sum.inr 0) + ∑ i, L (Sum.inr 0) i * (a i : ℚ)) + y := by sorry

theorem weakVectorCosetNF_of_no_outputs {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) :
    WeakVectorCosetNF f := by sorry

def LowRankSemidefiniteWeakNF_allM : Prop := sorry

theorem lowRankSemidefiniteWeakNF_allM_holds : LowRankSemidefiniteWeakNF_allM := by sorry

/-! ## s55 extension (s55, 2026-09-17, agora; Dr. Fukui ruling "ok go"; GATE25 Packet B).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s55] ResearchUpgrade/ConstResidual.lean  md5 2984e0d0d5442ecaa2e930dde2f61bfd
def WeakIntAffineCosetNF {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop := sorry

def CommonSlopeIntNF {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop := sorry

theorem cr_exists_common_den {ι : Type*} [Fintype ι] (x : ι → ℚ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ i, ∃ g : ℤ, (g : ℚ) = (M : ℚ) * x i := by sorry

theorem cr_mulVec_apply {ι κ : Type*} [Fintype κ] (G : Matrix ι κ ℤ) (t : κ → ℤ) (k : ι) :
    (G *ᵥ t) k = ∑ i, G k i * t i := by sorry

theorem weakVectorCosetNF_of_weakIntAffine {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : WeakIntAffineCosetNF f) : WeakVectorCosetNF f := by sorry

theorem fullVectorCosetNF_of_commonSlope {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : CommonSlopeIntNF f) : FullVectorCosetNF f := by sorry

def centreAt (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (a : Fin n → ℤ) :
    OutWit m r → ℚ := sorry

theorem cr_toQ_add (z w : OutWit m r → ℤ) : toQ (z + w) = toQ z + toQ w := by sorry

theorem cr_eval_cast {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (z : OutWit m r → ℤ) :
    ((D.P.eval (Sum.elim a z) : ℤ) : ℚ) = D.zQuadQ (toQ z - c) - D.residual a c := by sorry

theorem cr_zQuadQ_neg (v : OutWit m r → ℚ) : D.zQuadQ (-v) = D.zQuadQ v := by sorry

theorem cr_centreAt_add_smul (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a t : Fin n → ℤ) (M : ℕ) (k : OutWit m r) :
    centreAt c0 C (a + (M : ℤ) • t) k
      = centreAt c0 C a k + (M : ℚ) * ∑ i, C k i * (t i : ℚ) := by sorry

theorem constResidual_transport (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      (∀ k i, (G k i : ℚ) = (M : ℚ) * C k i) ∧
      ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ) (t : Fin n → ℤ),
        D.P.eval (Sum.elim (a + (M : ℤ) • t) (z + G *ᵥ t)) = D.P.eval (Sum.elim a z) := by sorry

theorem constResidual_solEquiv (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ)
    (hT : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ) (t : Fin n → ℤ),
      D.P.eval (Sum.elim (a + (M : ℤ) • t) (z + G *ᵥ t)) = D.P.eval (Sum.elim a z))
    (a t : Fin n → ℤ) :
    ∃ e : {z : OutWit m r → ℤ // D.SolZ a z} ≃ {z : OutWit m r → ℤ // D.SolZ (a + (M : ℤ) • t) z},
      (∀ z, (e z : OutWit m r → ℤ) = z.1 + G *ᵥ t) ∧
      (∀ z, (e.symm z : OutWit m r → ℤ) = z.1 - G *ᵥ t) := by sorry

theorem constResidual_translate (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    ∃ (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      (∀ k i, (G k i : ℚ) = (M : ℚ) * C k i) ∧
      ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = fun j => f a j + (G *ᵥ t) (Sum.inl j) := by sorry

theorem constResidual_commonSlopeIntNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    CommonSlopeIntNF f := by sorry

theorem constResidual_fullVectorCosetNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    FullVectorCosetNF f := by sorry

theorem affineSlope_unique {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (M M' : ℕ) (hM : 1 ≤ M) (hM' : 1 ≤ M') (A A' : Matrix (Fin m) (Fin n) ℚ)
    (h : ∀ (a t : Fin n → ℤ) (j : Fin m),
      (f (a + (M : ℤ) • t) j : ℚ) = f a j + (M : ℚ) * ∑ i, A j i * (t i : ℚ))
    (h' : ∀ (a t : Fin n → ℤ) (j : Fin m),
      (f (a + (M' : ℤ) • t) j : ℚ) = f a j + (M' : ℚ) * ∑ i, A' j i * (t i : ℚ)) :
    A = A' := by sorry

theorem familyData_constResidualCentre (hm : 0 < m) (hR : ∀ a, F.R a = PR.eval a)
    (hT : F.Total) (hU : F.OutputUnique) :
    ∃ (c0 : OutWit m 4 → ℚ) (C : Matrix (OutWit m 4) (Fin n) ℚ) (R0 : ℚ),
      (∀ a, (F.familyData PR).IsCentre a (QuadraticGraphData.centreAt c0 C a)) ∧
      (∀ a, (F.familyData PR).residual a (QuadraticGraphData.centreAt c0 C a) = R0) := by sorry

def ctlB1 : QuadraticGraphData 1 1 2 := sorry

theorem ctlB1_hyp :
    (∀ a, ctlB1.IsCentre a (QuadraticGraphData.centreAt 0 0 a)) ∧
    (∀ a, ctlB1.residual a (QuadraticGraphData.centreAt 0 0 a) = 0) := by sorry

theorem ctlB1_eval (a : Fin 1 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlB1.P.eval (pt a b u) = b 0 ^ 2 + (u 0 - u 1) ^ 2 := by sorry

theorem ctlB1_defines : ctlB1.Defines (fun _ => 0) := by sorry

theorem ctlB1_witnesses_infinite (a : Fin 1 → ℤ) : Set.Infinite {z | ctlB1.SolZ a z} := by sorry

-- [s55] ResearchUpgrade/CentreReflection.lean  md5 c57200b7a79e3d678c42aa4f6ce6a464
theorem centreReflect_solZ {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (h : OutWit m r → ℤ) (hh : toQ h = 2 • c) {z : OutWit m r → ℤ} (hz : D.SolZ a z) :
    D.SolZ a (h - z) := by sorry

theorem centreReflect_output {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (h : OutWit m r → ℤ) (hh : toQ h = 2 • c) (hU : D.OutputUnique)
    {z : OutWit m r → ℤ} (hz : D.SolZ a z) (j : Fin m) :
    (z (Sum.inl j) : ℚ) = c (Sum.inl j) := by sorry

theorem centreReflect_value {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (h : OutWit m r → ℤ) (hh : toQ h = 2 • c)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (j : Fin m) :
    (f a j : ℚ) = c (Sum.inl j) := by sorry

theorem centreReflect_finite_iff (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) :
    ∃ (N : ℕ) (H0 : OutWit m r → ℤ) (H : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ N ∧
      (∀ k, (H0 k : ℚ) = 2 * (N : ℚ) * c0 k) ∧
      (∀ k i, (H k i : ℚ) = 2 * (N : ℚ) * C k i) ∧
      ((∃ (a : Fin n → ℤ) (h : OutWit m r → ℤ), toQ h = 2 • centreAt c0 C a) ↔
        ∃ ρ : Fin n → Fin N, ∀ k, (N : ℤ) ∣ H0 k + ∑ i, H k i * ((ρ i : ℕ) : ℤ)) := by sorry

theorem centreReflect_coset (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ t : Fin n → ℤ,
      ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C (a0 + (M : ℤ) • t) := by sorry

theorem centreReflect_weakIntAffineCosetNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    WeakIntAffineCosetNF f := by sorry

theorem centreReflect_weakVectorCosetNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    WeakVectorCosetNF f := by sorry

/-! ## s55c extension (s55, 2026-09-17, agora; Dr. Fukui rulings "go" and "ok go"; GATE25 Packet C + B4-N; two statements amended with `0 ≤ h`).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s55] ResearchUpgrade/DefiniteShell.lean  md5 4ac507aaf0958f2796b6e3da0975e549
theorem centreReflect_coset_mod (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (N : ℕ) (hN : 1 ≤ N) (H : Matrix (OutWit m r) (Fin n) ℤ)
    (hH : ∀ k i, (H k i : ℚ) = 2 * (N : ℚ) * C k i)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    ∀ t : Fin n → ℤ, ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C (a0 + (N : ℤ) • t) := by sorry

theorem sc_zQuadQ_nonneg (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (u : OutWit m r → ℚ) : 0 ≤ D.zQuadQ u := by sorry

theorem definite_coord_sq_le (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ h : ℚ, 0 ≤ h ∧ ∀ (y : OutWit m r → ℚ) (k : OutWit m r), (y k) ^ 2 ≤ h * D.zQuadQ y := by sorry

theorem definiteShell_neg (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {T : ℚ} (hT : T < 0) (y : OutWit m r → ℤ) : D.zQuadQ (toQ y) ≠ T := by sorry

theorem definiteShell_zero (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (y : OutWit m r → ℤ) : D.zQuadQ (toQ y) = 0 ↔ y = 0 := by sorry

theorem definiteShell_bound {h : ℚ} (h0 : 0 ≤ h)
    (hh : ∀ (y : OutWit m r → ℚ) (k : OutWit m r), (y k) ^ 2 ≤ h * D.zQuadQ y)
    (T : ℚ) {y : OutWit m r → ℤ} (hy : D.zQuadQ (toQ y) = T) (k : OutWit m r) :
    |y k| ≤ ((⌈h * max T 0⌉₊ + 1 : ℕ) : ℤ) := by sorry

noncomputable def shellFinset (B : ℕ) (T : ℚ) : Finset (OutWit m r → ℤ) := sorry

theorem mem_shellFinset {h : ℚ} (h0 : 0 ≤ h)
    (hh : ∀ (y : OutWit m r → ℚ) (k : OutWit m r), (y k) ^ 2 ≤ h * D.zQuadQ y)
    (T : ℚ) (y : OutWit m r → ℤ) :
    y ∈ D.shellFinset (⌈h * max T 0⌉₊ + 1) T ↔ D.zQuadQ (toQ y) = T := by sorry

theorem sc_residue_mod {n : ℕ} {κ : Type*} [Fintype κ] (M : ℕ) (e0 : κ → ℤ)
    (E : Matrix κ (Fin n) ℤ) (a t : Fin n → ℤ) (y : κ → ℤ) :
    (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ (a + (M : ℤ) • t)) k) ↔
      (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) := by sorry

theorem shellResidue_mod {n s : ℕ} (M : ℕ) (e0 : Fin s → ℤ) (E : Matrix (Fin s) (Fin n) ℤ)
    (a t : Fin n → ℤ) (y : Fin s → ℤ) :
    (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ (a + (M : ℤ) • t)) k) ↔
      (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) := by sorry

theorem sc_cong {n : ℕ} {κ : Type*} [Fintype κ] (M : ℕ) (e0 : κ → ℤ)
    (E : Matrix κ (Fin n) ℤ) (a : Fin n → ℤ) (y : κ → ℤ) :
    (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ (fun i => a i % M)) k) ↔
      (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) := by sorry

theorem sc_solZ_iff {c0 : OutWit m r → ℚ} {C : Matrix (OutWit m r) (Fin n) ℚ} {R0 : ℚ}
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) (a : Fin n → ℤ) (z : OutWit m r → ℤ) :
    D.SolZ a z ↔ D.zQuadQ (toQ z - centreAt c0 C a) = R0 := by sorry

theorem sc_toQ_shift {c0 : OutWit m r → ℚ} {C : Matrix (OutWit m r) (Fin n) ℚ}
    (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ)
    (he0 : ∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) (hE : ∀ k i, (E k i : ℚ) = (M : ℚ) * C k i)
    (a : Fin n → ℤ) (z : OutWit m r → ℤ) :
    toQ ((M : ℤ) • z - (e0 + E *ᵥ a)) = (M : ℚ) • (toQ z - centreAt c0 C a) := by sorry

theorem shellEquiv_of (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    (M : ℕ) (hM : 1 ≤ M) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ)
    (he0 : ∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) (hE : ∀ k i, (E k i : ℚ) = (M : ℚ) * C k i)
    (a : Fin n → ℤ) :
    ∃ e : {z : OutWit m r → ℤ // D.SolZ a z} ≃
        {y : OutWit m r → ℤ // D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 ∧
          ∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k},
      (∀ z, (e z : OutWit m r → ℤ) = (M : ℤ) • z.1 - (e0 + E *ᵥ a)) ∧
      (∀ y, (M : ℤ) • (e.symm y : OutWit m r → ℤ) = y.1 + (e0 + E *ᵥ a)) := by sorry

theorem shellEquiv (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      (∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) ∧ (∀ k i, (E k i : ℚ) = (M : ℚ) * C k i) ∧
      ∀ a : Fin n → ℤ,
        ∃ e : {z : OutWit m r → ℤ // D.SolZ a z} ≃
            {y : OutWit m r → ℤ // D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 ∧
              ∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k},
          (∀ z, (e z : OutWit m r → ℤ) = (M : ℤ) • z.1 - (e0 + E *ᵥ a)) ∧
          (∀ y, (M : ℤ) • (e.symm y : OutWit m r → ℤ) = y.1 + (e0 + E *ᵥ a)) := by sorry

noncomputable def residueShell (B : ℕ) (T : ℚ) (M : ℕ) (e0 : OutWit m r → ℤ)
    (E : Matrix (OutWit m r) (Fin n) ℤ) (ρ : Fin n → ℤ) : Finset (OutWit m r → ℤ) := sorry

theorem shellImage_eq_value
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    (M : ℕ) (hM : 1 ≤ M) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ)
    (he0 : ∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) (hE : ∀ k i, (E k i : ℚ) = (M : ℚ) * C k i)
    (B : ℕ) (hB : ∀ y : OutWit m r → ℤ, D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 → ∀ k, |y k| ≤ B)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (a : Fin n → ℤ) :
    (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E (fun i => a i % M)).image outProj
      = {fun j => (M : ℤ) * f a j - (e0 + E *ᵥ a) (Sum.inl j)} := by sorry

theorem total_outputUnique_iff_shellImage
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ) (B : ℕ), 1 ≤ M ∧
      (∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) ∧ (∀ k i, (E k i : ℚ) = (M : ℚ) * C k i) ∧
      ((D.Total ∧ D.OutputUnique) ↔
        ∀ ρ : Fin n → Fin M,
          ((D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E (fun i => ((ρ i : ℕ) : ℤ))).image
            outProj).card = 1) := by sorry

theorem not_total_of_negResidual
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) (hR0 : R0 < 0) :
    ¬ D.Total := by sorry

def ctlC4 : QuadraticGraphData 1 1 2 := sorry

def cC4 : Matrix (OutWit 1 2) (Fin 1) ℚ := sorry

def eC4 : Matrix (OutWit 1 2) (Fin 1) ℤ := sorry

def fC4 : (Fin 1 → ℤ) → (Fin 1 → ℤ) := sorry

theorem cC4_b (i : Fin 1) : cC4 (Sum.inl 0) i = 1 / 3 := by sorry

theorem cC4_u (i : Fin 1) : cC4 (Sum.inr 0) i = -1 / 3 := by sorry

theorem cC4_v (i : Fin 1) : cC4 (Sum.inr 1) i = 0 := by sorry

theorem eC4_b (i : Fin 1) : eC4 (Sum.inl 0) i = 1 := by sorry

theorem eC4_u (i : Fin 1) : eC4 (Sum.inr 0) i = -1 := by sorry

theorem eC4_v (i : Fin 1) : eC4 (Sum.inr 1) i = 0 := by sorry

theorem ctlC4_eval (a b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlC4.P.eval (pt a b u) = (3 * b 0 - a 0) ^ 2 + (u 0 + b 0) ^ 2 + u 1 ^ 2 - 1 := by sorry

theorem c4_zQuadQ (u : OutWit 1 2 → ℚ) :
    ctlC4.zQuadQ u = 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2
      + u (Sum.inr 1) ^ 2 := by sorry

theorem c4_elim_eq_iff (b b' : Fin 1 → ℤ) (u u' : Fin 2 → ℤ) :
    (Sum.elim b u : OutWit 1 2 → ℤ) = Sum.elim b' u' ↔
      b 0 = b' 0 ∧ u 0 = u' 0 ∧ u 1 = u' 1 := by sorry

theorem ctlC4_posDef : ∀ u : OutWit 1 2 → ℚ, u ≠ 0 → 0 < ctlC4.zQuadQ u := by sorry

theorem ctlC4_polarRank : ctlC4.polarRank = 3 := by sorry

theorem ctlC4_centre_residual :
    (∀ a, ctlC4.IsCentre a (QuadraticGraphData.centreAt 0 cC4 a)) ∧
    (∀ a, ctlC4.residual a (QuadraticGraphData.centreAt 0 cC4 a) = 1) := by sorry

theorem ctlC4_defines : ctlC4.Defines fC4 := by sorry

theorem ctlC4_solutions_zero (z : OutWit 1 2 → ℤ) :
    ctlC4.SolZ 0 z ↔
      z = Sum.elim (0 : Fin 1 → ℤ) (![1, 0] : Fin 2 → ℤ) ∨
      z = Sum.elim (0 : Fin 1 → ℤ) (![-1, 0] : Fin 2 → ℤ) ∨
      z = Sum.elim (0 : Fin 1 → ℤ) (![0, 1] : Fin 2 → ℤ) ∨
      z = Sum.elim (0 : Fin 1 → ℤ) (![0, -1] : Fin 2 → ℤ) := by sorry

theorem ctlC4_not_witnessUnique : ¬ ctlC4.WitnessUnique := by sorry

theorem ctlC4_translate (a t : Fin 1 → ℤ) :
    fC4 (a + (3 : ℤ) • t) = fun j => fC4 a j + t 0 := by sorry

theorem c4_box (y : OutWit 1 2 → ℤ) (hy : ctlC4.zQuadQ (toQ y) = ((3 : ℕ) : ℚ) ^ 2 * 1)
    (k : OutWit 1 2) : |y k| ≤ ((4 : ℕ) : ℤ) := by sorry

theorem c4_hE : ∀ k i, (eC4 k i : ℚ) = ((3 : ℕ) : ℚ) * cC4 k i := by sorry

theorem ctlC4_shellImage (ρ : Fin 1 → ℤ) (hρ : 0 ≤ ρ 0 ∧ ρ 0 < 3) :
    ((ctlC4.residueShell 4 9 3 0 eC4 ρ).image outProj).card = 1 := by sorry

theorem ctlC4_residueShell_zero_card : (ctlC4.residueShell 4 9 3 0 eC4 0).card = 4 := by sorry

/-! ## s55d extension (s55, 2026-09-17, agora; Dr. Fukui ruling "go"; GATE25 A3, A4, C4 Step 5).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s55] ResearchUpgrade/AffineSection.lean  md5 ed715704644dd076084b348197a94bcf
theorem weakIntAffine_of_affineCoset {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (M : ℕ) (hM : 1 ≤ M) (ρ : Fin n → ℤ) (c : Fin m → ℚ) (L : Matrix (Fin m) (Fin n) ℚ)
    (h : ∀ (t : Fin n → ℤ) (j : Fin m), (f (ρ + (M : ℤ) • t) j : ℚ) = c j + ∑ i, L j i * (t i : ℚ)) :
    WeakIntAffineCosetNF f := by sorry

theorem weakIntAffine_of_section {n m r : ℕ} {D : QuadraticGraphData n m r}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (M : ℕ) (hM : 1 ≤ M) (a0 : Fin n → ℤ) (z0 : OutWit m r → ℤ)
    (G : Matrix (OutWit m r) (Fin n) ℤ)
    (hs : ∀ t : Fin n → ℤ, D.SolZ (a0 + (M : ℤ) • t) (z0 + G *ᵥ t)) :
    WeakIntAffineCosetNF f := by sorry

theorem ac_line_zero (A B c K S : ℚ) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (h : ∀ t : ℕ, |c + B * t + A * t ^ 2| ≤ K * (1 + t * S)) : A = 0 := by sorry

theorem quadForm_zero_of_linearGrowth {n : ℕ} (q : QuadForm n) (K : ℚ)
    (h : ∀ x : Fin n → ℤ, |q.eval (castQ x)| ≤ K * (1 + ∑ i, |(x i : ℚ)|)) :
    ∀ x : Fin n → ℚ, x ⬝ᵥ q.Q *ᵥ x = 0 := by sorry

theorem ac_supNorm_le {ι : Type*} [Fintype ι] (a : ι → ℤ) (N : ℕ) (h : ∀ i, |a i| ≤ N) :
    supNorm a ≤ N := by sorry

theorem weakIntAffine_of_weakNF_linearGrowth {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hNF : WeakVectorCosetNF f) (hlin : LinearGrowth f) :
    WeakIntAffineCosetNF f := by sorry

theorem ac_zPolarQ_sub_left (c c' w : OutWit m r → ℚ) :
    D.zPolarQ (c - c') w = D.zPolarQ c w - D.zPolarQ c' w := by sorry

theorem ac_centre_unique (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {a : Fin n → ℤ} {c c' : OutWit m r → ℚ} (hc : D.IsCentre a c) (hc' : D.IsCentre a c') :
    c = c' := by sorry

theorem binary_baseSection (e : OutWit m r ≃ Fin 2)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hT : ∀ a, ∃ z, D.SolZ a z)
    {a0 : Fin n → ℤ} {z0 : OutWit m r → ℤ} (hz0 : D.SolZ a0 z0)
    {c : OutWit m r → ℚ} (hc : D.IsCentre a0 c) (hR : 0 < D.residual a0 c) :
    ∃ (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      ∀ t : Fin n → ℤ, D.SolZ (a0 + (M : ℤ) • t) (z0 + G *ᵥ t) := by sorry

theorem zeroResidual_section (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (hT : ∀ a, ∃ z, D.SolZ a z)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = 0) :
    ∃ (g0 : OutWit m r → ℤ) (G : Matrix (OutWit m r) (Fin n) ℤ),
      ∀ a : Fin n → ℤ, D.SolZ a (g0 + G *ᵥ a) := by sorry

theorem weakIntAffineCosetNF_of_binary (e : OutWit m r ≃ Fin 2)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakIntAffineCosetNF f := by sorry

def LowRankSemidefiniteIntAffineNF : Prop := sorry

theorem lowRankSemidefiniteIntAffineNF_holds : LowRankSemidefiniteIntAffineNF := by sorry

-- [s55] ResearchUpgrade/ShellControls.lean  md5 40f589d7408a1ccb857df934d1ed9297
def ctlN0 : QuadraticGraphData 0 1 2 := sorry

def ctlNeg : QuadraticGraphData 0 1 2 := sorry

theorem sc_N0_zQuadQ (u : OutWit 1 2 → ℚ) :
    ctlN0.zQuadQ u = 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2
      + u (Sum.inr 1) ^ 2 := by sorry

theorem sc_Neg_zQuadQ (u : OutWit 1 2 → ℚ) :
    ctlNeg.zQuadQ u = 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2
      + u (Sum.inr 1) ^ 2 := by sorry

theorem sc_N0_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlN0.P.eval (pt a b u) = 9 * b 0 ^ 2 + (u 0 + b 0) ^ 2 + u 1 ^ 2 - 1 := by sorry

theorem sc_Neg_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlNeg.P.eval (pt a b u) = 9 * b 0 ^ 2 + (u 0 + b 0) ^ 2 + u 1 ^ 2 + 1 := by sorry

theorem sc_posForm (u : OutWit 1 2 → ℚ) (hu : u ≠ 0) :
    0 < 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2 + u (Sum.inr 1) ^ 2 := by sorry

theorem ctlN0_centre_residual :
    (∀ a, ctlN0.IsCentre a (QuadraticGraphData.centreAt 0 0 a)) ∧
    (∀ a, ctlN0.residual a (QuadraticGraphData.centreAt 0 0 a) = 1) := by sorry

theorem ctlN0_posDef : ∀ u : OutWit 1 2 → ℚ, u ≠ 0 → 0 < ctlN0.zQuadQ u := by sorry

theorem ctlN0_defines : ctlN0.Defines (fun _ _ => 0) := by sorry

theorem sc_N0_box (y : OutWit 1 2 → ℤ) (hy : ctlN0.zQuadQ (toQ y) = ((1 : ℕ) : ℚ) ^ 2 * 1)
    (k : OutWit 1 2) : |y k| ≤ ((1 : ℕ) : ℤ) := by sorry

theorem ctlN0_shellImage (ρ : Fin 0 → Fin 1) :
    ((ctlN0.residueShell 1 1 1 0 0 (fun i => ((ρ i : ℕ) : ℤ))).image outProj).card = 1 := by sorry

theorem ctlN0_residueShell_card : (ctlN0.residueShell 1 1 1 0 0 (fun _ => 0)).card = 4 := by sorry

theorem ctlNeg_centre_residual :
    (∀ a, ctlNeg.IsCentre a (QuadraticGraphData.centreAt 0 0 a)) ∧
    (∀ a, ctlNeg.residual a (QuadraticGraphData.centreAt 0 0 a) = -1) := by sorry

theorem ctlNeg_residueShell_empty (B : ℕ) :
    ctlNeg.residueShell B (-1) 1 0 0 (fun _ => 0) = ∅ := by sorry

theorem ctlNeg_not_total : ¬ ctlNeg.Total := by sorry

/-! ## s55e extension (s55, 2026-09-17, agora; Dr. Fukui ruling "ok go"; GATE25 D1–D4).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s55] ResearchUpgrade/RankControls.lean  md5 b257bf42e044bb13a2819e462926ec39
theorem rc_mulVec_castQ {a b : ℕ} (L : Matrix (Fin b) (Fin a) ℚ) (u : Fin a → ℤ) (k : Fin b) :
    (L *ᵥ castQ u) k = ∑ i, L k i * (u i : ℚ) := by sorry

theorem rc_gram {a b : ℕ} (M : ℕ) (lam : ℚ) (ρ : Fin a → ℤ) (p : Fin b → ℚ)
    (L : Matrix (Fin b) (Fin a) ℚ)
    (h : ∀ t : Fin a → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k) ^ 2
      = 1 + lam * ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2) :
    Lᵀ * L = (lam * (M : ℚ) ^ 2) • (1 : Matrix (Fin a) (Fin a) ℚ) := by sorry

theorem rc_rank_contra {a b : ℕ} (hab : b < a) (c : ℚ) (hc : c ≠ 0)
    (L : Matrix (Fin b) (Fin a) ℚ) (h : Lᵀ * L = c • (1 : Matrix (Fin a) (Fin a) ℚ)) : False := by sorry

theorem d1_no_affine_section (M : ℕ) (hM : 1 ≤ M) (ρ : Fin 4 → ℤ) (p : Fin 3 → ℚ)
    (L : Matrix (Fin 3) (Fin 4) ℚ) :
    ¬ ∀ t : Fin 4 → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k) ^ 2
        = 1 + 8 * ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2 := by sorry

theorem d1_total_of_threeSquares
    (h3 : ∀ N : ℤ, 0 ≤ N → N % 8 = 1 → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = N)
    (a : Fin 4 → ℤ) : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 1 + 8 * ∑ i, a i ^ 2 := by sorry

theorem d1_outputs_zero (b : ℤ) :
    (∃ u v : ℤ, b ^ 2 + u ^ 2 + v ^ 2 = 1 + 8 * ∑ i, (0 : Fin 4 → ℤ) i ^ 2) ↔
      b = -1 ∨ b = 0 ∨ b = 1 := by sorry

def ctlD1 : QuadraticGraphData 4 1 2 := sorry

theorem ctlD1_eval (a : Fin 4 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlD1.P.eval (pt a b u) = b 0 ^ 2 + u 0 ^ 2 + u 1 ^ 2 - 1 - 8 * ∑ i, a i ^ 2 := by sorry

theorem ctlD1_total_of_threeSquares
    (h3 : ∀ N : ℤ, 0 ≤ N → N % 8 = 1 → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = N) :
    ctlD1.Total := by sorry

theorem ctlD1_not_outputUnique : ¬ ctlD1.OutputUnique := by sorry

theorem d1r4_total (a : Fin 5 → ℤ) : ∃ z : Fin 4 → ℤ, ∑ k, z k ^ 2 = 1 + ∑ i, a i ^ 2 := by sorry

theorem d1r4_no_affine_section (M : ℕ) (hM : 1 ≤ M) (ρ : Fin 5 → ℤ) (p : Fin 4 → ℚ)
    (L : Matrix (Fin 4) (Fin 5) ℚ) :
    ¬ ∀ t : Fin 5 → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k) ^ 2
        = 1 + ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2 := by sorry

def ctlD1r4 : QuadraticGraphData 5 1 3 := sorry

theorem ctlD1r4_eval (a : Fin 5 → ℤ) (b : Fin 1 → ℤ) (u : Fin 3 → ℤ) :
    ctlD1r4.P.eval (pt a b u) = b 0 ^ 2 + u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 - 1 - ∑ i, a i ^ 2 := by sorry

theorem ctlD1r4_total : ctlD1r4.Total := by sorry

theorem ctlD1r4_not_outputUnique : ¬ ctlD1r4.OutputUnique := by sorry

-- [s55] ResearchUpgrade/IsometryCertificate.lean  md5 68577dd3de689fbb58a8f356979648a8
theorem isometry_solZ {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (T : Matrix (OutWit m r) (OutWit m r) ℚ) (hT : ∀ w, D.zQuadQ (T *ᵥ w) = D.zQuadQ w)
    {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (z' : OutWit m r → ℤ) (hz' : toQ z' = c + T *ᵥ (toQ z - c)) :
    D.SolZ a z' := by sorry

theorem isometry_output_zero {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (T : Matrix (OutWit m r) (OutWit m r) ℚ) (hT : ∀ w, D.zQuadQ (T *ᵥ w) = D.zQuadQ w)
    (hU : D.OutputUnique) {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (z' : OutWit m r → ℤ) (hz' : toQ z' = c + T *ᵥ (toQ z - c)) (j : Fin m) :
    (T *ᵥ (toQ z - c) - (toQ z - c)) (Sum.inl j) = 0 := by sorry

theorem isometry_integral_iff {s : Type*} [Fintype s] (c : s → ℚ) (T : Matrix s s ℚ) (z : s → ℤ)
    (N : ℕ) (hN : 1 ≤ N) (cN : s → ℤ) (TN : Matrix s s ℤ)
    (hcN : ∀ k, (cN k : ℚ) = (N : ℚ) * c k) (hTN : ∀ k l, (TN k l : ℚ) = (N : ℚ) * T k l) :
    (∃ z' : s → ℤ, (fun k => (z' k : ℚ)) = c + T *ᵥ ((fun k => (z k : ℚ)) - c)) ↔
      ∀ k, ((N : ℤ) ^ 2) ∣ ((N : ℤ) • cN + (N : ℤ) • (TN *ᵥ z) - TN *ᵥ cN) k := by sorry

theorem affineIntegral_coset {n : ℕ} {s : Type*} [Fintype s] (d0 : s → ℚ) (Dm : Matrix s (Fin n) ℚ)
    (M : ℕ) (hMD : ∀ k i, ∃ g : ℤ, (g : ℚ) = (M : ℚ) * Dm k i) (ρ : Fin n → ℤ)
    (h0 : ∃ h : s → ℤ, (fun k => (h k : ℚ)) = d0 + Dm *ᵥ castQ ρ) :
    ∀ t : Fin n → ℤ, ∃ h : s → ℤ,
      (fun k => (h k : ℚ)) = d0 + Dm *ᵥ castQ (ρ + (M : ℤ) • t) := by sorry

theorem ic_centreAt_eq (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a : Fin n → ℤ) : centreAt c0 C a = c0 + C *ᵥ castQ a := by sorry

theorem ic_toQ_mulVec (T : Matrix (OutWit m r) (OutWit m r) ℤ) (z : OutWit m r → ℤ) :
    toQ (T *ᵥ z) = T.map (Int.cast : ℤ → ℚ) *ᵥ toQ z := by sorry

theorem symmetry_certificate_NF {ι : Type*} [Fintype ι]
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (T : ι → Matrix (OutWit m r) (OutWit m r) ℤ)
    (hT : ∀ i w, D.zQuadQ ((T i).map (Int.cast : ℤ → ℚ) *ᵥ w) = D.zQuadQ w)
    (M : ℕ) (hM : 1 ≤ M) (ρ : Fin n → ℤ)
    (hMint : ∀ i k l, ∃ g : ℤ,
      (g : ℚ) = (M : ℚ) * (((1 - (T i).map (Int.cast : ℤ → ℚ) : Matrix (OutWit m r) (OutWit m r) ℚ) * C :
        Matrix (OutWit m r) (Fin n) ℚ) k l))
    (h0 : ∀ i, ∃ h : OutWit m r → ℤ,
      toQ h = (1 - (T i).map (Int.cast : ℤ → ℚ)) *ᵥ centreAt c0 C ρ)
    (A : ι → Matrix (Fin m) (Fin m) ℚ)
    (hA : ∀ w : OutWit m r → ℚ, (fun j => w (Sum.inl j)) =
      ∑ i, A i *ᵥ (fun j => (((T i).map (Int.cast : ℤ → ℚ) - 1) *ᵥ w) (Sum.inl j))) :
    WeakIntAffineCosetNF f := by sorry

theorem negIdentity_shift {s : Type*} [Fintype s] [DecidableEq s] (x : s → ℚ) :
    (1 - (-1 : Matrix s s ℤ).map (Int.cast : ℤ → ℚ)) *ᵥ x = 2 • x := by sorry

theorem negIdentity_certificate {m r : ℕ} (w : OutWit m r → ℚ) :
    (fun j => w (Sum.inl j)) =
      ((-1 / 2 : ℚ) • (1 : Matrix (Fin m) (Fin m) ℚ)) *ᵥ
        (fun j => (((-1 : Matrix (OutWit m r) (OutWit m r) ℤ).map (Int.cast : ℤ → ℚ) - 1) *ᵥ w)
          (Sum.inl j)) := by sorry

def ctlD4 : QuadraticGraphData 1 1 2 := sorry

def c0D4 : OutWit 1 2 → ℚ := sorry

def cD4 : Matrix (OutWit 1 2) (Fin 1) ℚ := sorry

def T1D4 : Matrix (OutWit 1 2) (OutWit 1 2) ℤ := sorry

def T2D4 : Matrix (OutWit 1 2) (OutWit 1 2) ℤ := sorry

theorem c0D4_b : c0D4 (Sum.inl 0) = 0 := by sorry

theorem c0D4_u : c0D4 (Sum.inr 0) = 1 / 3 := by sorry

theorem c0D4_v : c0D4 (Sum.inr 1) = 0 := by sorry

theorem cD4_b (i : Fin 1) : cD4 (Sum.inl 0) i = 1 := by sorry

theorem cD4_u (i : Fin 1) : cD4 (Sum.inr 0) i = 0 := by sorry

theorem cD4_v (i : Fin 1) : cD4 (Sum.inr 1) i = 0 := by sorry

theorem ctlD4_eval (a b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlD4.P.eval (pt a b u) = (2 * b 0 - 2 * a 0) ^ 2 + (3 * u 0 - 1) ^ 2 + u 1 ^ 2 - 1 := by sorry

theorem ctlD4_zQuadQ (w : OutWit 1 2 → ℚ) :
    ctlD4.zQuadQ w = 4 * w (Sum.inl 0) ^ 2 + 9 * w (Sum.inr 0) ^ 2 + w (Sum.inr 1) ^ 2 := by sorry

theorem ctlD4_centre_residual :
    (∀ a, ctlD4.IsCentre a (QuadraticGraphData.centreAt c0D4 cD4 a)) ∧
    (∀ a, ctlD4.residual a (QuadraticGraphData.centreAt c0D4 cD4 a) = 1) := by sorry

theorem ctlD4_defines : ctlD4.Defines (fun a _ => a 0) := by sorry

theorem ctlD4_not_reflectable (a : Fin 1 → ℤ) :
    ¬ ∃ h : OutWit 1 2 → ℤ, toQ h = 2 • QuadraticGraphData.centreAt c0D4 cD4 a := by sorry

theorem ctlD4_T1_isometry (w : OutWit 1 2 → ℚ) :
    ctlD4.zQuadQ (T1D4.map (Int.cast : ℤ → ℚ) *ᵥ w) = ctlD4.zQuadQ w := by sorry

theorem ctlD4_T2_isometry (w : OutWit 1 2 → ℚ) :
    ctlD4.zQuadQ (T2D4.map (Int.cast : ℤ → ℚ) *ᵥ w) = ctlD4.zQuadQ w := by sorry

theorem ctlD4_T2_not_integral (a : Fin 1 → ℤ) :
    ¬ ∃ z' : OutWit 1 2 → ℤ, toQ z' =
      QuadraticGraphData.centreAt c0D4 cD4 a +
        T2D4.map (Int.cast : ℤ → ℚ) *ᵥ
          (toQ (Sum.elim (fun _ => a 0) (0 : Fin 2 → ℤ)) - QuadraticGraphData.centreAt c0D4 cD4 a) := by sorry

theorem ctlD4_certificate_NF :
    WeakIntAffineCosetNF (fun a : Fin 1 → ℤ => fun _ : Fin 1 => a 0) := by sorry

-- [s55] ResearchUpgrade/ResidualReduction.lean  md5 b217020ba050d7c20bb0e0235cdce0ca
def ResidualReflectionObstructionNF : Prop := sorry

theorem definite_exists_centreAt {n m r : ℕ} (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ),
      ∀ a, D.IsCentre a (centreAt c0 C a) := by sorry

theorem generalWeakNF_iff_residualReflectionObstructionNF :
    GeneralWeakNF ↔ ResidualReflectionObstructionNF := by sorry

/-! ## s55f extension (s55, 2026-09-17, agora; Dr. Fukui ruling "GPTの宿題を終える"; R43 A4 Step 2 route, D1 Step 4).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s55] ResearchUpgrade/R43Completion.lean  md5 dce4753c9c133155cd737bae75ebd663
theorem weakIntAffine_of_small {n m r' : ℕ} (D : QuadraticGraphData n m r') (hmr : m + r' ≤ 2)
    (hm : 0 < m) (hpos : ∀ u : OutWit m r' → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakIntAffineCosetNF f := by sorry

theorem lowRankSemidefiniteIntAffineNF_holds_viaBinary : LowRankSemidefiniteIntAffineNF := by sorry

theorem d1_no_quadratic_section (M : ℕ) (hM : 1 ≤ M) (ρ : Fin 4 → ℤ) (p : Fin 3 → ℚ)
    (L : Matrix (Fin 3) (Fin 4) ℚ) (H : Fin 3 → Matrix (Fin 4) (Fin 4) ℚ) :
    ¬ ∀ t : Fin 4 → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k + castQ t ⬝ᵥ (H k *ᵥ castQ t)) ^ 2
        = 1 + 8 * ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2 := by sorry

/-! ## s55g extension (s55, 2026-09-17, agora; Dr. Fukui ruling "全て足して"; own-initiative NormTotality).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s55] ResearchUpgrade/NormTotality.lean  md5 07a33737a20e23c087c6e1b124ff0850
theorem nt_nonroot (A B C : ℚ) (hA : A ≠ 0) :
    ∃ t : ℤ, A * (t : ℚ) ^ 2 + B * (t : ℚ) + C ≠ 0 := by sorry

theorem norm_totality_iff (A B C D : ℚ) (hD : 0 < D) (hA : A ≠ 0) :
    (∀ t : ℤ, ∃ x z : ℚ, A * (t : ℚ) ^ 2 + B * (t : ℚ) + C = x ^ 2 + D * z ^ 2) ↔
      ((∃ h : ℚ, B ^ 2 - 4 * A * C = -D * h ^ 2) ∧ ∃ a0 b0 : ℚ, A = a0 ^ 2 + D * b0 ^ 2) := by sorry

/-! ## s56 extension (s56, 2026-09-25, agora; GATE26 Packet A + D1, statements frozen before proof, ruling R3).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s56] ResearchUpgrade/SectionRigidity.lean  md5 eb39866fd8633f4794b55f8d6a1206a7
theorem sr_solZ_iff (D : QuadraticGraphData n m r) {a : Fin n → ℤ} {c : OutWit m r → ℚ}
    (hc : D.IsCentre a c) (z : OutWit m r → ℤ) :
    D.SolZ a z ↔ D.zQuadQ (toQ z - c) = D.residual a c := by sorry

theorem sr_zQuadQ_nonneg (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (u : OutWit m r → ℚ) :
    0 ≤ D.zQuadQ u := by sorry

theorem sr_polarRank_eq (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) : D.polarRank = m + r := by sorry

theorem sr_centreAt_line (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a0 v : Fin n → ℤ) (t : ℤ) :
    centreAt c0 C (a0 + t • v)
      = centreAt c0 C a0 + (t : ℚ) • (fun k => ∑ i, C k i * (v i : ℚ)) := by sorry

theorem sr_aPart_line (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : ℤ) :
    D.aPart (a0 + t • v) = D.aPart a0
      + t * ((∑ i, D.P.l (Sum.inl i) * v i)
          + ∑ i, ∑ j, (a0 i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j)
              + v i * (D.P.Q (Sum.inl i) (Sum.inl j) * a0 j)))
      + t ^ 2 * ∑ i, ∑ j, v i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j) := by sorry

theorem sr_residual_line (D : QuadraticGraphData n m r) (c0 : OutWit m r → ℚ)
    (C : Matrix (OutWit m r) (Fin n) ℚ) (a0 v : Fin n → ℤ) :
    ∃ A B : ℚ, ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
      = A * (t : ℚ) ^ 2 + B * t + D.residual a0 (centreAt c0 C a0) := by sorry

theorem sr_quad_nonneg (A B C : ℚ) (h : ∀ t : ℤ, 0 ≤ A * (t : ℚ) ^ 2 + B * t + C) :
    0 ≤ A ∧ (A = 0 → B = 0) := by sorry

def ConstantResidualRigidity : Prop := sorry

def LineCollision : Prop := sorry

def RankTwoSemidefiniteFullNF : Prop := sorry

theorem sr_solZ_of_total (D : QuadraticGraphData n m r) (hT : D.Total) (a : Fin n → ℤ) :
    ∃ z, D.SolZ a z := by sorry

theorem sr_polar_comb_right (D : QuadraticGraphData n m r) (v y x : OutWit m r → ℚ) (α β : ℚ) :
    D.zPolarQ v (α • y - β • x) = α * D.zPolarQ v y - β * D.zPolarQ v x := by sorry

theorem sr_polar_comb_left (D : QuadraticGraphData n m r) (v y x : OutWit m r → ℚ) (α β : ℚ) :
    D.zPolarQ (α • y - β • x) v = α * D.zPolarQ y v - β * D.zPolarQ x v := by sorry

theorem sr_ne_zero_of_quad (D : QuadraticGraphData n m r) {u : OutWit m r → ℚ}
    (h : 0 < D.zQuadQ u) : u ≠ 0 := by sorry

theorem sr_collide (D : QuadraticGraphData n m r) (hOU : D.OutputUnique) {a : Fin n → ℤ}
    {c : OutWit m r → ℚ} (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (κ : OutWit m r → ℤ) (j : Fin m) (hκ : κ (Sum.inl j) ≠ 0)
    (hnorm : D.zQuadQ (toQ z - c + toQ κ) = D.zQuadQ (toQ z - c)) : False := by sorry

theorem sr_reflect_norm (D : QuadraticGraphData n m r) (x w : OutWit m r → ℚ)
    (hw : D.zQuadQ w ≠ 0) (t : ℚ) (ht : t = - D.zPolarQ x w / D.zQuadQ w) :
    D.zQuadQ (x + t • w) = D.zQuadQ x := by sorry

theorem sr_nonradial_step (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (X h : OutWit m r → ℚ) (j0 : Fin m)
    (hV : (2 * D.zQuadQ X) • h - D.zPolarQ h X • X ≠ 0)
    (hf2 : ∃ y : OutWit m r → ℚ,
      2 * D.zQuadQ X * y (Sum.inl j0) - D.zPolarQ X y * X (Sum.inl j0) ≠ 0) :
    ∃ (M : ℕ) (κ : OutWit m r → ℤ), 1 ≤ M ∧ κ (Sum.inl j0) ≠ 0 ∧
      D.zQuadQ (X + (M : ℚ) • h + toQ κ) = D.zQuadQ (X + (M : ℚ) • h) := by sorry

theorem lineSection_centredSlope_zero (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (hOU : D.OutputUnique)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 w : Fin n → ℤ) (z0 g : OutWit m r → ℤ)
    (hsec : ∀ s : ℤ, D.SolZ (a0 + s • w) (z0 + s • g)) :
    ∀ s : ℤ, toQ (z0 + s • g) - centreAt c0 C (a0 + s • w) = toQ z0 - centreAt c0 C a0 := by sorry

theorem sr_const_of_coset (D : QuadraticGraphData n m r) (c0 : OutWit m r → ℚ)
    (C : Matrix (OutWit m r) (Fin n) ℚ) (a0 : Fin n → ℤ) (M : ℕ) (hM : 1 ≤ M) (R0 : ℚ)
    (h : ∀ t : Fin n → ℤ, D.residual (a0 + (M : ℤ) • t) (centreAt c0 C (a0 + (M : ℤ) • t)) = R0) :
    ∀ a, D.residual a (centreAt c0 C a) = R0 := by sorry

theorem affineSection_constResidual (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (hOU : D.OutputUnique)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 : Fin n → ℤ) (M : ℕ) (hM : 1 ≤ M) (z0 : OutWit m r → ℤ) (G : Matrix (OutWit m r) (Fin n) ℤ)
    (hsec : ∀ t : Fin n → ℤ, D.SolZ (a0 + (M : ℤ) • t) (z0 + G *ᵥ t)) :
    ∃ R0 : ℚ, ∀ a, D.residual a (centreAt c0 C a) = R0 := by sorry

theorem discriminantZero_line_const (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (hOU : D.OutputUnique)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 v : Fin n → ℤ) (z0 : OutWit m r → ℤ) (hz0 : D.SolZ a0 z0)
    (hR0 : 0 < D.residual a0 (centreAt c0 C a0)) (A B : ℚ)
    (hline : ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = A * (t : ℚ) ^ 2 + B * t + D.residual a0 (centreAt c0 C a0))
    (hdisc : B ^ 2 = 4 * A * D.residual a0 (centreAt c0 C a0)) :
    A = 0 ∧ B = 0 := by sorry

theorem rankTwo_CCR (D : QuadraticGraphData n m r) (e : OutWit m r ≃ Fin 2) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a)) (hT : D.Total) (hOU : D.OutputUnique) :
    ∃ R0 : ℚ, ∀ a, D.residual a (centreAt c0 C a) = R0 := by sorry

theorem residual_line_of_nonconstant (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a)) (hT : D.Total)
    (hnc : ¬ ∃ R0 : ℚ, ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (a0 v : Fin n → ℤ) (A B : ℚ), 0 < A ∧ ∀ t : ℤ,
      D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = A * (t : ℚ) ^ 2 + B * t + D.residual a0 (centreAt c0 C a0) := by sorry

theorem ccr_of_lineCollision (h : LineCollision) : ConstantResidualRigidity := by sorry

theorem rankTwoSemidefiniteFullNF_holds : RankTwoSemidefiniteFullNF := by sorry

-- [s56] ResearchUpgrade/CCRControls.lean  md5 4acdb8f2af63b8dfcf6cc813d8fd6e43
def noOut : QuadraticGraphData 1 0 2 := sorry

theorem noOut_zQuadQ (u : OutWit 0 2 → ℚ) :
    noOut.zQuadQ u = u (Sum.inr 0) ^ 2 + u (Sum.inr 1) ^ 2 := by sorry

theorem noOut_pos : ∀ u : OutWit 0 2 → ℚ, u ≠ 0 → 0 < noOut.zQuadQ u := by sorry

theorem noOut_eval (a : Fin 1 → ℤ) (b : Fin 0 → ℤ) (u : Fin 2 → ℤ) :
    noOut.P.eval (pt a b u) = u 0 ^ 2 + u 1 ^ 2 - a 0 ^ 2 := by sorry

theorem noOut_aPart (a : Fin 1 → ℤ) : noOut.aPart a = -(a 0) ^ 2 := by sorry

theorem noOut_centre (a : Fin 1 → ℤ) :
    noOut.IsCentre a (centreAt (0 : OutWit 0 2 → ℚ) (0 : Matrix (OutWit 0 2) (Fin 1) ℚ) a) := by sorry

theorem noOut_residual (a : Fin 1 → ℤ) :
    noOut.residual a (centreAt (0 : OutWit 0 2 → ℚ) (0 : Matrix (OutWit 0 2) (Fin 1) ℚ) a)
      = ((a 0 : ℤ) : ℚ) ^ 2 := by sorry

theorem ccr_false_without_output :
    ∃ (D : QuadraticGraphData 1 0 2) (c0 : OutWit 0 2 → ℚ) (C : Matrix (OutWit 0 2) (Fin 1) ℚ),
      (∀ u : OutWit 0 2 → ℚ, u ≠ 0 → 0 < D.zQuadQ u) ∧ 2 ≤ D.polarRank ∧
      (∀ a, D.IsCentre a (QuadraticGraphData.centreAt c0 C a)) ∧ D.Total ∧ D.OutputUnique ∧
      ¬ ∃ R0 : ℚ, ∀ a, D.residual a (QuadraticGraphData.centreAt c0 C a) = R0 := by sorry

theorem D3_zQuadQ (u : OutWit 1 0 → ℚ) : N4Control.D3.zQuadQ u = 4 * u (Sum.inl 0) ^ 2 := by sorry

theorem D3_pos : ∀ u : OutWit 1 0 → ℚ, u ≠ 0 → 0 < N4Control.D3.zQuadQ u := by sorry

theorem ccr_false_rank_one :
    ∃ (c0 : OutWit 1 0 → ℚ) (C : Matrix (OutWit 1 0) (Fin 1) ℚ),
      (∀ u : OutWit 1 0 → ℚ, u ≠ 0 → 0 < N4Control.D3.zQuadQ u) ∧ N4Control.D3.polarRank = 1 ∧
      (∀ a, N4Control.D3.IsCentre a (QuadraticGraphData.centreAt c0 C a)) ∧
      N4Control.D3.Total ∧ N4Control.D3.OutputUnique ∧
      ¬ ∃ R0 : ℚ, ∀ a, N4Control.D3.residual a (QuadraticGraphData.centreAt c0 C a) = R0 := by sorry

theorem rotation_without_congruence_not_integral :
    ((-4 / 5 : ℚ) ^ 2 + (3 / 5 : ℚ) ^ 2 = 1) ∧
    (-4 / 5 : ℚ) = ((1 - 1 * 1 * 3 ^ 2) * 1 + 2 * 1 * 3 * 0) / (1 + 1 * 1 * 3 ^ 2) ∧
    (3 / 5 : ℚ) = ((1 - 1 * 1 * 3 ^ 2) * 0 + 2 * 1 * 3 * 1) / (1 + 1 * 1 * 3 ^ 2) ∧
    ¬ ∃ z : Fin 2 → ℤ, (z 0 : ℚ) = ((-4 / 5 : ℚ) - 1) / 3 ∧ (z 1 : ℚ) = ((3 / 5 : ℚ) - 0) / 3 := by sorry

theorem integer_nonneg_not_real_nonneg :
    (∀ t : ℤ, 0 ≤ t * (t - 1)) ∧ ∃ t : ℚ, t * (t - 1) < 0 := by sorry

theorem sq_add_sq_eq_24_aux : ∀ (N : ℕ) (A B C D : ℤ), C.natAbs + D.natAbs ≤ N →
    A ^ 2 + B ^ 2 = 24 * (C ^ 2 + D ^ 2) → C = 0 ∧ D = 0 := by sorry

theorem sq_add_sq_eq_24_rat (a b c d : ℚ) (h : a ^ 2 + b ^ 2 = 24 * (c ^ 2 + d ^ 2)) :
    c = 0 ∧ d = 0 := by sorry

theorem threeSquares24_no_rational_affine_section :
    ¬ ∃ (M : ℕ) (ρ : ℤ) (x0 x1 : Fin 3 → ℚ), 1 ≤ M ∧
      ∀ t : ℤ, ∑ i, (x0 i + (t : ℚ) * x1 i) ^ 2 = 1 + 24 * ((ρ : ℚ) + (M : ℚ) * t) ^ 2 := by sorry

/-! ## s56b extension (s56, 2026-09-25, agora; GATE26 Packets B + C2 (TCERBridge), statements frozen before installation, rulings R4/R5).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s56b] ResearchUpgrade/TCERBridge.lean  md5 d38c3b75eb941169e6765e68f7bca5d5
def QS (S : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) : ℤ := sorry

def e1 : Fin 3 → ℤ := sorry

def LocalPrimRep (S : Matrix (Fin 3) (Fin 3) ℤ) (d : ℕ) (ρ : Fin 3 → ℤ) (N : ℤ) : Prop := sorry

def TernaryCosetEventualRepresentation : Prop := sorry

def BS (S : Matrix (Fin 3) (Fin 3) ℤ) (x y : Fin 3 → ℤ) : ℤ := sorry

theorem QS_sub_smul (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm) (x y : Fin 3 → ℤ) (c : ℤ) :
    QS S (x - c • y) = QS S x - 2 * c * BS S x y + c ^ 2 * QS S y := by sorry

theorem BS_e1 (S : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) :
    BS S e1 y = S 0 0 * y 0 + S 0 1 * y 1 + S 0 2 * y 2 := by sorry

theorem QS_e1 (S : Matrix (Fin 3) (Fin 3) ℤ) : QS S e1 = S 0 0 := by sorry

theorem twoVisibleCosets (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) (d : ℕ) (hd : 0 < d)
    (p : Fin 3 → ℤ) (hp : p ≠ 0) :
    ∃ (ℓ : ℕ) (ρ₁ ρ₂ : Fin 3 → ℤ), ℓ.Prime ∧
      ¬ ℓ ∣ 2 * d * S.det.natAbs * (QS S e1).natAbs ∧
      (∀ i, ρ₁ i ≡ e1 i [ZMOD d]) ∧ (∀ i, ρ₂ i ≡ e1 i [ZMOD d]) ∧
      (∀ i, ρ₁ i ≡ e1 i [ZMOD ℓ]) ∧ QS S ρ₂ ≡ QS S e1 [ZMOD ℓ] ∧
      ¬ (p ⬝ᵥ ρ₁ ≡ p ⬝ᵥ ρ₂ [ZMOD ℓ]) := by sorry

theorem b4_valInt_one {q : ℕ} [hq : Fact q.Prime] {x : ℤ} (h1 : (q : ℤ) ∣ x) (h2 : ¬ (q : ℤ) ^ 2 ∣ x) :
    x ≠ 0 ∧ padicValInt q x = 1 := by sorry

theorem b4_not_squareClass {q : ℕ} [hq : Fact q.Prime] {x : ℤ} (hx : x ≠ 0) (hv : padicValInt q x = 1)
    (e : ℕ) (he : 0 < e) (hqe : ¬ q ∣ e) : ¬ ∃ s : ℚ, (x : ℚ) = (e : ℚ) * s ^ 2 := by sorry

theorem squareClassEscapeProgression (A B c : ℤ) (hA : 0 < A) (hc : 0 < c)
    (hdisc : B ^ 2 - 4 * A * c ≠ 0) (forbid : ℕ) (hforbid : 0 < forbid)
    (E : Finset ℕ) (hE : ∀ e ∈ E, 0 < e) :
    ∃ (q : ℕ) (k1 : ℤ), q.Prime ∧ ¬ q ∣ forbid ∧
      ¬ q ∣ 2 * A.natAbs * (B ^ 2 - 4 * A * c).natAbs ∧ (∀ e ∈ E, ¬ q ∣ e) ∧
      ∀ k : ℤ, k ≡ k1 [ZMOD (q : ℤ) ^ 2] →
        A * k ^ 2 + B * k + c ≠ 0 ∧ padicValInt q (A * k ^ 2 + B * k + c) = 1 ∧
        ∀ e ∈ E, ¬ ∃ s : ℚ, ((A * k ^ 2 + B * k + c : ℤ) : ℚ) = (e : ℚ) * s ^ 2 := by sorry

theorem b3_hensel0 {p : ℕ} (hp : p.Prime) (a b c u : ℤ) (g : ℕ)
    (hb : b = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u) (hc : (p : ℤ) ^ (2 * g + 1) ∣ c) :
    ∀ e : ℕ, ∃ τ : ℤ, (p : ℤ) ^ (e + (2 * g + 1)) ∣
      a * ((p : ℤ) ^ (g + 1) * τ) ^ 2 + b * ((p : ℤ) ^ (g + 1) * τ) + c := by sorry

theorem b3_hensel {p : ℕ} (hp : p.Prime) (a b c t0 u : ℤ) (g : ℕ)
    (hF0 : (p : ℤ) ^ (2 * g + 1) ∣ a * t0 ^ 2 + b * t0 + c)
    (hb : b + 2 * a * t0 = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u) :
    ∀ e : ℕ, ∃ τ : ℤ, (p : ℤ) ^ (e + (2 * g + 1)) ∣
      a * (t0 + (p : ℤ) ^ (g + 1) * τ) ^ 2 + b * (t0 + (p : ℤ) ^ (g + 1) * τ) + c := by sorry

theorem b3_QS_add_smul (S : Matrix (Fin 3) (Fin 3) ℤ) (y z : Fin 3 → ℤ) (t : ℤ) :
    QS S (y + t • z) = QS S y + t * (y ⬝ᵥ (S *ᵥ z) + z ⬝ᵥ (S *ᵥ y)) + t ^ 2 * QS S z := by sorry

theorem b3_QS_smul (S : Matrix (Fin 3) (Fin 3) ℤ) (z : Fin 3 → ℤ) (t : ℤ) :
    QS S (t • z) = t ^ 2 * QS S z := by sorry

theorem b3_polar_single (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm) (y : Fin 3 → ℤ) (i : Fin 3) :
    y ⬝ᵥ (S *ᵥ Pi.single i 1) + Pi.single i 1 ⬝ᵥ (S *ᵥ y) = 2 * (S *ᵥ y) i := by sorry

theorem b3_det_ne_zero (S : Matrix (Fin 3) (Fin 3) ℤ)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) : S.det ≠ 0 := by sorry

theorem b3_coord_not_dvd {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : ¬ (p : ℤ) ∣ S.det) (y : Fin 3 → ℤ) (hy : ¬ ∀ i, (p : ℤ) ∣ y i) :
    ∃ i, ¬ (p : ℤ) ∣ (S *ᵥ y) i := by sorry

theorem b3_isotropic {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) :
    ∃ x : Fin 3 → ℤ, (¬ ∀ i, (p : ℤ) ∣ x i) ∧ (p : ℤ) ∣ QS S x := by sorry

theorem b3_vec {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (ρ y x0 w : Fin 3 → ℤ) (D N : ℤ)
    (hy : y = ρ + D • x0) (h g : ℕ) (a' b' c' t0 u : ℤ)
    (hF : ∀ t : ℤ, QS S (y + (t * D) • w) - N = (p : ℤ) ^ h * (a' * t ^ 2 + b' * t + c'))
    (hF0 : (p : ℤ) ^ (2 * g + 1) ∣ a' * t0 ^ 2 + b' * t0 + c')
    (hb : b' + 2 * a' * t0 = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u)
    (hprim : ¬ ∀ i, (p : ℤ) ∣ (y + (t0 * D) • w) i) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i := by sorry

theorem b3_vec0 {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (ρ y x0 w : Fin 3 → ℤ) (D N : ℤ)
    (hy : y = ρ + D • x0) (g : ℕ) (u : ℤ)
    (hb : D * (y ⬝ᵥ (S *ᵥ w) + w ⬝ᵥ (S *ᵥ y)) = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u)
    (hc : (p : ℤ) ^ (2 * g + 1) ∣ QS S y - N) (hprim : ¬ ∀ i, (p : ℤ) ∣ y i) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i := by sorry

theorem b3_val_le {q : ℕ} (hq : q.Prime) {c : ℤ} (hc : c ≠ 0) : padicValInt q c ≤ c.natAbs := by sorry

theorem b3_val {q : ℕ} (hq : q.Prime) {c N : ℤ} (hc : c ≠ 0) (h : (q : ℤ) ^ (c.natAbs + 1) ∣ N - c) :
    padicValInt q N = padicValInt q c := by sorry

theorem b3_QS_congr (S : Matrix (Fin 3) (Fin 3) ℤ) (n : ℤ) (ρ σ : Fin 3 → ℤ)
    (h : ∀ i, ρ i ≡ σ i [ZMOD n]) : QS S ρ ≡ QS S σ [ZMOD n] := by sorry

theorem b3_dvd_QS {p : ℤ} (S : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) (h : ∀ i, p ∣ y i) :
    p ∣ QS S y := by sorry

theorem b3_dvd_polar {p : ℤ} (S : Matrix (Fin 3) (Fin 3) ℤ) (x y : Fin 3 → ℤ) (h : ∀ i, p ∣ y i) :
    p ∣ x ⬝ᵥ (S *ᵥ y) + y ⬝ᵥ (S *ᵥ x) := by sorry

theorem b3_caseA {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (ρ y x0 v : Fin 3 → ℤ) (D R N c : ℤ) (K : ℕ) (i0 : Fin 3)
    (hy1 : y = e1 + R ^ K • v) (hy2 : y = ρ + D • x0) (hc : c = QS S e1) (hNc : R ^ K ∣ N - c)
    (hpR : (p : ℤ) ∣ R) (hb1 : D * (2 * (S *ᵥ e1) i0) ≠ 0)
    (hK : 2 * (D * (2 * (S *ᵥ e1) i0)).natAbs + 1 ≤ K) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i := by sorry

theorem b3_caseB {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (ρ y x0 : Fin 3 → ℤ) (d N c : ℤ)
    (hy2 : y = ρ + (d * p) • x0) (hρ : QS S ρ ≡ c [ZMOD p]) (hNc : (p : ℤ) ∣ N - c)
    (hpc : ¬ (p : ℤ) ∣ c) (hpd : ¬ (p : ℤ) ∣ d) (hp2 : ¬ (p : ℤ) ∣ 2) (hpdet : ¬ (p : ℤ) ∣ S.det) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + (d * p) • x) - N ∧
      ¬ ∀ i, (p : ℤ) ∣ (ρ + (d * p) • x) i := by sorry

theorem b3_caseC {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (ρ : Fin 3 → ℤ) (D N : ℤ) (hpD : ¬ (p : ℤ) ∣ D) (hp2 : ¬ (p : ℤ) ∣ 2)
    (hpdet : ¬ (p : ℤ) ∣ S.det) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i := by sorry

theorem b3_one (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm) (d : ℕ) (hd : 0 < d)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓd : ¬ ℓ ∣ 2 * d * S.det.natAbs * (QS S e1).natAbs)
    (ρ : Fin 3 → ℤ) (hρd : ∀ i, ρ i ≡ e1 i [ZMOD d]) (hρℓ : QS S ρ ≡ QS S e1 [ZMOD ℓ])
    (i0 : Fin 3) (hi0 : (S *ᵥ e1) i0 ≠ 0) (K : ℕ)
    (hK : 2 * (((d * ℓ : ℕ) : ℤ) * (2 * (S *ᵥ e1) i0)).natAbs + 1 ≤ K)
    (J : ℕ) (hRJ : ((2 * d * S.det.natAbs : ℕ) : ℤ) ^ K ∣ (J : ℤ)) (hℓJ : (ℓ : ℤ) ∣ (J : ℤ))
    (A B k : ℤ) :
    LocalPrimRep S (d * ℓ) ρ (A * (J * k) ^ 2 + B * (J * k) + QS S e1) := by sorry

theorem localProgression (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) (d : ℕ) (hd : 0 < d)
    (ℓ : ℕ) (ρ₁ ρ₂ : Fin 3 → ℤ) (hℓ : ℓ.Prime) (hℓd : ¬ ℓ ∣ 2 * d * S.det.natAbs * (QS S e1).natAbs)
    (h1d : ∀ i, ρ₁ i ≡ e1 i [ZMOD d]) (h2d : ∀ i, ρ₂ i ≡ e1 i [ZMOD d])
    (h1ℓ : ∀ i, ρ₁ i ≡ e1 i [ZMOD ℓ]) (h2ℓ : QS S ρ₂ ≡ QS S e1 [ZMOD ℓ])
    (A B : ℤ) (bad : Finset ℕ) (hbad : ∀ q ∈ bad, q.Prime) (M : ℕ) (hM : 0 < M) :
    ∃ J : ℕ, 0 < J ∧ M ∣ J ∧ ∀ k : ℤ,
      LocalPrimRep S (d * ℓ) ρ₁ (A * (J * k) ^ 2 + B * (J * k) + QS S e1) ∧
      LocalPrimRep S (d * ℓ) ρ₂ (A * (J * k) ^ 2 + B * (J * k) + QS S e1) ∧
      ∀ q ∈ bad, padicValInt q (A * (J * k) ^ 2 + B * (J * k) + QS S e1) = padicValInt q (QS S e1) := by sorry

theorem ternaryCosetCollision_of_TCER (hT : TernaryCosetEventualRepresentation)
    (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) (d : ℕ) (hd : 0 < d)
    (p : Fin 3 → ℤ) (hp : p ≠ 0) (A B : ℤ) (hA : 0 < A) (hdisc : B ^ 2 - 4 * A * QS S e1 ≠ 0)
    (M : ℕ) (hM : 0 < M) :
    ∃ (k : ℤ) (x x' : Fin 3 → ℤ),
      QS S (e1 + (d : ℤ) • x) = A * (M * k) ^ 2 + B * (M * k) + QS S e1 ∧
      QS S (e1 + (d : ℤ) • x') = A * (M * k) ^ 2 + B * (M * k) + QS S e1 ∧
      p ⬝ᵥ (e1 + (d : ℤ) • x) ≠ p ⬝ᵥ (e1 + (d : ℤ) • x') := by sorry

/-! ## s56c extension (s56, 2026-09-25, agora; GATE26 Packet B1 (TCERSlice), statement frozen before installation, ruling R5).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s56c] ResearchUpgrade/TCERSlice.lean  md5 849e525ecddd154cae6de983f355b67e
theorem b1_common {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ∃ L : ℕ, 0 < L ∧ ∃ z : ι → ℤ, ∀ k, (z k : ℚ) = (L : ℚ) * f k := by sorry

theorem fixedCoset_slice (D : QuadraticGraphData n m r) (j0 : Fin m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 3 ≤ D.polarRank)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 v : Fin n → ℤ) (z0 : OutWit m r → ℤ) (hz0 : D.SolZ a0 z0)
    (hR0 : 0 < D.residual a0 (centreAt c0 C a0)) (Aq Bq : ℚ)
    (hline : ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = Aq * (t : ℚ) ^ 2 + Bq * t + D.residual a0 (centreAt c0 C a0))
    (hA : 0 < Aq) (hdisc : Bq ^ 2 - 4 * Aq * D.residual a0 (centreAt c0 C a0) ≠ 0) :
    ∃ (S : Matrix (Fin 3) (Fin 3) ℤ) (d M : ℕ) (p : Fin 3 → ℤ) (A B : ℤ) (α β γ : ℚ),
      S.IsSymm ∧ (∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < TCERBridge.QS S y) ∧ 0 < d ∧ 0 < M ∧ p ≠ 0 ∧
      0 < A ∧ B ^ 2 - 4 * A * TCERBridge.QS S TCERBridge.e1 ≠ 0 ∧ β ≠ 0 ∧
      ∀ (k : ℤ) (x : Fin 3 → ℤ),
        TCERBridge.QS S (TCERBridge.e1 + (d : ℤ) • x) = A * (M * k) ^ 2 + B * (M * k) + TCERBridge.QS S TCERBridge.e1 →
        ∃ z : OutWit m r → ℤ, D.SolZ (a0 + ((M : ℤ) * k) • v) z ∧
          (z (Sum.inl j0) : ℚ) = α + β * (p ⬝ᵥ (TCERBridge.e1 + (d : ℤ) • x) : ℤ) + γ * k := by sorry

/-! ## s56d extension (s56, 2026-09-25, agora; GATE26 C3/C4 capstones (TCERCapstones, TCERFullNF) and D2 (FullNFBranches), statements frozen before proof, ruling 15:51).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s56d] ResearchUpgrade/TCERCapstones.lean  md5 ba381a59bd72b953b09a2607a502c6f4
theorem lineCollision_rankThree_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation)
    (D : QuadraticGraphData n m r) (j0 : Fin m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 3 ≤ D.polarRank)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 v : Fin n → ℤ) (z0 : OutWit m r → ℤ) (hz0 : D.SolZ a0 z0)
    (hR0 : 0 < D.residual a0 (centreAt c0 C a0)) (Aq Bq : ℚ)
    (hline : ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = Aq * (t : ℚ) ^ 2 + Bq * t + D.residual a0 (centreAt c0 C a0))
    (hA : 0 < Aq) (hdisc : Bq ^ 2 - 4 * Aq * D.residual a0 (centreAt c0 C a0) ≠ 0) :
    ∃ (t : ℤ) (z z' : OutWit m r → ℤ), D.SolZ (a0 + t • v) z ∧ D.SolZ (a0 + t • v) z' ∧
      z (Sum.inl j0) ≠ z' (Sum.inl j0) := by sorry

theorem ccr_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) : ConstantResidualRigidity := by sorry

theorem definiteShellCriterion_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation)
    (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a)) :
    (D.Total ∧ D.OutputUnique) ↔
      ∃ R0 : ℚ, (∀ a, D.residual a (centreAt c0 C a) = R0) ∧
        ∃ (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ) (B : ℕ), 1 ≤ M ∧
          (∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) ∧ (∀ k i, (E k i : ℚ) = (M : ℚ) * C k i) ∧
          (∀ y : OutWit m r → ℤ, D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 → ∀ k, |y k| ≤ B) ∧
          ∀ ρ : Fin n → Fin M,
            ((D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E (fun i => ((ρ i : ℕ) : ℤ))).image
              outProj).card = 1 := by sorry

theorem definiteCommonSlopeNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → 2 ≤ D.polarRank → D.Defines f →
        CommonSlopeIntNF f := by sorry

theorem semidefiniteFullNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
      ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
      2 ≤ D.polarRank → D.Defines f → FullVectorCosetNF f := by sorry

theorem generalWeakNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) : GeneralWeakNF := by sorry

theorem sealedWeakNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → WeakVectorCosetNF f := by sorry

-- [s56d] ResearchUpgrade/TCERFullNF.lean  md5 bbc04e0dc0b5023f2e295819539ba6a5
theorem semidefiniteFullNF_allRanks_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
      ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
      D.Defines f → FullVectorCosetNF f := by sorry

-- [s56d] ResearchUpgrade/FullNFBranches.lean  md5 9f9514785140cb10a85f81d1d7c7ca68
def GeneralFullNF : Prop := sorry

def LinearBranchFullNF : Prop := sorry

def IsotropicBranchFullNF : Prop := sorry

def AnisotropicIndefiniteFullNF : Prop := sorry

def SemidefiniteFullNF : Prop := sorry

theorem generalFullNF_iff_branches :
    GeneralFullNF ↔
      LinearBranchFullNF ∧ IsotropicBranchFullNF ∧ AnisotropicIndefiniteFullNF ∧ SemidefiniteFullNF := by sorry

theorem generalFullNF_iff_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    GeneralFullNF ↔ LinearBranchFullNF ∧ IsotropicBranchFullNF ∧ AnisotropicIndefiniteFullNF := by sorry

/-! ## s56e extension (s56, 2026-09-25, agora; GATE26 A1.3–A1.5 compilers (CCRCompilers), statements frozen before proof, ruling 15:51).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s56e] ResearchUpgrade/CCRCompilers.lean  md5 c00d21be1a0b2f734b2010d6f7ef993d
def lineData (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) : QuadraticGraphData 1 m r := sorry

theorem lineData_zLin (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ) (k : OutWit m r) :
    (D.lineData a0 v).zLin t k = D.zLin (a0 + t 0 • v) k := by sorry

theorem lineData_aPart (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ) :
    (D.lineData a0 v).aPart t = D.aPart (a0 + t 0 • v) := by sorry

theorem lineData_solZ (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ)
    (z : OutWit m r → ℤ) : (D.lineData a0 v).SolZ t z ↔ D.SolZ (a0 + t 0 • v) z := by sorry

theorem lineData_zQuadQ (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (u : OutWit m r → ℚ) :
    (D.lineData a0 v).zQuadQ u = D.zQuadQ u := by sorry

theorem lineData_polarRank (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) :
    (D.lineData a0 v).polarRank = D.polarRank := by sorry

theorem lineData_isCentre (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ)
    (c : OutWit m r → ℚ) : (D.lineData a0 v).IsCentre t c ↔ D.IsCentre (a0 + t 0 • v) c := by sorry

theorem lineData_residual (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ)
    (c : OutWit m r → ℚ) : (D.lineData a0 v).residual t c = D.residual (a0 + t 0 • v) c := by sorry

theorem lineData_centreAt (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (a0 v : Fin n → ℤ)
    (t : Fin 1 → ℤ) :
    centreAt (centreAt c0 C a0) (fun k _ => ∑ i, C k i * (v i : ℚ)) t = centreAt c0 C (a0 + t 0 • v) := by sorry

theorem lineData_total (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (hT : D.Total) :
    (D.lineData a0 v).Total := by sorry

theorem lineData_outputUnique (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (hOU : D.OutputUnique) :
    (D.lineData a0 v).OutputUnique := by sorry

def reindexOut (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r) :
    QuadraticGraphData n m' r' := sorry

theorem reindexOut_eval (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (x : Vars n m' r' → ℤ) :
    (D.reindexOut σ).P.eval x = D.P.eval (x ∘ (Equiv.sumCongr (Equiv.refl (Fin n)) σ).symm) := by sorry

theorem reindexOut_solZ (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (a : Fin n → ℤ) (z : OutWit m' r' → ℤ) : (D.reindexOut σ).SolZ a z ↔ D.SolZ a (z ∘ σ.symm) := by sorry

theorem reindexOut_zQuadQ (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (u : OutWit m' r' → ℚ) : (D.reindexOut σ).zQuadQ u = D.zQuadQ (u ∘ σ.symm) := by sorry

theorem reindexOut_isCentre (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (a : Fin n → ℤ) (c : OutWit m' r' → ℚ) :
    (D.reindexOut σ).IsCentre a c ↔ D.IsCentre a (c ∘ σ.symm) := by sorry

theorem reindexOut_residual (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (a : Fin n → ℤ) (c : OutWit m' r' → ℚ) :
    (D.reindexOut σ).residual a c = D.residual a (c ∘ σ.symm) := by sorry

theorem reindexOut_total (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (hT : D.Total) : (D.reindexOut σ).Total := by sorry

theorem reindexOut_outputUnique_one (D : QuadraticGraphData n m r) {r' : ℕ} (σ : OutWit 1 r' ≃ OutWit m r)
    (j0 : Fin m) (hσ : σ (Sum.inl 0) = Sum.inl j0) (hOU : D.OutputUnique) :
    (D.reindexOut σ).OutputUnique := by sorry

theorem exists_outSelect (j0 : Fin m) :
    ∃ σ : OutWit 1 (m - 1 + r) ≃ OutWit m r, σ (Sum.inl 0) = Sum.inl j0 := by sorry

def CCR_oneInputOneOutput : Prop := sorry

theorem ccr_iff_oneInputOneOutput : ConstantResidualRigidity ↔ CCR_oneInputOneOutput := by sorry

/-! ## s57 extension (s57, 2026-09-25, agora; GATE27 A3/A4, B, C, D1/D2 (FullNFExtraction, IsotropicEichler, SplitRankTwo, GeneralFullNF), statements frozen before proof, ruling 21:23).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s57] ResearchUpgrade/FullNFExtraction.lean  md5 df5344e588f436725c9583f3fef4d68e
theorem linearBranchFullNF_holds : LinearBranchFullNF := by sorry

theorem anisotropicIndefiniteFullNF_holds : AnisotropicIndefiniteFullNF := by sorry

theorem generalFullNF_iff_isotropic_and_semidefinite :
    GeneralFullNF ↔ IsotropicBranchFullNF ∧ SemidefiniteFullNF := by sorry

theorem generalFullNF_iff_isotropic_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    GeneralFullNF ↔ IsotropicBranchFullNF := by sorry

-- [s57] ResearchUpgrade/IsotropicEichler.lean  md5 d4ac109912eeaeb905694c014f60d533
theorem zQuadQ_eichler {e v : OutWit m r → ℚ} (he : D.zQuadQ e = 0) (hev : D.zPolarQ e v = 0)
    (x : OutWit m r → ℚ) :
    D.zQuadQ (x + D.zPolarQ x e • v - (D.zPolarQ x v + D.zQuadQ v * D.zPolarQ x e) • e) = D.zQuadQ x := by sorry

theorem exists_isotropic_partner {e : OutWit m r → ℚ} (he : D.zQuadQ e = 0) (hne : ¬ D.InRadicalQ e) :
    ∃ e' : OutWit m r → ℚ, D.zQuadQ e' = 0 ∧ D.zPolarQ e e' = 1 := by sorry

theorem zPolarQ_sub_two_smul (u w : OutWit m r → ℚ) (α β : ℚ) (e₁ e₂ : OutWit m r → ℚ) :
    D.zPolarQ (u - α • e₁ - β • e₂) w = D.zPolarQ u w - α * D.zPolarQ e₁ w - β * D.zPolarQ e₂ w := by sorry

theorem polarRank_le_two_of_null_complement {e₁ e₂ : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0)
    (h₂ : D.zQuadQ e₂ = 0) (h₁₂ : D.zPolarQ e₁ e₂ ≠ 0)
    (hnull : ∀ w, D.zPolarQ e₁ w = 0 → D.zPolarQ e₂ w = 0 → D.zQuadQ w = 0) : D.polarRank ≤ 2 := by sorry

theorem three_le_polarRank_of_complement {e₁ e₂ w : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0)
    (h₂ : D.zQuadQ e₂ = 0) (h₁₂ : D.zPolarQ e₁ e₂ ≠ 0) (hw₁ : D.zPolarQ e₁ w = 0) (hw₂ : D.zPolarQ e₂ w = 0)
    (hw : D.zQuadQ w ≠ 0) : 3 ≤ D.polarRank := by sorry

theorem eichler_output_constraints (hOU : D.OutputUnique) {a : Fin n → ℤ} {c : OutWit m r → ℚ}
    (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z) {e v : OutWit m r → ℚ}
    (he : D.zQuadQ e = 0) (hev : D.zPolarQ e v = 0) (j : Fin m) :
    D.zPolarQ (toQ z - c) e * v (Sum.inl j) - D.zPolarQ (toQ z - c) v * e (Sum.inl j) = 0 ∧
      D.zQuadQ v * D.zPolarQ (toQ z - c) e * e (Sum.inl j) = 0 := by sorry

theorem outputs_vanish_on_perp (hOU : D.OutputUnique) {a : Fin n → ℤ} {c : OutWit m r → ℚ}
    (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z) {e : OutWit m r → ℚ}
    (he : D.zQuadQ e = 0) (hxe : D.zPolarQ (toQ z - c) e ≠ 0) (hrank : 3 ≤ D.polarRank)
    (v : OutWit m r → ℚ) (hv : D.zPolarQ e v = 0) (j : Fin m) : v (Sum.inl j) = 0 := by sorry

theorem false_of_offRadical_of_three_le_polarRank (hm : 0 < m) (hOU : D.OutputUnique) {a : Fin n → ℤ}
    {c : OutWit m r → ℚ} (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (hx : ¬ D.InRadicalQ (toQ z - c)) {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    (hrank : 3 ≤ D.polarRank) : False := by sorry

theorem isotropicBranchFullNF_of_three_le_polarRank :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → 3 ≤ D.polarRank →
      D.Defines f → FullVectorCosetNF f := by sorry

-- [s57] ResearchUpgrade/SplitRankTwo.lean  md5 6c7379d284723c3239f1ca70629f09a8
theorem exists_scaling_divisor (α β γ K : ℤ) (hF : α ≠ 0 ∨ β ≠ 0) (hK : 0 < K) :
    ∃ k₀ lam : ℤ, lam ≠ 0 ∧ lam ≠ 1 ∧ K ∣ lam - 1 ∧ lam ∣ α * k₀ ^ 2 + β * k₀ + γ := by sorry

theorem quad_const_of_three (α β γ k₀ lam : ℤ) (hlam : lam ≠ 0)
    (h1 : α * (k₀ + lam) ^ 2 + β * (k₀ + lam) + γ = α * k₀ ^ 2 + β * k₀ + γ)
    (h2 : α * (k₀ + 2 * lam) ^ 2 + β * (k₀ + 2 * lam) + γ = α * k₀ ^ 2 + β * k₀ + γ) :
    α = 0 ∧ β = 0 := by sorry

theorem hyperbolic_form_of_polarRank_le_two {e₁ e₂ : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0)
    (h₂ : D.zQuadQ e₂ = 0) (h₁₂ : D.zPolarQ e₁ e₂ = 1) (hrank : D.polarRank ≤ 2) (u : OutWit m r → ℚ) :
    D.zQuadQ u = D.zPolarQ u e₂ * D.zPolarQ u e₁ ∧
      D.InRadicalQ (u - D.zPolarQ u e₂ • e₁ - D.zPolarQ u e₁ • e₂) := by sorry

theorem zQuadQ_hyperbolic_section {e₁ e₂ ρ : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0) (h₂ : D.zQuadQ e₂ = 0)
    (h₁₂ : D.zPolarQ e₁ e₂ = 1) (hρ : D.InRadicalQ ρ) (X Y : ℚ) :
    D.zQuadQ (X • e₁ + Y • e₂ + ρ) = X * Y := by sorry

theorem constResidual_of_isotropic_polarRank_le_two (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    (hrank : D.polarRank ≤ 2) (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a)) :
    ∃ R0 : ℚ, ∀ a : Fin n → ℤ, D.residual a (centreFamily c₀ cs a) = R0 := by sorry

theorem isotropicBranchFullNF_of_polarRank_le_two :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → D.polarRank ≤ 2 →
      D.Defines f → FullVectorCosetNF f := by sorry

-- [s57] ResearchUpgrade/GeneralFullNF.lean  md5 9208a5edea46f154a00d450edc5daae1
theorem isotropicBranchFullNF_holds : IsotropicBranchFullNF := by sorry

theorem generalFullNF_iff_semidefiniteFullNF : GeneralFullNF ↔ SemidefiniteFullNF := by sorry

theorem generalFullNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) : GeneralFullNF := by sorry

theorem sealedFullNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → FullVectorCosetNF f := by sorry

/-! ## s57b extension (s57, 2026-09-25, agora; GATE27 D3 controls (FullNFControls), statements frozen before proof, ruling 22:00).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s57b] ResearchUpgrade/FullNFControls.lean  md5 80937e497171acf5f03a92ecbc2404b0
def split1 : QuadraticGraphData 0 1 1 := sorry

def split2 : QuadraticGraphData 0 1 1 := sorry

theorem split1_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 1 → ℤ) :
    split1.P.eval (pt a b u) = b 0 * (2 * u 0 + 1) := by sorry

theorem split2_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 1 → ℤ) :
    split2.P.eval (pt a b u) = (4 * b 0 + 1) * (4 * u 0 + 1) - 1 := by sorry

theorem split1_defines : split1.Defines (fun _ => 0) := by sorry

theorem split2_defines : split2.Defines (fun _ => 0) := by sorry

theorem split1_zPolarQ (v w : OutWit 1 1 → ℚ) :
    split1.zPolarQ v w = 2 * (v (Sum.inl 0) * w (Sum.inr 0) + v (Sum.inr 0) * w (Sum.inl 0)) := by sorry

theorem split2_zPolarQ (v w : OutWit 1 1 → ℚ) :
    split2.zPolarQ v w = 16 * (v (Sum.inl 0) * w (Sum.inr 0) + v (Sum.inr 0) * w (Sum.inl 0)) := by sorry

theorem split1_zQuadQ (v : OutWit 1 1 → ℚ) : split1.zQuadQ v = 2 * v (Sum.inl 0) * v (Sum.inr 0) := by sorry

theorem split2_zQuadQ (v : OutWit 1 1 → ℚ) : split2.zQuadQ v = 16 * v (Sum.inl 0) * v (Sum.inr 0) := by sorry

theorem split1_zLinQ (a : Fin 0 → ℤ) (w : OutWit 1 1 → ℚ) : split1.zLinQ a w = w (Sum.inl 0) := by sorry

theorem split2_zLinQ (a : Fin 0 → ℤ) (w : OutWit 1 1 → ℚ) :
    split2.zLinQ a w = 4 * w (Sum.inl 0) + 4 * w (Sum.inr 0) := by sorry

def eb : OutWit 1 1 → ℚ := sorry

def eu : OutWit 1 1 → ℚ := sorry

theorem rank_hypothesis_needed :
    ¬ (∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (a : Fin n → ℤ) (c : OutWit m r → ℚ) (z : OutWit m r → ℤ)
        (e₀ : OutWit m r → ℚ), 0 < m → D.OutputUnique → D.IsCentre a c → D.SolZ a z → ¬ D.InRadicalQ (toQ z - c) →
        D.zQuadQ e₀ = 0 → ¬ D.InRadicalQ e₀ → False) := by sorry

theorem residual_zero_not_forced :
    ¬ (∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)) (c₀ : OutWit m r → ℚ)
        (cs : Fin n → OutWit m r → ℚ), 0 < m → D.Defines f → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) →
        D.polarRank ≤ 2 → (∀ a, D.IsCentre a (centreFamily c₀ cs a)) → ∀ a, D.residual a (centreFamily c₀ cs a) = 0) := by sorry

/-! ## s58 extension (s58, 2026-09-26, agora; GATE28 A4, B1-B4, C1-C4, D1-D3 (CommonSlopeForward, CommonSlopeCompiler, VectorClassification), statements frozen before proof (freeze G1-G3)).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s58] ResearchUpgrade/CommonSlopeForward.lean  md5 f9ddbfdf178aada9db4a788d0d756bac
theorem false_of_isotropic_of_three_le_polarRank (hm : 0 < m) (hOU : D.OutputUnique)
    {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    (hrank : 3 ≤ D.polarRank) : False := by sorry

theorem intAffine_of_ratAffine {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (c₀ : Fin m → ℚ) (cs : Fin n → Fin m → ℚ)
    (h : ∀ (a : Fin n → ℤ) (j : Fin m), ((f a j : ℤ) : ℚ) = c₀ j + ∑ i, (a i : ℚ) * cs i j) :
    (∀ j, ((f 0 j : ℤ) : ℚ) = c₀ j) ∧
    (∀ i j, ((f (Pi.single i 1) j - f 0 j : ℤ) : ℚ) = cs i j) ∧
    ∀ a : Fin n → ℤ, f a = f 0 + (Matrix.of fun j i => f (Pi.single i 1) j - f 0 j) *ᵥ a := by sorry

theorem commonSlopeIntNF_of_ratAffine {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (c₀ : Fin m → ℚ) (cs : Fin n → Fin m → ℚ)
    (h : ∀ (a : Fin n → ℤ) (j : Fin m), ((f a j : ℤ) : ℚ) = c₀ j + ∑ i, (a i : ℚ) * cs i j) :
    CommonSlopeIntNF f := by sorry

theorem commonSlopeIntNF_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    CommonSlopeIntNF f := by sorry

theorem isotropic_three_le_polarRank_not_defines :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → 3 ≤ D.polarRank →
      ¬ D.Defines f := by sorry

theorem isotropicRankTwoCommonSlope_holds :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → D.polarRank ≤ 2 →
      D.Defines f → CommonSlopeIntNF f := by sorry

theorem anisotropicIndefiniteCommonSlope_holds :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x) →
      (∃ p, 0 < D.zQuadQ p) → (∃ q, D.zQuadQ q < 0) → D.Defines f → CommonSlopeIntNF f := by sorry

theorem semidefiniteCommonSlopeNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
      ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
      2 ≤ D.polarRank → D.Defines f → CommonSlopeIntNF f := by sorry

theorem commonSlopeNF_of_TCER_of_two_le (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      2 ≤ m → D.Defines f → CommonSlopeIntNF f := by sorry

theorem sealedCommonSlopeNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)), 2 ≤ m →
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → CommonSlopeIntNF f := by sorry

-- [s58] ResearchUpgrade/CommonSlopeCompiler.lean  md5 be5564e003943020ea6a4695838f4eb5
theorem int_mul_sub_one_nonneg (x : ℤ) : 0 ≤ x * (x - 1) := by sorry

theorem oneHot_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℤ) :
    ((∑ i, e i) - 1) ^ 2 + ∑ i, e i * (e i - 1) = 0 ↔ ∃ i₀, e = Pi.single i₀ 1 := by sorry

theorem oneHot_nonBoolean_control :
    (∑ i, (![-1, 2] : Fin 2 → ℤ) i) = 1 ∧
      ((∑ i, (![-1, 2] : Fin 2 → ℤ) i) - 1) ^ 2
        + ∑ i, (![-1, 2] : Fin 2 → ℤ) i * ((![-1, 2] : Fin 2 → ℤ) i - 1) = 4 := by sorry

noncomputable def slopeEncoder {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) :
    MvPolynomial (Fin (n + m) ⊕ (Fin n ⊕ (Fin n → Fin M))) ℤ := sorry

theorem sc_td_X (i : σ) : (X i : MvPolynomial σ ℤ).totalDegree ≤ 1 := by sorry

theorem sc_td_CX (c : ℤ) (i : σ) : (C c * X i : MvPolynomial σ ℤ).totalDegree ≤ 1 := by sorry

theorem sc_td_sub {p q : MvPolynomial σ ℤ} {k : ℕ} (hp : p.totalDegree ≤ k) (hq : q.totalDegree ≤ k) :
    (p - q).totalDegree ≤ k := by sorry

theorem sc_td_add {p q : MvPolynomial σ ℤ} {k : ℕ} (hp : p.totalDegree ≤ k) (hq : q.totalDegree ≤ k) :
    (p + q).totalDegree ≤ k := by sorry

theorem sc_td_sum {ι : Type*} [Fintype ι] (g : ι → MvPolynomial σ ℤ) {k : ℕ}
    (h : ∀ x, (g x).totalDegree ≤ k) : (∑ x, g x).totalDegree ≤ k := by sorry

theorem sc_td_sq {p : MvPolynomial σ ℤ} (h : p.totalDegree ≤ 1) : (p ^ 2).totalDegree ≤ 2 := by sorry

theorem sc_td_one : (1 : MvPolynomial σ ℤ).totalDegree ≤ 1 := by sorry

theorem slopeEncoder_totalDegree {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) : (slopeEncoder M B β).totalDegree ≤ 2 := by sorry

theorem slopeEncoder_eval {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin n → ℤ)
    (e : (Fin n → Fin M) → ℤ) :
    MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β)
      = ((∑ ρ, e ρ) - 1) ^ 2 + ∑ ρ, e ρ * (e ρ - 1)
        + ∑ i, (a i - (M : ℤ) * u i - ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ) ^ 2
        + ∑ j, ((M : ℤ) * b j - ∑ i, B j i * a i
            - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ) ^ 2 := by sorry

theorem slopeEncoder_zero_iff {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin n → ℤ)
    (e : (Fin n → Fin M) → ℤ) :
    MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0 ↔
      ∃ ρ : Fin n → Fin M, e = Pi.single ρ 1 ∧ (∀ i, a i = (M : ℤ) * u i + ((ρ i : ℕ) : ℤ)) ∧
        ∀ j, (M : ℤ) * b j
          = ∑ i, B j i * a i + ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) := by sorry

theorem slopeEncoder_graph_iff {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (M : ℕ)
    (B : Matrix (Fin m) (Fin n) ℤ) (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t)
    (a : Fin n → ℤ) (b : Fin m → ℤ) :
    b = f a ↔ ∃ (u : Fin n → ℤ) (e : (Fin n → Fin M) → ℤ),
      MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e))
        (slopeEncoder M B (fun ρ => f (fun i => ((ρ i : ℕ) : ℤ)))) = 0 := by sorry

theorem slopeEncoder_witness_unique {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (hM : 1 ≤ M) {a : Fin n → ℤ} {b : Fin m → ℤ}
    {u u' : Fin n → ℤ} {e e' : (Fin n → Fin M) → ℤ}
    (h : MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0)
    (h' : MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u' e')) (slopeEncoder M B β) = 0) :
    u = u' ∧ e = e' := by sorry

theorem singleQuadratic_of_poly {n m : ℕ} {W : Type} [Fintype W]
    (P : MvPolynomial (Fin (n + m) ⊕ W) ℤ) (hP : P.totalDegree ≤ 2) (f : (Fin n → ℤ) → (Fin m → ℤ))
    (h : ∀ (a : Fin n → ℤ) (b : Fin m → ℤ),
      b = f a ↔ ∃ w : W → ℤ, MvPolynomial.eval (Sum.elim (pairVec a b) w) P = 0) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f := by sorry

theorem singleQuadratic_of_commonSlope_witnesses {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (M : ℕ)
    (B : Matrix (Fin m) (Fin n) ℤ) (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t) :
    ∃ P : MvPolynomial (Fin (n + m) ⊕ Fin (n + M ^ n)) ℤ, P.totalDegree ≤ 2 ∧
      ∀ v : Fin (n + m) → ℤ, v ∈ DiophCompression.graphVecZZ f ↔
        ∃ y : Fin (n + M ^ n) → ℤ, MvPolynomial.eval (Sum.elim v y) P = 0 := by sorry

theorem singleQuadratic_of_commonSlope {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : CommonSlopeIntNF f) : DiophCompression.SingleQuadraticDefinableFunctionZZ f := by sorry

-- [s58] ResearchUpgrade/VectorClassification.lean  md5 9cc7a4c54e6e6b6c918b4265719d8b35
theorem singleQuadratic_iff_commonSlope_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)), 2 ≤ m →
      (DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ CommonSlopeIntNF f) := by sorry

def sqFn : (Fin 1 → ℤ) → (Fin 1 → ℤ) := sorry

def sqPadFn : (Fin 1 → ℤ) → (Fin 2 → ℤ) := sorry

theorem sqFn_singleQuadratic : DiophCompression.SingleQuadraticDefinableFunctionZZ sqFn := by sorry

theorem vc_one_add_smul (x y : ℤ) (M : ℕ) :
    ((fun _ => x) + (M : ℤ) • (fun _ => y) : Fin 1 → ℤ) = fun _ => x + (M : ℤ) * y := by sorry

theorem sqPadFn_not_commonSlope : ¬ CommonSlopeIntNF sqPadFn := by sorry

theorem sqPadFn_not_singleQuadratic_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ¬ DiophCompression.SingleQuadraticDefinableFunctionZZ sqPadFn := by sorry

def parityFn : (Fin 1 → ℤ) → (Fin 1 → ℤ) := sorry

theorem parityFn_apply (x : ℤ) (j : Fin 1) :
    parityFn (fun _ => x) j = if x % 2 = 0 then x / 2 else (1 - 3 * x) / 2 := by sorry

theorem parityFn_graph (a b : ℤ) :
    (2 * b - a) * (2 * b + 3 * a - 1) = 0 ↔ b = parityFn (fun _ => a) 0 := by sorry

theorem parityFn_singleQuadratic : DiophCompression.SingleQuadraticDefinableFunctionZZ parityFn := by sorry

theorem parityFn_fullVectorCosetNF : FullVectorCosetNF parityFn := by sorry

theorem parityFn_not_commonSlope : ¬ CommonSlopeIntNF parityFn := by sorry

theorem not_commonSlope_of_fullVectorCosetNF :
    ¬ ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → FullVectorCosetNF f → CommonSlopeIntNF f := by sorry

theorem cs_decomp {n M : ℕ} (hM : 1 ≤ M) (a : Fin n → ℤ) :
    ∃ (ρ : Fin n → Fin M) (u : Fin n → ℤ), a = (fun i => ((ρ i : ℕ) : ℤ)) + (M : ℤ) • u := by sorry

theorem cs_decomp_unique {n M : ℕ} (hM : 1 ≤ M) {ρ σ : Fin n → Fin M} {u v : Fin n → ℤ}
    (h : (fun i => ((ρ i : ℕ) : ℤ)) + (M : ℤ) • u = (fun i => ((σ i : ℕ) : ℤ)) + (M : ℤ) • v) :
    ρ = σ ∧ u = v := by sorry

theorem commonSlope_range {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {M : ℕ}
    {B : Matrix (Fin m) (Fin n) ℤ} (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t) :
    Set.range f = ⋃ ρ : Fin n → Fin M,
      Set.range fun t : Fin n → ℤ => f (fun i => ((ρ i : ℕ) : ℤ)) + B *ᵥ t := by sorry

theorem commonSlope_injective_iff {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {M : ℕ}
    {B : Matrix (Fin m) (Fin n) ℤ} (hM : 1 ≤ M)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t) :
    Function.Injective f ↔
      Function.Injective (fun t : Fin n → ℤ => B *ᵥ t) ∧
        ∀ ρ σ : Fin n → Fin M, ρ ≠ σ → ∀ t : Fin n → ℤ,
          f (fun i => ((ρ i : ℕ) : ℤ)) - f (fun i => ((σ i : ℕ) : ℤ)) ≠ B *ᵥ t := by sorry

theorem commonSlope_injective_dim {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : CommonSlopeIntNF f) (hinj : Function.Injective f) : n ≤ m := by sorry

/-! ## s59 extension (s59, 2026-09-27, agora; GATE29 B1-B4, C1-C4, D1-D3 (ScalarRoots, ScalarClassification, SlopeStructure), statements frozen before proof (freeze H1-H3)).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s59] ResearchUpgrade/ScalarRoots.lean  md5 52b2f2e442c2141d95ffaaccfc0ce5db
def ParityAffineNF {n : ℕ} (F : (Fin n → ℤ) → ℤ) : Prop := sorry

theorem affine_dvd_iff_sub {n : ℕ} (k : ℤ) (w : Fin n → ℤ) (e : ℤ) {x₀ : Fin n → ℤ}
    (h₀ : k ∣ w ⬝ᵥ x₀ + e) (x : Fin n → ℤ) : k ∣ w ⬝ᵥ x + e ↔ k ∣ w ⬝ᵥ (x - x₀) := by sorry

theorem affine_dvd_add_smul {n : ℕ} (k : ℤ) (w : Fin n → ℤ) (e : ℤ) {x : Fin n → ℤ}
    (h : k ∣ w ⬝ᵥ x + e) (t : Fin n → ℤ) : k ∣ w ⬝ᵥ (x + k • t) + e := by sorry

theorem affine_eq_of_eq_on_coset {n : ℕ} {k : ℤ} (hk : k ≠ 0) {w w' : Fin n → ℤ} {e e' : ℤ} (x₀ : Fin n → ℤ)
    (h : ∀ t : Fin n → ℤ, w ⬝ᵥ (x₀ + k • t) + e = w' ⬝ᵥ (x₀ + k • t) + e') : w = w' ∧ e = e' := by sorry

theorem addSubgroup_two_coset_cover {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (b : G)
    (hcov : ∀ g : G, g ∈ H ∨ g - b ∈ K) (hdisj : ∀ g : G, g ∈ H → g - b ∉ K) :
    H = K ∧ b ∉ H ∧ (∀ g : G, g ∈ H ∨ g - b ∈ H) ∧ ∀ g : G, g + g ∈ H := by sorry

theorem rn_two_roots {n : ℕ} {F : (Fin n → ℤ) → ℤ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ) (ha : a ≠ 0)
    (hF : ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = F x) :
    ∃ (ℓ : Fin n → ℤ) (s : ℤ), ∀ (x : Fin n → ℤ) (y : ℤ),
      Rn a β d E φ g x y ↔
        (2 * a * y = -(β ⬝ᵥ x + d) + (ℓ ⬝ᵥ x + s) ∨ 2 * a * y = -(β ⬝ᵥ x + d) - (ℓ ⬝ᵥ x + s)) := by sorry

theorem globalQuadratic_of_rn_zero {n : ℕ} {F : (Fin n → ℤ) → ℤ} (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ)
    (hF : ∀ (x : Fin n → ℤ) (y : ℤ), Rn 0 β d E φ g x y ↔ y = F x) : GlobalQuadratic F := by sorry

theorem globalQuadratic_of_int_affine {n : ℕ} {F : (Fin n → ℤ) → ℤ} {k : ℤ} (hk : k ≠ 0)
    (w : Fin n → ℤ) (e : ℤ) (h : ∀ x : Fin n → ℤ, k * F x = w ⬝ᵥ x + e) : GlobalQuadratic F := by sorry

theorem rn_classify {n : ℕ} {F : (Fin n → ℤ) → ℤ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ)
    (hF : ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = F x) :
    GlobalQuadratic F ∨ ParityAffineNF F := by sorry

theorem parityFn_parityAffine : ParityAffineNF (scalarOut parityFn) := by sorry

theorem plusMinus_not_relUnique : ¬ RelUnique (Rn (n := by sorry

theorem sameParity_not_function :
    ¬ ∃ F : ℤ → ℤ, ∀ x y : ℤ, (2 * y - x) * (2 * y - x - 2) = 0 ↔ y = F x := by sorry

theorem modThree_not_total : ¬ ∀ x : ℤ, ∃ y : ℤ, (3 * y - x) * (3 * y - x + 1) = 0 := by sorry

-- [s59] ResearchUpgrade/ScalarClassification.lean  md5 96135873af910d0f3529e880cd3d018c
theorem commonSlope_of_TCER_of_two_le_polarRank (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) → 2 ≤ D.polarRank → D.Defines f → CommonSlopeIntNF f := by sorry

theorem scalar_commonSlope_or_rn_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n r : ℕ) (D : QuadraticGraphData n 1 r) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), D.Defines f →
      CommonSlopeIntNF f ∨ ∃ (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ),
        ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = scalarOut f x := by sorry

theorem sealed_scalar_commonSlope_or_rn_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n : ℕ) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), DiophCompression.SingleQuadraticDefinableFunctionZZ f →
      CommonSlopeIntNF f ∨ ∃ (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ),
        ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = scalarOut f x := by sorry

theorem zeroWitness_of_globalQuadratic {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : GlobalQuadratic (scalarOut f)) :
    ∃ P : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ, P.totalDegree ≤ 2 ∧
      ∀ (a : Fin n → ℤ) (b : Fin 1 → ℤ), b = f a ↔ MvPolynomial.eval (Sum.elim (pairVec a b) 0) P = 0 := by sorry

theorem zeroWitness_of_parityAffine {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : ParityAffineNF (scalarOut f)) :
    ∃ P : MvPolynomial (Fin (n + 1) ⊕ Fin 0) ℤ, P.totalDegree ≤ 2 ∧
      ∀ (a : Fin n → ℤ) (b : Fin 1 → ℤ), b = f a ↔ MvPolynomial.eval (Sum.elim (pairVec a b) 0) P = 0 := by sorry

theorem singleQuadratic_of_scalarFamilies {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : CommonSlopeIntNF f ∨ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f)) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f := by sorry

theorem sealed_scalarFamilies_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n : ℕ) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), DiophCompression.SingleQuadraticDefinableFunctionZZ f →
      CommonSlopeIntNF f ∨ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f) := by sorry

theorem scalar_singleQuadratic_iff_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n : ℕ) (f : (Fin n → ℤ) → (Fin 1 → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔
        (CommonSlopeIntNF f ∨ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f)) := by sorry

theorem commonSlopeIntNF_of_zero_outputs {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) : CommonSlopeIntNF f := by sorry

theorem singleQuadratic_iff_commonSlope_of_TCER_of_ne_one (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)), m ≠ 1 →
      (DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ CommonSlopeIntNF f) := by sorry

-- [s59] ResearchUpgrade/SlopeStructure.lean  md5 feb235139ce2dad765021510fc45c18e
def padZero {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : (Fin n → ℤ) → (Fin (m + 1) → ℤ) := sorry

theorem commonSlope_padZero_iff {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    CommonSlopeIntNF (padZero f) ↔ CommonSlopeIntNF f := by sorry

theorem singleQuadratic_padZero_iff_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ (padZero f) ↔ CommonSlopeIntNF f := by sorry

theorem sqPadFn_eq_padZero : sqPadFn = padZero sqFn := by sorry

theorem sqFn_not_commonSlope : ¬ CommonSlopeIntNF sqFn := by sorry

theorem sqPadFn_not_singleQuadratic_of_padding (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ¬ DiophCompression.SingleQuadraticDefinableFunctionZZ sqPadFn := by sorry

theorem commonSlope_comp_data {n m k : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {g : (Fin m → ℤ) → (Fin k → ℤ)}
    (M N : ℕ) (B : Matrix (Fin m) (Fin n) ℤ) (C : Matrix (Fin k) (Fin m) ℤ)
    (hf : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t)
    (hg : ∀ y s : Fin m → ℤ, g (y + (N : ℤ) • s) = g y + C *ᵥ s) :
    ∀ a t : Fin n → ℤ, g (f (a + ((M * N : ℕ) : ℤ) • t)) = g (f a) + (C * B) *ᵥ t := by sorry

theorem commonSlope_comp {n m k : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {g : (Fin m → ℤ) → (Fin k → ℤ)}
    (hf : CommonSlopeIntNF f) (hg : CommonSlopeIntNF g) : CommonSlopeIntNF (g ∘ f) := by sorry

def slopeUnknownQuad {R : Type*} [CommRing R] {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (b : Fin m → R) (u : Fin n → R) (e : (Fin n → Fin M) → R) : R := sorry

theorem slopeEncoder_eval_scale {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin n → ℤ)
    (e : (Fin n → Fin M) → ℤ) (t : ℤ) :
    MvPolynomial.eval (Sum.elim (pairVec a (t • b)) (Sum.elim (t • u) (t • e))) (slopeEncoder M B β)
      = t ^ 2 * slopeUnknownQuad M B β b u e
        + t * (-3 * ∑ ρ, e ρ - 2 * ∑ i, a i * ((M : ℤ) * u i + ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ)
          - 2 * ∑ j, (∑ i, B j i * a i)
              * ((M : ℤ) * b j - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ))
        + MvPolynomial.eval (Sum.elim (pairVec a 0) (Sum.elim 0 0)) (slopeEncoder M B β) := by sorry

theorem slopeUnknownQuad_nonneg {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (b : Fin m → ℚ) (u : Fin n → ℚ) (e : (Fin n → Fin M) → ℚ) :
    0 ≤ slopeUnknownQuad M B β b u e := by sorry

theorem slopeUnknownQuad_eq_zero {n m : ℕ} (M : ℕ) (hM : 1 ≤ M) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (b : Fin m → ℚ) (u : Fin n → ℚ) (e : (Fin n → Fin M) → ℚ)
    (h : slopeUnknownQuad M B β b u e = 0) : b = 0 ∧ u = 0 ∧ e = 0 := by sorry

theorem commonSlope_posDef_presentation {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : CommonSlopeIntNF f) :
    ∃ (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ) (β : (Fin n → Fin M) → Fin m → ℤ), 1 ≤ M ∧
      (∀ (a : Fin n → ℤ) (b : Fin m → ℤ), b = f a ↔
        ∃ (u : Fin n → ℤ) (e : (Fin n → Fin M) → ℤ),
          MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0) ∧
      (∀ (a : Fin n → ℤ) (b : Fin m → ℤ) (u u' : Fin n → ℤ) (e e' : (Fin n → Fin M) → ℤ),
        MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0 →
        MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u' e')) (slopeEncoder M B β) = 0 → u = u' ∧ e = e') ∧
      (∀ (b : Fin m → ℚ) (u : Fin n → ℚ) (e : (Fin n → Fin M) → ℚ),
        slopeUnknownQuad M B β b u e = 0 → b = 0 ∧ u = 0 ∧ e = 0) := by sorry

/-! ## s60 extension (s60, 2026-09-28, agora; GATE30 B1-B4 (WitnessCount), statements frozen before proof (freeze H4)).
Statements of every `theorem`/`def` in the module below, cut by statement_diff.py's own rule
from the production text; bodies `sorry`.  Not compiled.  Module md5 at freeze time is recorded per block. -/

-- [s60] ResearchUpgrade/WitnessCount.lean  md5 026716ded7fc12ec987f2a91c85c1300
def SingleQuadraticWithWitnessesZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (r : ℕ) : Prop := sorry

theorem singleQuadratic_iff_exists_witnesses {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ ∃ r, SingleQuadraticWithWitnessesZZ f r := by sorry

theorem graphData_of_witnesses {n m r : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : SingleQuadraticWithWitnessesZZ f r) : ∃ D : QuadraticGraphData n m r, D.Defines f := by sorry

theorem scalar_rn_of_polarRank_le_one :
    ∀ (n r : ℕ) (D : QuadraticGraphData n 1 r) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), D.Defines f → D.polarRank ≤ 1 →
      ∃ (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ),
        ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = scalarOut f x := by sorry

theorem zeroWitness_iff {n : ℕ} (f : (Fin n → ℤ) → (Fin 1 → ℤ)) :
    SingleQuadraticWithWitnessesZZ f 0 ↔ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f) := by sorry

def UniqueWitnessSingleQuadraticZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop := sorry

theorem existsUnique_of_uniqueWitness {n m r : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (P : MPUP.Poly (n + m) r)
    (hrep : DiophCompression.RepresentsZZ P (DiophCompression.graphVecZZ f))
    (hu : ∀ (v : Fin (n + m) → ℤ) (y y' : Fin r → ℤ),
      DiophCompression.evalAtZZ P v y = 0 → DiophCompression.evalAtZZ P v y' = 0 → y = y')
    (a : Fin n → ℤ) :
    ∃! p : (Fin m → ℤ) × (Fin r → ℤ), DiophCompression.evalAtZZ P (pairVec a p.1) p.2 = 0 := by sorry

theorem uniqueWitness_of_commonSlope {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : CommonSlopeIntNF f) :
    UniqueWitnessSingleQuadraticZZ f := by sorry

theorem uniqueWitness_of_zeroWitness {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : SingleQuadraticWithWitnessesZZ f 0) :
    UniqueWitnessSingleQuadraticZZ f := by sorry

theorem singleQuadratic_iff_uniqueWitness_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ UniqueWitnessSingleQuadraticZZ f := by sorry

def floorThird : (Fin 1 → ℤ) → (Fin 1 → ℤ) := sorry

noncomputable def floorThirdPoly : MPUP.Poly (1 + 1) 1 := sorry

theorem floorThirdPoly_eval (v : Fin (1 + 1) → ℤ) (y : Fin 1 → ℤ) :
    DiophCompression.evalAtZZ floorThirdPoly v y = (3 * v 1 - v 0 + 1) ^ 2 + y 0 ^ 2 - 1 := by sorry

theorem floorThird_oneWitness : SingleQuadraticWithWitnessesZZ floorThird 1 := by sorry

theorem floorThirdPoly_two_witnesses :
    DiophCompression.evalAtZZ floorThirdPoly (pairVec (fun _ => 1) (fun _ => 0)) (fun _ => 1) = 0 ∧
    DiophCompression.evalAtZZ floorThirdPoly (pairVec (fun _ => 1) (fun _ => 0)) (fun _ => -1) = 0 := by sorry

theorem floorThird_not_zeroWitness : ¬ SingleQuadraticWithWitnessesZZ floorThird 0 := by sorry

theorem floorThird_min_witnesses :
    SingleQuadraticWithWitnessesZZ floorThird 1 ∧ ¬ SingleQuadraticWithWitnessesZZ floorThird 0 := by sorry

