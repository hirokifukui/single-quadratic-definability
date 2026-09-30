/-
  NoWitnessCompiler.lean — s52.  R41-B2: from a datum with `r` witnesses whose witness
  directions are all radical, CONSTRUCT the witness-free datum `QuadraticGraphData n 1 0`
  and transport the graph, `Defines`, totality and output-uniqueness across it.

  This returns a new presentation; it is not a `Prop` whose conclusion is a normal form.
  The witness count goes DOWN to zero — nothing is encoded as a sum of squares, and the
  `m = 0` case is not pushed into this compiler.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.NoWitnessDimension
import ResearchUpgrade.WitnessInvariance

namespace DiophCompression.ResearchUpgrade
namespace QuadraticGraphData

open Matrix

variable {n r : ℕ} (D : QuadraticGraphData n 1 r)

/-- Evaluating at ZERO witnesses is already a `Pn` in the restricted coefficients. -/
theorem eval_zeroWitness_eq_Pn (x : Fin n → ℤ) (y : ℤ) :
    D.P.eval (pt x (fun _ => y) (0 : Fin r → ℤ))
      = Pn (D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)))
           (fun i => D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0))
                   + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i))
           (D.P.l (Sum.inr (Sum.inl 0)))
           (fun i j => D.P.Q (Sum.inl i) (Sum.inl j))
           (fun i => D.P.l (Sum.inl i))
           D.P.c x y := by
  classical
  rw [D.eval_split x (fun _ => y) (0 : Fin r → ℤ)]
  simp only [zQuad, zLin, aPart, Pn, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  have h1 : ∑ i, x i * (D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0))
        + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i))
      = ∑ i, (D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0))
        + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i)) * x i :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, x i * (D.P.Q (Sum.inl i) (Sum.inl j) * x j)
      = ∑ i, x i * ∑ j, D.P.Q (Sum.inl i) (Sum.inl j) * x j :=
    Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [h1, h2]
  ring

/-- The inclusion of the witness-free variables into the original ones. -/
def inclNoWit : Vars n 1 0 → Vars n 1 r :=
  Sum.elim (fun i => Sum.inl i)
    (fun z => Sum.inr (Sum.elim (fun j : Fin 1 => Sum.inl j) (fun k : Fin 0 => k.elim0) z))

/-- **R41-B2 — the compiler.**  A NEW datum with the witness block deleted: `r` becomes `0`,
the same `n` and `m = 1`, the same coefficients restricted.  No witness is added and no
sum-of-squares encoding is used. -/
def noWitnessData : QuadraticGraphData n 1 0 where
  P := { c := D.P.c
         l := fun k => D.P.l (inclNoWit k)
         Q := fun k k' => D.P.Q (inclNoWit k) (inclNoWit k') }

theorem noWitnessData_eval (x : Fin n → ℤ) (y : ℤ) (u : Fin 0 → ℤ) :
    (D.noWitnessData).P.eval (pt x (fun _ => y) u)
      = D.P.eval (pt x (fun _ => y) (0 : Fin r → ℤ)) := by
  rw [(D.noWitnessData).eval_eq_Pn x y u, D.eval_zeroWitness_eq_Pn x y]
  rfl

/-- The graphs agree, so `Defines`, totality and output-uniqueness all transport. -/
theorem noWitnessData_graph_iff
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x)
    (a : Fin n → ℤ) (b : Fin 1 → ℤ) :
    D.Graph a b ↔ (D.noWitnessData).Graph a b := by
  have hb : b = fun _ => b 0 := by funext j; rw [Subsingleton.elim j 0]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨fun k => k.elim0, ?_⟩
    have h0 : D.P.eval (pt a b (0 : Fin r → ℤ)) = 0 := by
      rw [← D.eval_witness_invariant Nat.one_pos hOU hT hQ hrad a b u]; exact hu
    show (D.noWitnessData).P.eval (pt a b (fun k => k.elim0)) = 0
    rw [hb] at h0 ⊢
    rw [D.noWitnessData_eval a (b 0) (fun k => k.elim0)]
    exact h0
  · rintro ⟨u₀, hu₀⟩
    refine ⟨(0 : Fin r → ℤ), ?_⟩
    have h0 : (D.noWitnessData).P.eval (pt a b u₀) = 0 := hu₀
    show D.P.eval (pt a b (0 : Fin r → ℤ)) = 0
    rw [hb] at h0 ⊢
    rw [← D.noWitnessData_eval a (b 0) u₀]
    exact h0

theorem noWitnessData_defines
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x)
    {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) :
    (D.noWitnessData).Defines f := by
  intro a b
  rw [← D.noWitnessData_graph_iff hOU hT hQ hrad a b]
  exact hf a b

theorem noWitnessData_total
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x) :
    (D.noWitnessData).Total := by
  intro a
  obtain ⟨b, hb⟩ := hT a
  exact ⟨b, (D.noWitnessData_graph_iff hOU hT hQ hrad a b).mp hb⟩

theorem noWitnessData_outputUnique
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x) :
    (D.noWitnessData).OutputUnique := by
  intro a b b' hb hb'
  exact hOU a b b' ((D.noWitnessData_graph_iff hOU hT hQ hrad a b).mpr hb)
    ((D.noWitnessData_graph_iff hOU hT hQ hrad a b').mpr hb')

end QuadraticGraphData
end DiophCompression.ResearchUpgrade
