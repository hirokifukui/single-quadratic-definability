/-
  WitnessInvariance.lean — s52.  R41-B1: the evaluation of `P` does not see the witness block
  once every vector with vanishing output coordinates is radical.

  Stated and proved in the ORIGINAL integer coordinates: the conclusion is an equality of
  evaluations at arbitrary integer points `(a, b, u)` and `(a, b, 0)`, not a statement about
  solutions, and `0` is the zero of `Fin r → ℤ`, not a representative of a rational quotient.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.RadicalBridge
import ResearchUpgrade.RationalCentre
import ResearchUpgrade.PolarAnnihilator

namespace DiophCompression.ResearchUpgrade
namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- A vector that is radical has zero form value: `2Q(v) = B(v,v) = 0`. -/
theorem zQuadQ_eq_zero_of_inRadicalQ {v : OutWit m r → ℚ} (hv : D.InRadicalQ v) :
    D.zQuadQ v = 0 := by
  have h2 : D.zQuadQ (v + v) = D.zQuadQ v + D.zPolarQ v v + D.zQuadQ v := D.zQuadQ_add v v
  have hsm : (v + v) = (2 : ℚ) • v := by funext k; simp; ring
  have h4 : D.zQuadQ (v + v) = 4 * D.zQuadQ v := by
    rw [hsm, D.zQuadQ_smul]; norm_num
  rw [h4, hv v] at h2
  linarith

/-- **R41-B1 — statement frozen s52.** -/
theorem eval_witness_invariant
    (hm : 0 < m) (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit m r → ℚ, (∀ j : Fin m, x (Sum.inl j) = 0) → D.InRadicalQ x)
    (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) :
    D.P.eval (pt a b u) = D.P.eval (pt a b (0 : Fin r → ℤ)) := by
  classical
  set x : OutWit m r → ℤ := Sum.elim (fun _ => (0 : ℤ)) u with hxdef
  set y : OutWit m r → ℤ := Sum.elim b (0 : Fin r → ℤ) with hydef
  have hxrad : D.InRadicalQ (toQ x) := by
    refine hrad _ ?_
    intro j; simp [toQ, hxdef]
  -- the witness-carrying vector splits off
  have hdec : (Sum.elim b u : OutWit m r → ℤ) = y + x := by
    funext k; cases k <;> simp [hxdef, hydef]
  -- a solution at this very input, from totality
  obtain ⟨b₀, u₀, hsol⟩ : ∃ b₀ u₀, D.Sol a b₀ u₀ := by
    obtain ⟨b₀, hb₀⟩ := hT a; obtain ⟨u₀, hu₀⟩ := hb₀; exact ⟨b₀, u₀, hu₀⟩
  have hz : D.SolZ a (Sum.elim b₀ u₀) := hsol
  -- quadratic part
  have hquadQ : D.zQuadQ (toQ (y + x)) = D.zQuadQ (toQ y) := by
    have hadd : toQ (y + x) = toQ y + toQ x := by funext k; simp [toQ]
    rw [hadd, D.zQuadQ_add, D.zQuadQ_eq_zero_of_inRadicalQ hxrad,
        D.zPolarQ_symm, hxrad (toQ y)]
    ring
  have hquad : D.zQuad (y + x) = D.zQuad y := by
    have := hquadQ
    rw [D.zQuadQ_toQ, D.zQuadQ_toQ] at this
    exact_mod_cast this
  -- linear part
  have hlinQ : D.zLinQ a (toQ (y + x)) = D.zLinQ a (toQ y) := by
    have hadd : toQ (y + x) = toQ y + toQ x := by funext k; simp [toQ]
    rw [hadd, D.zLinQ_add, D.zLinQ_radicalQ_eq_zero hm hOU hz hQ hxrad]
    ring
  have hlin : D.zLinEval a (y + x) = D.zLinEval a y := by
    have := hlinQ
    rw [D.zLinQ_toQ, D.zLinQ_toQ] at this
    exact_mod_cast this
  -- assemble
  rw [D.eval_split a b u, D.eval_split a b (0 : Fin r → ℤ), hdec, ← hydef, hquad]
  have : (∑ k, D.zLin a k * (y + x) k) = ∑ k, D.zLin a k * y k := by
    simpa [zLinEval] using hlin
  rw [this]

/-- The `m = 1` instance that B2's compiler will consume. -/
theorem eval_witness_invariant_one {n r : ℕ} (D : QuadraticGraphData n 1 r)
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit 1 r → ℤ, D.zQuad v ≠ 0)
    (hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x)
    (a : Fin n → ℤ) (b : Fin 1 → ℤ) (u : Fin r → ℤ) :
    D.P.eval (pt a b u) = D.P.eval (pt a b (0 : Fin r → ℤ)) :=
  D.eval_witness_invariant Nat.one_pos hOU hT hQ hrad a b u

end QuadraticGraphData
end DiophCompression.ResearchUpgrade
