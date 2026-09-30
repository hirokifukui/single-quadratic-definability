/-
  R42Completion.lean — s54.  The three GATE24 items that the first s54 pass left partial.

  * R42-A3 item 4: `fullVectorCosetNF_of_polarRank_eq_one` — the rank-one capstone
    `fullVectorCosetNF_of_polarRankOne` with its base solution (from totality) and its
    codimension-one direction (a vector spanning the one-dimensional polar image) built
    internally.  Hypotheses: `Q ≠ 0` (already a hypothesis of the capstone), `polarRank = 1`,
    `Defines f`.  No new mathematical hypothesis.
  * R42-D1, solution side: `definite_binary_compiler_solutions` — the `(n, 1, 1)` compiler together
    with an iff: an integer vector is a solution at `a` exactly when its offset from the centre is
    `(x − βy, y)` with `R(a) = α(x² + Δy²)`.  This exports the exact rational norm representation of
    a given solution and the inverse transform back to it.
  * R42-D3, `m = 0`: `weakVectorCosetNF_of_no_outputs`, and `lowRankSemidefiniteWeakNF_allM_holds`,
    the low-rank statement without the hypothesis `0 < m`.

  Claim tags: [P] (std-3).
-/
/-
  S54_completion_freeze_draft.lean — statements for the three GATE24 items left partial
  (R42-A3 item 4, R42-D1 solution side, R42-D3 m = 0), work file (proofs).  s54 ckpt 5.
-/
import ResearchUpgrade.DefiniteBinary
import ResearchUpgrade.RankOneConfluence

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

/-- **R42-A3 item 4.**  The rank-one capstone with its auxiliary hypotheses (a base solution and a
codimension-one direction) built internally from `Defines f` and `polarRank = 1`. -/
theorem fullVectorCosetNF_of_polarRank_eq_one {n m r : ℕ} (D : QuadraticGraphData n m r)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) (hrank : D.polarRank = 1)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : FullVectorCosetNF f := by
  classical
  have hT : D.Total := fun a => ⟨f a, (hf a (f a)).mpr rfl⟩
  have hOU := D.outputUnique_of_defines hf
  obtain ⟨u, hu⟩ := (hf 0 (f 0)).mpr rfl
  have hz : D.SolZ 0 (Sum.elim (f 0) u) := hu
  have hne : ∃ w₀ : OutWit m r → ℚ, D.polarMapQ w₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : D.polarMapQ = 0 := LinearMap.ext h
    have : D.polarRank = 0 := by
      unfold polarRank
      rw [LinearMap.range_eq_bot.mpr h0, finrank_bot]
    omega
  obtain ⟨w₀, hw₀⟩ := hne
  have hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀) := by
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
  exact D.fullVectorCosetNF_of_polarRankOne hOU hT hQ hz hcodim hf

/-- **R42-D1 (solution side).**  The compiler of `definite_binary_compiler`, together with: an
integer vector is a solution at `a` exactly when its offset from the centre is `(x − βy, y)` for a
rational pair with `R(a) = α(x² + Δy²)` — so every integer solution has an exact rational norm
representation, and the inverse transform returns to that solution. -/
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
          (z (Sum.inr 0) : ℚ) = (c0 (Sum.inr 0) + ∑ i, L (Sum.inr 0) i * (a i : ℚ)) + y := by
  obtain ⟨α, β, Δ, c0, L, Rq, hα, hΔ, hC, hR, hdiag⟩ := D.definite_binary_compiler hpos
  refine ⟨α, β, Δ, c0, L, Rq, hα, hΔ, hC, hR, hdiag, fun a z => ⟨fun hz => ?_, ?_⟩⟩
  · have hn := D.offCentre_norm (hC a) hz
    rw [hR a, hdiag] at hn
    refine ⟨(toQ z - fun k => c0 k + ∑ i, L k i * (a i : ℚ)) (Sum.inl 0)
        + β * (toQ z - fun k => c0 k + ∑ i, L k i * (a i : ℚ)) (Sum.inr 0),
      (toQ z - fun k => c0 k + ∑ i, L k i * (a i : ℚ)) (Sum.inr 0), hn.symm, ?_, ?_⟩
    · simp only [Pi.sub_apply, toQ]; ring
    · simp only [Pi.sub_apply, toQ]; ring
  · rintro ⟨x, y, hxy, h1, h2⟩
    apply QuadraticGraphData.solZ_of_norm (hC a)
    rw [hR a, hdiag, hxy]
    simp only [Pi.sub_apply, toQ]
    rw [h1, h2]
    ring

end QuadraticGraphData

/-- **R42-D3, m = 0.**  With no outputs the weak vector coset normal form holds vacuously. -/
theorem weakVectorCosetNF_of_no_outputs {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) :
    WeakVectorCosetNF f :=
  weakVectorCosetNF_of_fullVectorCosetNF (fullVectorCosetNF_of_m_zero f)

/-- The low-rank statement without the hypothesis `0 < m`. -/
def LowRankSemidefiniteWeakNF_allM : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
    ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
    D.polarRank ≤ 2 → D.Defines f → WeakVectorCosetNF f

/-- **R42-D3 (every m).** -/
theorem lowRankSemidefiniteWeakNF_allM_holds : LowRankSemidefiniteWeakNF_allM := by
  intro n m r D f hQ hsemi hrank hf
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact weakVectorCosetNF_of_no_outputs f
  · exact lowRankSemidefiniteWeakNF_holds n m r D f hm hQ hsemi hrank hf

end DiophCompression.ResearchUpgrade
