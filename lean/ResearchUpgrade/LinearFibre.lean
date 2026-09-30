/-
  LinearFibre.lean — Gate-20 Packet 6, tasks T19 and T20 (the `Q = 0` branch).

  When the output/witness quadratic part vanishes the equation is LINEAR in `z`, every vector is in
  the radical, and T05's translation argument applies to every direction at once:

      ℓ_a(e) = 0  ⇒  π(e) = 0            (`kerLin_subset_kerProj`)

  From that, two facts fall out with no further machinery: the coefficient of the first output
  variable is non-zero, and `m ≤ 1`.  This is the reviewer's T19 conclusion `ker ℓ ⊆ ker π, m ≤ 1`
  and the first half of T20 (`ℓ` is a non-zero multiple of `π`).

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.RadicalDrift

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem zLinEval_single (a : Fin n → ℤ) (k : OutWit m r) (v : ℤ) :
    D.zLinEval a (Pi.single k v) = D.zLin a k * v := by
  simp only [zLinEval]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb.symm]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **T19.**  With a vanishing quadratic part, output uniqueness forces the kernel of the linear
form into the kernel of the projection.  Every vector is radical, so this is T05's translation
argument applied in every direction at once. -/
theorem kerLin_subset_kerProj (hpol : ∀ v w : OutWit m r → ℤ, D.zPolar v w = 0)
    (hOU : D.OutputUnique) {a : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a z₀)
    {e : OutWit m r → ℤ} (he : D.zLinEval a e = 0) : outProj e = 0 :=
  D.outProj_radical_eq_zero hOU (fun w => hpol e w) he hz

/-- **T19 / T20.**  In the linear branch the first output coefficient is non-zero and `m ≤ 1`. -/
theorem m_le_one_of_linear (hpol : ∀ v w : OutWit m r → ℤ, D.zPolar v w = 0)
    (hOU : D.OutputUnique) {a : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a z₀)
    (hm : 0 < m) :
    D.zLin a (Sum.inl ⟨0, hm⟩) ≠ 0 ∧ m ≤ 1 := by
  have hker : ∀ e : OutWit m r → ℤ, D.zLinEval a e = 0 → outProj e = 0 :=
    fun e he => D.kerLin_subset_kerProj hpol hOU hz he
  have hc0 : D.zLin a (Sum.inl ⟨0, hm⟩) ≠ 0 := by
    intro h0
    have hlin : D.zLinEval a (Pi.single (Sum.inl (⟨0, hm⟩ : Fin m)) (1 : ℤ)) = 0 := by
      rw [D.zLinEval_single, h0, zero_mul]
    have hp := hker _ hlin
    have := congrFun hp ⟨0, hm⟩
    simp [outProj, Pi.single_apply] at this
  refine ⟨hc0, ?_⟩
  by_contra hm2
  push_neg at hm2
  have h1 : (1 : ℕ) < m := hm2
  set i0 : Fin m := ⟨0, hm⟩ with hi0
  set i1 : Fin m := ⟨1, h1⟩ with hi1
  set c0 : ℤ := D.zLin a (Sum.inl i0) with hc0def
  set c1 : ℤ := D.zLin a (Sum.inl i1) with hc1def
  set e : OutWit m r → ℤ :=
    c1 • Pi.single (Sum.inl i0) (1 : ℤ) + (-c0) • Pi.single (Sum.inl i1) (1 : ℤ) with hedef
  have hlin : D.zLinEval a e = 0 := by
    rw [hedef, D.zLinEval_add, D.zLinEval_smul, D.zLinEval_smul,
      D.zLinEval_single, D.zLinEval_single]
    ring
  have hp := hker e hlin
  have hval := congrFun hp i1
  have hne : i0 ≠ i1 := by
    simp [hi0, hi1]
  simp [outProj, hedef, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hne, hne.symm] at hval
  exact hc0 (by linarith [hval])

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
