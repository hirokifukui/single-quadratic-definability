/-
  PellBranch.lean — s48.  Gate22 **G22-T15, the assembly**: the quotient-anisotropic branch of
  II-D closes.

  Everything needed is in place: the visible orthogonal plane (G22-T13), the non-square certificate
  (G22-T14), the quadric step and the two-step obstruction (G22-T15 core), the Pell unit congruent
  to 1 (T15, held), and the affine consumer `linearGrowth_of_offCentre_radical`.  What remains is
  the bookkeeping the reviewer's §6.2 prescribes:

    * clear the denominators of `v, w` with ONE modulus `L` (the same `exists_int_clear` move as
      G22-T12), giving integer `V, W` and `A = Q(V) = L²Q(v)`, `C = Q(W) = L²Q(w)`;
    * `d = −A·C > 0` is a non-square by G22-T14, so `exists_pell_unit_congr` gives `(T,S)` with
      `L ∣ (T−1)` and `L ∣ S` — which is exactly what makes the displacement
      `((T−1)/L)·V + (A·S/L)·W` an INTEGER vector;
    * the two shifted points are integer SOLUTIONS at the same input, because the Pell point stays
      on the quadric;
    * output uniqueness then feeds `pell_invisible`, forcing `πv = 0` and `πw = 0` — contradicting
      the visibility G22-T13 guarantees.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.IsotropicBranch
import ResearchUpgrade.PellQuadric
import ResearchUpgrade.PellStep
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- A point at the same quadric distance from the centre as a known solution is itself a
solution. -/
theorem solZ_of_sameNorm {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    {z₀ : OutWit m r → ℤ} (hz₀ : D.SolZ a z₀) {z : OutWit m r → ℤ}
    (hq : D.zQuadQ (toQ z - c) = D.zQuadQ (toQ z₀ - c)) : D.SolZ a z := by
  have hR := D.offCentre_norm hc hz₀
  have hcs := D.completeSquare hc (toQ z)
  rw [hq, hR, sub_self] at hcs
  rw [D.zQuadQ_toQ, D.zLinQ_toQ] at hcs
  have hint : D.zQuad z + D.zLinEval a z + D.aPart a = 0 := by exact_mod_cast hcs
  unfold QuadraticGraphData.SolZ
  rw [D.evalZ]
  exact hint

/-- **G22-T15, the assembly.**  In the quotient-anisotropic branch, an off-centre vector that the
output can see (together with an orthogonal partner of the opposite sign) is impossible. -/
theorem pell_branch_contradiction
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz₀ : D.SolZ a₀ z₀)
    {c : OutWit m r → ℚ} (hc : D.IsCentre a₀ c)
    {v w : OutWit m r → ℚ} (hv : toQ z₀ - c = v)
    (hperp : D.zPolarQ v w = 0) (hsign : D.zQuadQ v * D.zQuadQ w < 0)
    (hvis : (∃ j, v (Sum.inl j) ≠ 0) ∨ ∃ j, w (Sum.inl j) ≠ 0) : False := by
  classical
  have hOU : D.OutputUnique := D.outputUnique_of_defines hf
  have hQv : D.zQuadQ v ≠ 0 := by intro h; rw [h] at hsign; simp at hsign
  -- one modulus clears both vectors
  obtain ⟨WW, L, hLpos, hWW⟩ := exists_int_clear (Sum.elim v w)
  set V : OutWit m r → ℤ := fun k => WW (Sum.inl k) with hVdef
  set W' : OutWit m r → ℤ := fun k => WW (Sum.inr k) with hWdef
  have hVv : ∀ k, ((V k : ℤ) : ℚ) = (L : ℚ) * v k := fun k => hWW (Sum.inl k)
  have hWw : ∀ k, ((W' k : ℤ) : ℚ) = (L : ℚ) * w k := fun k => hWW (Sum.inr k)
  have hLQ : ((L : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hVQ : toQ V = (L : ℚ) • v := by funext k; exact hVv k
  have hWQ : toQ W' = (L : ℚ) • w := by funext k; exact hWw k
  set A : ℤ := D.zQuad V with hAdef
  set C : ℤ := D.zQuad W' with hCdef
  have hAQ : ((A : ℤ) : ℚ) = (L : ℚ) ^ 2 * D.zQuadQ v := by
    rw [hAdef, ← D.zQuadQ_toQ, hVQ, D.zQuadQ_smul]
  have hCQ : ((C : ℤ) : ℚ) = (L : ℚ) ^ 2 * D.zQuadQ w := by
    rw [hCdef, ← D.zQuadQ_toQ, hWQ, D.zQuadQ_smul]
  have hperpVW : D.zPolarQ (toQ V) (toQ W') = 0 := by
    rw [hVQ, hWQ, D.zPolarQ_smul_left, D.zPolarQ_smul_right, hperp]; ring
  have hA0 : A ≠ 0 := by
    intro h
    have : ((A : ℤ) : ℚ) = 0 := by rw [h]; norm_num
    rw [hAQ] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hLQ (by nlinarith [h1])
    · exact hQv h1
  have hdQ : (0 : ℚ) < -(((A : ℤ) : ℚ) * ((C : ℤ) : ℚ)) := by
    rw [hAQ, hCQ]
    have hL2 : (0 : ℚ) < (L : ℚ) ^ 2 := by positivity
    have key : -(((L : ℚ) ^ 2 * D.zQuadQ v) * ((L : ℚ) ^ 2 * D.zQuadQ w))
        = ((L : ℚ) ^ 2 * (L : ℚ) ^ 2) * (-(D.zQuadQ v * D.zQuadQ w)) := by ring
    rw [key]
    exact mul_pos (mul_pos hL2 hL2) (by linarith)
  have hd : 0 < -(A * C) := by exact_mod_cast hdQ
  have hns := D.not_isSquare_pellDiscr hqa hperpVW hA0 hd
  obtain ⟨T, S, hpellZ, hT, hS, hdiv1, hdiv2⟩ := exists_pell_unit_congr hd hns L (by omega)
  obtain ⟨p, hp⟩ := hdiv1
  obtain ⟨q, hq⟩ := hdiv2
  have hpL : (p : ℚ) * (L : ℚ) = (T : ℚ) - 1 := by
    have := congrArg (fun t : ℤ => (t : ℚ)) hp
    push_cast at this
    linarith
  have hqL : (q : ℚ) * (L : ℚ) = (S : ℚ) := by
    have := congrArg (fun t : ℤ => (t : ℚ)) hq
    push_cast at this
    linarith
  have hpellQ : (T : ℚ) ^ 2 - (-(((A : ℤ) : ℚ) * ((C : ℤ) : ℚ))) * (S : ℚ) ^ 2 = 1 := by
    have := congrArg (fun t : ℤ => (t : ℚ)) hpellZ
    push_cast at this
    linarith [this]
  obtain ⟨hpell2, hT2, hS2⟩ := pell_square_rat hpellQ (by exact_mod_cast hT)
    (by exact_mod_cast hS)
  -- the two shifted points
  set z₁ : OutWit m r → ℤ := fun k => z₀ k + p * V k + (A * q) * W' k with hz1def
  set z₂ : OutWit m r → ℤ :=
    fun k => z₀ k + (2 * p * (T + 1)) * V k + (A * (2 * T * q)) * W' k with hz2def
  have hsub1 : toQ z₁ - c = (T : ℚ) • v + (((A : ℤ) : ℚ) * (S : ℚ)) • w := by
    funext k
    have hz0 : ((z₀ k : ℤ) : ℚ) - c k = v k := congrFun hv k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toQ, hz1def]
    push_cast
    rw [hVv k, hWw k]
    linear_combination hz0 + (v k) * hpL + (((A : ℤ) : ℚ) * (w k)) * hqL
  have hsub2 : toQ z₂ - c
      = (2 * (T : ℚ) ^ 2 - 1) • v + (((A : ℤ) : ℚ) * (2 * (T : ℚ) * (S : ℚ))) • w := by
    funext k
    have hz0 : ((z₀ k : ℤ) : ℚ) - c k = v k := congrFun hv k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toQ, hz2def]
    push_cast
    rw [hVv k, hWw k]
    linear_combination hz0 + (v k) * (2 * ((T : ℚ) + 1)) * hpL
      + (((A : ℤ) : ℚ) * (w k) * (2 * (T : ℚ))) * hqL
  have hq1 : D.zQuadQ (toQ z₁ - c) = D.zQuadQ (toQ z₀ - c) := by
    rw [hsub1, hv, D.zQuadQ_pell_point hperp hLQ hAQ hCQ hpellQ]
  have hq2 : D.zQuadQ (toQ z₂ - c) = D.zQuadQ (toQ z₀ - c) := by
    rw [hsub2, hv]
    exact D.zQuadQ_pell_point hperp hLQ hAQ hCQ (by linarith [hpell2])
  have hsol1 : D.SolZ a₀ z₁ := D.solZ_of_sameNorm hc hz₀ hq1
  have hsol2 : D.SolZ a₀ z₂ := D.solZ_of_sameNorm hc hz₀ hq2
  -- output uniqueness
  have hout1 : outProj z₁ = outProj z₀ :=
    hOU a₀ _ _ (D.graph_of_solZ hsol1) (D.graph_of_solZ hz₀)
  have hout2 : outProj z₂ = outProj z₀ :=
    hOU a₀ _ _ (D.graph_of_solZ hsol2) (D.graph_of_solZ hz₀)
  have hrel1 : ∀ j : Fin m,
      (((T : ℚ) - 1) • v + (((A : ℤ) : ℚ) * (S : ℚ)) • w) (Sum.inl j) = 0 := by
    intro j
    have he : z₁ (Sum.inl j) = z₀ (Sum.inl j) := congrFun hout1 j
    have h1 := congrFun hsub1 (Sum.inl j)
    have h0 : ((z₀ (Sum.inl j) : ℤ) : ℚ) - c (Sum.inl j) = v (Sum.inl j) := congrFun hv _
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toQ, he] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [h1, h0]
  have hrel2 : ∀ j : Fin m,
      ((2 * (T : ℚ) ^ 2 - 1 - 1) • v
        + (((A : ℤ) : ℚ) * (2 * (T : ℚ) * (S : ℚ))) • w) (Sum.inl j) = 0 := by
    intro j
    have he : z₂ (Sum.inl j) = z₀ (Sum.inl j) := congrFun hout2 j
    have h1 := congrFun hsub2 (Sum.inl j)
    have h0 : ((z₀ (Sum.inl j) : ℤ) : ℚ) - c (Sum.inl j) = v (Sum.inl j) := congrFun hv _
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toQ, he] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [h1, h0]
  have hA0Q : ((A : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hA0
  obtain ⟨hpv, hpw⟩ :=
    pell_invisible hA0Q (by exact_mod_cast hT) (by exact_mod_cast hS) hrel1 hrel2
  rcases hvis with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact hj (hpv j)
  · exact hj (hpw j)

/-- **The quotient-anisotropic branch of II-D, self-contained.**  Indefinite (`Q` takes both
signs), quotient-anisotropic (`Q(x) = 0 ⇒ x ∈ rad`), `0 < m`, `Q ≠ 0`: then `n ≤ m` for any
injective function the graph defines.  Every off-centre part is forced to be radical by the Pell
argument, so `f = π∘h` is affine and the counting theorem closes it. -/
theorem dim_le_of_quotientAnisotropic_defines
    (hm : 0 < m) (hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0)
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {pp qq : OutWit m r → ℚ} (hpp : 0 < D.zQuadQ pp) (hqq : D.zQuadQ qq < 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ m := by
  classical
  have hOU := D.outputUnique_of_defines hf
  have hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0 := by
    intro a e he
    obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf a
    exact D.zLinQ_radicalQ_eq_zero hm hOU hz hQ he
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_all_inputs hall
  have hcen' : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a) := hcen
  have hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a) := by
    intro a z hz
    by_contra hcon
    have hQv : D.zQuadQ (toQ z - centreFamily c₀ cs a) ≠ 0 :=
      D.zQuadQ_ne_zero_of_nonradical hqa hcon
    obtain ⟨u, hu⟩ := D.exists_opposite_sign hpp hqq hQv
    obtain ⟨w, hperp, hsign, hvis⟩ := D.exists_visible_orthogonal hm hu
    exact D.pell_branch_contradiction hf hqa hz (hcen' a) rfl hperp hsign hvis
  exact dim_le_of_linearGrowth_injective
    (D.linearGrowth_of_offCentre_radical hm hQ hf hrad) hinj

/-! ### Controls -/

/-- POSITIVE control: the branch hypothesis is inhabited — a graph whose polar form vanishes
identically is quotient-anisotropic (vacuously, every vector is radical), so `hqa` is not an
impossible demand. -/
theorem quotientAnisotropic_of_zero_polar (h : ∀ x y : OutWit m r → ℚ, D.zPolarQ x y = 0) :
    ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x :=
  fun x _ y => h x y

/-- NEGATIVE control: quotient-anisotropy is a REAL restriction, not a theorem — the explicit
`(1,1,1)` graph of `isotropic_not_radical_possible` violates it.  So this branch is a genuine case
of the split and the Pell machinery is not decorative. -/
theorem quotientAnisotropic_fails_somewhere :
    ∃ (D' : QuadraticGraphData 1 1 1),
      ¬ (∀ x : OutWit 1 1 → ℚ, D'.zQuadQ x = 0 → D'.InRadicalQ x) := by
  obtain ⟨D', v, hv0, hvr⟩ := isotropic_not_radical_possible
  exact ⟨D', fun hcon => hvr (hcon v hv0)⟩

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
