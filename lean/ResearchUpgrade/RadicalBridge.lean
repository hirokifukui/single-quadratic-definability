/-
  RadicalBridge.lean — s48.  Gate22 task **G22-T04**, and the capstone it unlocks.

  G21-T05 proves radical annihilation for INTEGER radical vectors; everything built at s48 (the
  centre, the output representatives, the growth bound) is stated over ℚ with `InRadicalQ`.  This
  file closes that gap by the reviewer's §2 argument — clear denominators, apply the integer
  theorem, divide by `d ≠ 0` — and then assembles the semidefinite branch into a statement with
  NO leftover hypotheses beyond the branch condition itself:

      `0 < m`, `Q` positive semidefinite over ℚ, `Q ≠ 0`, `D.Defines f`, `f` injective  ⇒  `n ≤ m`.

  That is the semidefinite branch of II-D, self-contained.  The centre, the representatives and
  the coercivity-free growth bound are all produced inside the proof.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.OutputGrowth
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RadicalDrift
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

/-- Denominator clearing on any finite index type: a rational vector is `1/d` times an integer
vector, for one positive `d` (the product of the denominators). -/
theorem exists_int_clear {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℚ) :
    ∃ (w : ι → ℤ) (d : ℕ), 0 < d ∧ ∀ k, (w k : ℚ) = (d : ℚ) * e k := by
  classical
  set d : ℕ := ∏ k, (e k).den with hd
  have hdpos : 0 < d := Finset.prod_pos (fun k _ => (e k).den_pos)
  have hint : ∀ k, ∃ z : ℤ, (z : ℚ) = e k * d := by
    intro k
    have hsplit := Finset.mul_prod_erase Finset.univ (fun k => (e k).den) (Finset.mem_univ k)
    refine ⟨(e k).num * ((∏ j ∈ Finset.univ.erase k, (e j).den : ℕ) : ℤ), ?_⟩
    rw [hd, ← hsplit]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose w hw using hint
  exact ⟨w, d, hdpos, fun k => by rw [hw k]; ring⟩

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### Faithfulness of the polar form on integer points -/

theorem zPolarQ_toQ (v w : OutWit m r → ℤ) :
    D.zPolarQ (toQ v) (toQ w) = (D.zPolar v w : ℚ) := by
  simp only [zPolarQ, zPolar, toQ]
  push_cast
  rfl

/-! ### G22-T04 — the ℤ → ℚ radical bridge -/

/-- A cleared rational radical vector is an INTEGER radical vector. -/
theorem inRadical_of_clear {e : OutWit m r → ℚ} (he : D.InRadicalQ e)
    {w : OutWit m r → ℤ} {d : ℕ} (_hd : 0 < d) (hw : ∀ k, (w k : ℚ) = (d : ℚ) * e k) :
    D.InRadical w := by
  intro u
  have h2 : toQ w = (d : ℚ) • e := by funext k; simp [toQ, hw k]
  have h1 : D.zPolarQ (toQ w) (toQ u) = (D.zPolar w u : ℚ) := D.zPolarQ_toQ w u
  rw [h2, D.zPolarQ_smul_left, he (toQ u), mul_zero] at h1
  exact_mod_cast h1.symm

/-- **G22-T04, linear half.**  Under output uniqueness, `ℓ_a` annihilates the RATIONAL radical —
the hypothesis the affine centre family (G22-T06 §3.1) asks for. -/
theorem zLinQ_radicalQ_eq_zero {a : Fin n → ℤ} {z₀ : OutWit m r → ℤ}
    (hm : 0 < m) (hOU : D.OutputUnique) (hz : D.SolZ a z₀)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {e : OutWit m r → ℚ} (he : D.InRadicalQ e) : D.zLinQ a e = 0 := by
  obtain ⟨w, d, hdpos, hw⟩ := exists_int_clear e
  have hrad := D.inRadical_of_clear he hdpos hw
  have h0 := D.zLinEval_radical_eq_zero hm hOU hz hrad hQ
  have h2 : toQ w = (d : ℚ) • e := by funext k; simp [toQ, hw k]
  have h1 : D.zLinQ a (toQ w) = 0 := by rw [D.zLinQ_toQ, h0]; simp
  rw [h2, D.zLinQ_smul] at h1
  have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hdpos.ne'
  exact (mul_eq_zero.mp h1).resolve_left hd0

/-- **G22-T04, output half.**  Under output uniqueness, every output coordinate annihilates the
RATIONAL radical — the hypothesis the polar representatives (G22-T06 §3.2) ask for. -/
theorem outCoordQ_radicalQ_eq_zero {a : Fin n → ℤ} {z₀ : OutWit m r → ℤ}
    (hm : 0 < m) (hOU : D.OutputUnique) (hz : D.SolZ a z₀)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {e : OutWit m r → ℚ} (he : D.InRadicalQ e) (j : Fin m) : e (Sum.inl j) = 0 := by
  obtain ⟨w, d, hdpos, hw⟩ := exists_int_clear e
  have hrad := D.inRadical_of_clear he hdpos hw
  have hlin := D.zLinEval_radical_eq_zero hm hOU hz hrad hQ
  have hout := D.outProj_radical_eq_zero hOU hrad hlin hz
  have hwj : w (Sum.inl j) = 0 := by
    have := congrFun hout j
    simpa [outProj] using this
  have hq := hw (Sum.inl j)
  rw [hwj] at hq
  have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hz0 : (d : ℚ) * e (Sum.inl j) = 0 := by exact_mod_cast hq.symm
  exact (mul_eq_zero.mp hz0).resolve_left hd0

/-- The branch condition may be checked over ℚ: a nonzero rational value of the form produces an
INTEGER vector on which the form is nonzero. -/
theorem exists_zQuad_ne_zero_of_rat {v : OutWit m r → ℚ} (hv : D.zQuadQ v ≠ 0) :
    ∃ w : OutWit m r → ℤ, D.zQuad w ≠ 0 := by
  obtain ⟨w, d, hdpos, hw⟩ := exists_int_clear v
  have h2 : toQ w = (d : ℚ) • v := by funext k; simp [toQ, hw k]
  have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hdpos.ne'
  refine ⟨w, ?_⟩
  intro hzero
  have h1 : D.zQuadQ (toQ w) = (D.zQuad w : ℚ) := D.zQuadQ_toQ w
  rw [h2, D.zQuadQ_smul, hzero] at h1
  simp only [Int.cast_zero] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact hd0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)
  · exact hv h

/-! ### Output uniqueness is free once the graph defines a function -/

theorem outputUnique_of_defines {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    D.OutputUnique := by
  intro a b b' hb hb'
  rw [(hf a b).mp hb, (hf a b').mp hb']

theorem exists_solZ_of_defines {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (a : Fin n → ℤ) : ∃ z : OutWit m r → ℤ, D.SolZ a z := by
  obtain ⟨u, hu⟩ : D.Graph a (f a) := (hf a (f a)).mpr rfl
  exact ⟨Sum.elim (f a) u, hu⟩

/-! ### The semidefinite branch of II-D, self-contained -/

/-- **The semidefinite branch, with no leftover hypotheses.**  A nonzero positive semidefinite
output/witness form forces linear output growth for any function the graph defines.  The centre
family, the output representatives and the growth bound are all constructed inside. -/
theorem linearGrowth_of_semidefinite_defines
    (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f := by
  have hOU := D.outputUnique_of_defines hf
  have hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0 := by
    intro a e he
    obtain ⟨z₀, hz⟩ := D.exists_solZ_of_defines hf a
    exact D.zLinQ_radicalQ_eq_zero hm hOU hz hQ he
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_all_inputs hall
  have hrep : ∀ j : Fin m, ∃ w : OutWit m r → ℚ, ∀ v, D.zPolarQ w v = v (Sum.inl j) := by
    intro j
    refine D.exists_polar_representative ?_
    intro e he
    obtain ⟨z₀, hz⟩ := D.exists_solZ_of_defines hf (fun _ => 0)
    exact D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ he j
  choose ws hws using hrep
  exact D.linearGrowth_of_semidefinite hpos hcen hws hf

/-- **II-D on the semidefinite branch.**  `0 < m`, `Q ≥ 0`, `Q ≠ 0`, the graph defines an injective
function ⇒ `n ≤ m`.  No coercivity, no nondegeneracy, no normal form, no witness bound, and no
hypothesis left over from the construction. -/
theorem dim_le_of_semidefinite_defines
    (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ m :=
  dim_le_of_linearGrowth_injective (D.linearGrowth_of_semidefinite_defines hm hpos hQ hf) hinj

/-! ### Controls -/

/-- POSITIVE control: the bridge is not vacuous — it transports the integer radical statement in
the direction it is needed, and `exists_zQuad_ne_zero_of_rat` shows the branch condition `Q ≠ 0`
may equivalently be checked over ℚ, which is where `hpos` lives. -/
theorem zQuad_ne_zero_iff_rat :
    (∃ w : OutWit m r → ℤ, D.zQuad w ≠ 0) ↔ (∃ v : OutWit m r → ℚ, D.zQuadQ v ≠ 0) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨toQ w, ?_⟩
    rw [D.zQuadQ_toQ w]
    exact_mod_cast hw
  · rintro ⟨v, hv⟩
    exact D.exists_zQuad_ne_zero_of_rat hv

/-- NEGATIVE control: the `Q ≠ 0` hypothesis is load-bearing.  With the form identically zero every
vector is radical, so no output coordinate can have a polar representative, and this route is
unavailable — `Q = 0` is a genuinely separate branch (it is handled by `m_le_one_of_linear` and
`kerLin_subset_kerProj`, G21-T19/T20). -/
theorem not_exists_polar_representative_of_zero_form
    (hzero : ∀ v w : OutWit m r → ℚ, D.zPolarQ v w = 0) (j : Fin m) :
    ¬ ∃ w : OutWit m r → ℚ, ∀ v, D.zPolarQ w v = v (Sum.inl j) := by
  classical
  rintro ⟨w, hw⟩
  have h := hw (fun k => if k = Sum.inl j then (1 : ℚ) else 0)
  rw [hzero] at h
  simp at h

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
