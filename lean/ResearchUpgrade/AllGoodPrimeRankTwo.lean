/-
  AllGoodPrimeRankTwo.lean — Gate-18 research program, Packet A1 (A1-1, A1-2, A1-3).
  The baseline `moving_modulus_prime_step_general` (MovingModulusGeneral.lean line 150, sealed,
  untouched) CHOOSES a prime p ≡ 1 mod M via Nat.exists_prime_gt_modEq_one and then derives
  everything from `M ∣ p − 1` and `M < p`. Here the prime is an EXTERNAL argument with exactly
  those two hypotheses; the proof after the choice is transplanted line by line (the reviewer's
  "reconstruct, do not derive ∀ from ∃"). The modulus M = 2|D|·b·t₀ does not depend on p.
  Output: c(p) = c₀ + t₀·((p−1)/b) with b·c(p) + μ = t₀·p, a witness u_p with u_p ≡ u₀ (mod t₀)
  and b•u_p ≡ x (mod p) for a mod-p root x of the moving-remainder polynomial, and
  (b·c(p) + μ) ∣ fqM(c(p), u_p).  Private helpers of the baseline file are re-declared verbatim.
-/
import DiophCompression.SemanticQuadraticSingular.MovingModulusGeneral

namespace DiophCompression.ResearchUpgrade

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular
variable {k : ℕ}

/-- The moving modulus `M = 2|D|·b·t₀` (as a natural number), independent of `p`. -/
def movingModulusNat (D b t₀ : ℤ) : ℕ := 2 * D.natAbs * b.natAbs * t₀.natAbs

/-! ### Helpers re-declared verbatim from the baseline (there `private`) -/

private theorem ru_dvd_dotProduct_sub (d : ℤ) (a x y : Fin k → ℤ)
    (h : ∀ i, d ∣ x i - y i) : d ∣ a ⬝ᵥ x - a ⬝ᵥ y := by
  have he : a ⬝ᵥ x - a ⬝ᵥ y = ∑ i, a i * (x i - y i) := by
    rw [dotProduct, dotProduct, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [he]
  exact Finset.dvd_sum (fun i _ => (h i).mul_left _)

private theorem ru_dvd_witnessQuad_sub (d : ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (x y : Fin k → ℤ)
    (h : ∀ i, d ∣ x i - y i) : d ∣ witnessQuad C x - witnessQuad C y := by
  have he : witnessQuad C x - witnessQuad C y
      = ∑ i, ∑ j, C i j * (x i * (x j - y j) + (x i - y i) * y j) := by
    simp only [witnessQuad, dotProduct, mulVec]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [he]
  refine Finset.dvd_sum (fun i _ => Finset.dvd_sum (fun j _ => ?_))
  exact Dvd.dvd.mul_left (dvd_add ((h j).mul_left _) ((h i).mul_right _)) _

private theorem ru_fqM_dvd_sub (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (l : ℤ) (m : Fin k → ℤ) (q : ℤ) (c c₀ : ℤ) (u u₀ : Fin k → ℤ) (d : ℤ)
    (hc : d ∣ c - c₀) (hu : ∀ i, d ∣ u i - u₀ i) :
    d ∣ fqM A B C l m q c u - fqM A B C l m q c₀ u₀ := by
  have he : fqM A B C l m q c u - fqM A B C l m q c₀ u₀
      = A * ((c - c₀) * (c + c₀)) + ((c - c₀) * (B ⬝ᵥ u₀) + c * (B ⬝ᵥ u - B ⬝ᵥ u₀))
        + (witnessQuad C u - witnessQuad C u₀) + l * (c - c₀) + (m ⬝ᵥ u - m ⬝ᵥ u₀) := by
    simp only [fqM]; ring
  rw [he]
  have hBd : d ∣ B ⬝ᵥ u - B ⬝ᵥ u₀ := ru_dvd_dotProduct_sub d B u u₀ hu
  have hmd : d ∣ m ⬝ᵥ u - m ⬝ᵥ u₀ := ru_dvd_dotProduct_sub d m u u₀ hu
  have hWd : d ∣ witnessQuad C u - witnessQuad C u₀ := ru_dvd_witnessQuad_sub d C u u₀ hu
  refine dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) hWd) ?_) hmd
  · exact Dvd.dvd.mul_left (hc.mul_right _) _
  · exact dvd_add (hc.mul_right _) (hBd.mul_left _)
  · exact hc.mul_left _

private theorem ru_mrpG_dvd_sub (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (x x₀ : Fin k → ℤ) (d : ℤ)
    (hx : ∀ i, d ∣ x i - x₀ i) :
    d ∣ movingRemainderPolyG A B C b l m μ q x - movingRemainderPolyG A B C b l m μ q x₀ := by
  have he : movingRemainderPolyG A B C b l m μ q x - movingRemainderPolyG A B C b l m μ q x₀
      = (witnessQuad C x - witnessQuad C x₀)
        + ((b • m - μ • B) ⬝ᵥ x - (b • m - μ • B) ⬝ᵥ x₀) := by
    simp only [movingRemainderPolyG]; ring
  rw [he]
  exact dvd_add (ru_dvd_witnessQuad_sub d C x x₀ hx)
    (ru_dvd_dotProduct_sub d (b • m - μ • B) x x₀ hx)

private theorem ru_prime_not_dvd_of_dvd_pred (p : ℕ) (hp : p.Prime) (x : ℤ)
    (hx : x ∣ (p : ℤ) - 1) : ¬ (p : ℤ) ∣ x := by
  intro hc
  have := dvd_trans hc hx
  have h1 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
  have := Int.eq_one_of_dvd_one (by positivity) h1
  have := hp.one_lt; omega

/-! ### A1-1: arithmetic facts about any good prime -/

/-- A1-1. For any prime `p ≡ 1 (mod M)` with `M = 2|D|·b·t₀ > 0`:
`b ∣ p−1`, `t₀ ∣ p−1`, `p ∤ b`, `p ∤ t₀`, `p ≠ 2`, `p ∤ D`. -/
theorem goodPrime_facts (D b t₀ : ℤ) (hD : D ≠ 0) (hb : 0 < b) (ht₀ : 0 < t₀)
    (p : ℕ) (hp : p.Prime) (hpmod : p ≡ 1 [MOD movingModulusNat D b t₀]) :
    b ∣ (p : ℤ) - 1 ∧ t₀ ∣ (p : ℤ) - 1 ∧ ¬ (p : ℤ) ∣ b ∧ ¬ (p : ℤ) ∣ t₀ ∧ p ≠ 2 ∧
      ¬ (p : ℤ) ∣ D := by
  have hMcast : (movingModulusNat D b t₀ : ℤ) = 2 * |D| * b * t₀ := by
    unfold movingModulusNat; push_cast
    rw [abs_of_pos hb, abs_of_pos ht₀]
  have hMdvd : (movingModulusNat D b t₀ : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by have := hp.one_lt; omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by have := hp.one_lt; omega), Nat.cast_one] at h'
  have hbdvd : b ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D| * t₀, by ring⟩
  have ht₀dvd : t₀ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D| * b, by ring⟩
  have h2dvd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨|D| * b * t₀, by ring⟩
  have hDdvd : D ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs D).trans ⟨2 * b * t₀, by ring⟩
  have hp2' : ¬ (p : ℤ) ∣ 2 := ru_prime_not_dvd_of_dvd_pred p hp 2 h2dvd
  refine ⟨hbdvd, ht₀dvd, ru_prime_not_dvd_of_dvd_pred p hp b hbdvd,
    ru_prime_not_dvd_of_dvd_pred p hp t₀ ht₀dvd, ?_, ru_prime_not_dvd_of_dvd_pred p hp D hDdvd⟩
  intro h; apply hp2'; rw [h]; norm_num

/-! ### A1-2 / A1-3: the prime step for EVERY good prime, with its data -/

/-- A1-2/A1-3. Same base point `(c₀, u₀)`, same modulus `M = 2|D|·b·t₀` (`D = det(C + Cᵀ)`,
`t₀ = b c₀ + μ`), ANY prime `p > M`, `p ≡ 1 (mod M)`: with `c(p) = c₀ + t₀·((p−1)/b)`,
`b·c(p) + μ = t₀·p`, and there are a witness `u` and a mod-`p` root `x` with
`u ≡ u₀ (mod t₀)`, `b•u ≡ x (mod p)`, `p ∣ mrpG(x)`, and `(b·c(p) + μ) ∣ fqM(c(p), u)`. -/
theorem moving_modulus_prime_step_allGoodPrime (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ)
    (u₀ : Fin k → ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀)
    (p : ℕ) (hp : p.Prime)
    (hpM : movingModulusNat (C + Cᵀ).det b (b * c₀ + μ) < p)
    (hpmod : p ≡ 1 [MOD movingModulusNat (C + Cᵀ).det b (b * c₀ + μ)]) :
    c₀ < c₀ + (b * c₀ + μ) * (((p : ℤ) - 1) / b) ∧
    b * (c₀ + (b * c₀ + μ) * (((p : ℤ) - 1) / b)) + μ = (b * c₀ + μ) * p ∧
    ∃ (u x : Fin k → ℤ),
      (∀ i, (b * c₀ + μ) ∣ u i - u₀ i) ∧
      (∀ i, (p : ℤ) ∣ (b • u) i - x i) ∧
      (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q x ∧
      (b * (c₀ + (b * c₀ + μ) * (((p : ℤ) - 1) / b)) + μ) ∣
        fqM A B C l m q (c₀ + (b * c₀ + μ) * (((p : ℤ) - 1) / b)) u := by
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℤ, t₀ = b * c₀ + μ := ⟨_, rfl⟩
  rw [← ht₀def] at ht₀ hdiv hpM hpmod ⊢
  obtain ⟨D', hD'⟩ : ∃ D' : ℤ, D' = (C + Cᵀ).det := ⟨_, rfl⟩
  have hD'ne : D' ≠ 0 := by rw [hD']; exact hN
  rw [← hD'] at hpM hpmod
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, Mn = movingModulusNat D' b t₀ := ⟨_, rfl⟩
  rw [← hMn] at hpM hpmod
  have hMpos : 0 < Mn := by
    rw [hMn]; unfold movingModulusNat
    have h1 : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'ne
    have h2 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
    have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    positivity
  haveI := Fact.mk hp
  obtain ⟨hbdvd, ht₀dvd, hpb, hpt₀, hp2, hpD'⟩ :=
    goodPrime_facts D' b t₀ hD'ne hb ht₀ p hp (hMn ▸ hpmod)
  have hpD : ¬ (p : ℤ) ∣ (C + Cᵀ).det := by rw [← hD']; exact hpD'
  obtain ⟨j, hj⟩ := hbdvd
  have hjdef : ((p : ℤ) - 1) / b = j := by
    rw [hj]; exact Int.mul_ediv_cancel_left j hb.ne'
  rw [hjdef]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = c₀ + t₀ * j := ⟨_, rfl⟩
  rw [← hc]
  have hj1 : 1 ≤ j := by
    have hpB : b ≤ (p : ℤ) - 1 := by
      have : b.natAbs ≤ Mn := Nat.le_of_dvd hMpos
        ⟨2 * D'.natAbs * t₀.natAbs, by rw [hMn]; unfold movingModulusNat; ring⟩
      have : (b.natAbs : ℤ) = b := by rw [Int.natCast_natAbs, abs_of_pos hb]
      omega
    by_contra hcon; push Not at hcon
    have : b * j ≤ b * 0 := mul_le_mul_of_nonneg_left (by omega) hb.le
    linarith
  have hct : b * c + μ = t₀ * p := by rw [hc]; linear_combination (-t₀) * hj - ht₀def
  have hc₀c : c₀ < c := by rw [hc]; nlinarith
  obtain ⟨x, hxy⟩ := moving_remainder_root_mod_prime_general hk p hp hp2 A B C b l m μ q hpD
  have hcopbp : IsCoprime b (p : ℤ) := by
    have hnat : b.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpb
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos hb] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos hb] at this
  obtain ⟨α, β, hαβ⟩ := hcopbp
  have hcop : IsCoprime t₀ (p : ℤ) := by
    have hnat : t₀.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpt₀
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
  obtain ⟨a', b', hab⟩ := hcop
  set u : Fin k → ℤ := fun i => (α * x i) * (a' * t₀) + u₀ i * (b' * (p : ℤ)) with hudef
  have hui : ∀ i, u i = (α * x i) * (a' * t₀) + u₀ i * (b' * (p : ℤ)) := fun i => rfl
  have hu₀ : ∀ i, t₀ ∣ u i - u₀ i := fun i =>
    ⟨a' * (α * x i - u₀ i), by rw [hui]; linear_combination (u₀ i) * hab⟩
  have hup' : ∀ i, (p : ℤ) ∣ u i - α * x i := fun i =>
    ⟨b' * (u₀ i - α * x i), by rw [hui]; linear_combination (α * x i) * hab⟩
  have hbup : ∀ i, (p : ℤ) ∣ b * (α * x i) - x i := fun i =>
    ⟨-(β * x i), by linear_combination (x i) * hαβ⟩
  have hx' : ∀ i, (p : ℤ) ∣ (b • u) i - x i := by
    intro i
    have e : (b • u) i - x i = b * (u i - α * x i) + (b * (α * x i) - x i) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact dvd_add ((hup' i).mul_left b) (hbup i)
  refine ⟨hc₀c, hct, u, x, hu₀, hx', hxy, ?_⟩
  rw [hct]
  apply IsCoprime.mul_dvd ⟨a', b', hab⟩
  · have hcc : t₀ ∣ c - c₀ := ⟨j, by rw [hc]; ring⟩
    have := dvd_add hdiv (ru_fqM_dvd_sub A B C l m q c c₀ u u₀ t₀ hcc hu₀)
    simpa using this
  · have hpR : (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q (b • u) := by
      have := dvd_add hxy (ru_mrpG_dvd_sub A B C b l m μ q (b • u) x p hx')
      simpa using this
    have hpt : (p : ℤ) ∣ b * c + μ := ⟨t₀, by rw [hct]; ring⟩
    have hpb2 : (p : ℤ) ∣ b ^ 2 * fqM A B C l m q c u := by
      rw [moving_remainder_identity_general A B C b l m μ q c u]
      exact dvd_add hpR (hpt.mul_right _)
    have hcopb : IsCoprime (p : ℤ) b := ⟨β, α, by linear_combination hαβ⟩
    exact (hcopb.pow_right).dvd_of_dvd_mul_left hpb2

/-- Sanity: the baseline existence statement is recovered from the all-good-prime version by
choosing one prime (Dirichlet-type existence `Nat.exists_prime_gt_modEq_one`). -/
theorem baseline_step_of_allGoodPrime (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ)
    (u₀ : Fin k → ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀) :
    ∃ (c : ℤ) (u : Fin k → ℤ), c₀ < c ∧ (b * c + μ) ∣ fqM A B C l m q c u := by
  have hM0 : movingModulusNat (C + Cᵀ).det b (b * c₀ + μ) ≠ 0 := by
    unfold movingModulusNat
    have h1 : (C + Cᵀ).det.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN
    have h2 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
    have h4 : (b * c₀ + μ).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    positivity
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one _ hM0
  obtain ⟨hlt, -, u, -, -, -, -, hdvd⟩ :=
    moving_modulus_prime_step_allGoodPrime hk A B C b l m μ q c₀ u₀ hb hN ht₀ hdiv p hp hpM hpmod
  exact ⟨_, u, hlt, hdvd⟩

end DiophCompression.ResearchUpgrade
