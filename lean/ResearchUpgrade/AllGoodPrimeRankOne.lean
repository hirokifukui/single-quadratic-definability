/-
  AllGoodPrimeRankOne.lean — Gate-18 research program, Packet A2 (A2-1, A2-2, A2-3).
  Baseline `rank_one_coupled_prime_step_data` (RankOneCoupledData.lean line 19, sealed, untouched)
  chooses p ≡ 1 mod M with M = 8·max(1,|D'|)·B₂·|2k|·t₀ and returns the data. Here p is EXTERNAL
  (p prime, M < p, p ≡ 1 mod M) with the same base point and the same M; the proof after the
  choice is the sealed script transplanted. A2-2: the D' = 0 case is isolated in
  `disc_square_of_dPrime_zero` (no reciprocity used there); A2-1: D' ≠ 0 uses the baseline
  reciprocity lemma `square_mod_prime_of_one_mod_eight_abs` only. No quadratic-residue hypothesis is
  added. Output c(p) = c₀ + t₀·((p−1)/B₂) with B₂·c(p) + m₂ = t₀·p, u ≡ u₀ (mod t₀), u ≡ u_p (mod p)
  with u_p a mod-p root, and (B₂·c(p) + m₂) ∣ qOne(c(p), u).
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankOneCoupledData

namespace DiophCompression.ResearchUpgrade

open DiophCompression.SemanticQuadratic DiophCompression.SemanticQuadraticTwoWitness

/-- The rank-one modulus `M = 8·max(1,|D'|)·B₂·|2k|·t₀`, independent of `p`. -/
def rankOneModulusNat (D' B₂ k t₀ : ℤ) : ℕ :=
  8 * (max 1 |D'|).natAbs * B₂.natAbs * (2 * k).natAbs * t₀.natAbs

/-- A2-2 (the double-root case): when `D' = 0`, `B₂² · disc(c)` is divisible by `B₂c + m₂`
(by `dPrime_identity`), so for `p ∣ B₂c + m₂`, `p ∤ B₂` the discriminant is `0` mod `p` — a square,
with no reciprocity input. -/
theorem disc_square_of_dPrime_zero (A B₁ B₂ k l m₁ m₂ q c : ℤ) (p : ℕ) (hp : p.Prime)
    (hD0 : dPrime A B₁ B₂ k l m₁ m₂ q = 0) (hpt : (p : ℤ) ∣ B₂ * c + m₂) (hpB₂ : ¬ (p : ℤ) ∣ B₂) :
    (p : ℤ) ∣ (B₁ * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q) := by
  haveI := Fact.mk hp
  have hid := dPrime_identity A B₁ B₂ k l m₁ m₂ q c
  rw [hD0, sub_zero] at hid
  have hdvd : (p : ℤ) ∣ B₂ ^ 2 * ((B₁ * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)) := by
    rw [hid]; exact hpt.mul_right _
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_or_dvd hdvd with h | h
  · exact absurd (hpZ.dvd_of_dvd_pow h) hpB₂
  · exact h

/-- A2-1 / A2-3. Rank-one coupled prime step for EVERY good prime, with data. -/
theorem rank_one_coupled_prime_step_allGoodPrime (A B₁ B₂ k l m₁ m₂ q c₀ u₀ : ℤ) (hB₂ : 0 < B₂)
    (hk : k ≠ 0) (ht₀ : 0 < B₂ * c₀ + m₂) (hdiv : (B₂ * c₀ + m₂) ∣ qOne A B₁ k l m₁ q c₀ u₀)
    (p : ℕ) (hp : p.Prime)
    (hpM : rankOneModulusNat (dPrime A B₁ B₂ k l m₁ m₂ q) B₂ k (B₂ * c₀ + m₂) < p)
    (hpmod : p ≡ 1 [MOD rankOneModulusNat (dPrime A B₁ B₂ k l m₁ m₂ q) B₂ k (B₂ * c₀ + m₂)]) :
    c₀ < c₀ + (B₂ * c₀ + m₂) * (((p : ℤ) - 1) / B₂) ∧
    B₂ * (c₀ + (B₂ * c₀ + m₂) * (((p : ℤ) - 1) / B₂)) + m₂ = (B₂ * c₀ + m₂) * p ∧
    ∃ u up : ℤ,
      (B₂ * c₀ + m₂) ∣ u - u₀ ∧ (p : ℤ) ∣ u - up ∧
      (p : ℤ) ∣ qOne A B₁ k l m₁ q (c₀ + (B₂ * c₀ + m₂) * (((p : ℤ) - 1) / B₂)) up ∧
      (B₂ * (c₀ + (B₂ * c₀ + m₂) * (((p : ℤ) - 1) / B₂)) + m₂) ∣
        qOne A B₁ k l m₁ q (c₀ + (B₂ * c₀ + m₂) * (((p : ℤ) - 1) / B₂)) u := by
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℤ, t₀ = B₂ * c₀ + m₂ := ⟨_, rfl⟩
  rw [← ht₀def] at ht₀ hdiv hpM hpmod ⊢
  obtain ⟨D', hD'⟩ : ∃ D' : ℤ, D' = dPrime A B₁ B₂ k l m₁ m₂ q := ⟨_, rfl⟩
  rw [← hD'] at hpM hpmod
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, Mn = 8 * (max 1 |D'|).natAbs * B₂.natAbs * (2 * k).natAbs * t₀.natAbs := ⟨_, rfl⟩
  have hMn' : rankOneModulusNat D' B₂ k t₀ = Mn := by rw [hMn]; rfl
  rw [hMn'] at hpM hpmod
  have h1 : (max 1 |D'|).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |D'|; omega)
  have h2 : B₂.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hB₂.ne'
  have h3 : (2 * k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero two_ne_zero hk)
  have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
  have hM0 : Mn ≠ 0 := by
    rw [hMn]; positivity
  have hMpos : 0 < Mn := Nat.pos_of_ne_zero hM0
  haveI := Fact.mk hp
  have hMdvd : (Mn : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by have := hp.one_lt; omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by have := hp.one_lt; omega), Nat.cast_one] at h'
  have hB₂dvd : B₂ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMn]; push_cast
    rw [abs_of_pos hB₂]
    exact ⟨8 * (abs (max 1 (abs D'))) * |2 * k| * |t₀|, by ring⟩
  have h2kdvd : 2 * k ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMn]; push_cast
    exact (self_dvd_abs (2 * k)).trans ⟨8 * (abs (max 1 (abs D'))) * |B₂| * |t₀|, by ring⟩
  have hD'dvd : D' ≠ 0 → (8 * D'.natAbs : ℕ) ∣ Mn := by
    intro hne
    rw [hMn, show (max 1 |D'|).natAbs = D'.natAbs by
      rw [max_eq_right (Int.one_le_abs hne), Int.natAbs_abs]]
    exact ⟨B₂.natAbs * (2 * k).natAbs * t₀.natAbs, by ring⟩
  have hp2k : ¬ (p : ℤ) ∣ 2 * k := by
    intro hc
    have := dvd_trans hc h2kdvd
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have := hp.one_lt; omega
  have hpB₂ : ¬ (p : ℤ) ∣ B₂ := by
    intro hc
    have := dvd_trans hc hB₂dvd
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have := hp.one_lt; omega
  obtain ⟨j, hj⟩ := hB₂dvd
  have hjdef : ((p : ℤ) - 1) / B₂ = j := by
    rw [hj]; exact Int.mul_ediv_cancel_left j hB₂.ne'
  rw [hjdef]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = c₀ + t₀ * j := ⟨_, rfl⟩
  rw [← hc]
  have hj1 : 1 ≤ j := by
    have hpB : B₂ ≤ (p : ℤ) - 1 := by
      have : B₂.natAbs ≤ Mn := Nat.le_of_dvd hMpos ⟨8 * (max 1 |D'|).natAbs * (2 * k).natAbs * t₀.natAbs, by rw [hMn]; ring⟩
      have : (B₂.natAbs : ℤ) = B₂ := by rw [Int.natCast_natAbs, abs_of_pos hB₂]
      omega
    by_contra hcon; push Not at hcon
    have : B₂ * j ≤ B₂ * 0 := mul_le_mul_of_nonneg_left (by omega) hB₂.le
    linarith
  have hct : B₂ * c + m₂ = t₀ * p := by rw [hc]; linear_combination (-t₀) * hj - ht₀def
  have hc₀c : c₀ < c := by rw [hc]; nlinarith
  have hpt : (p : ℤ) ∣ B₂ * c + m₂ := ⟨t₀, by rw [hct]; ring⟩
  -- A2-1 (D' ≠ 0, reciprocity) / A2-2 (D' = 0, no reciprocity): the discriminant is a square mod p
  have hdisc_sq : IsSquare (((B₁ * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q) : ℤ) : ZMod p) := by
    by_cases hne : D' = 0
    · have h0 : (p : ℤ) ∣ (B₁ * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q) :=
        disc_square_of_dPrime_zero A B₁ B₂ k l m₁ m₂ q c p hp (hD' ▸ hne) hpt hpB₂
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h0]
      exact ⟨0, by simp⟩
    · have hid := dPrime_identity A B₁ B₂ k l m₁ m₂ q c
      rw [← hD'] at hid
      have hz : (((B₂ * c + m₂) * (B₁ ^ 2 * (B₂ * c + m₂) + 2 * B₁ * (B₂ * m₁ - B₁ * m₂)
          - 4 * k * A * (B₂ * c + m₂) + 8 * k * A * m₂ - 4 * k * l * B₂) : ℤ) : ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.dvd.mul_right hpt _
      rw [← hid] at hz
      have hB₂z : ((B₂ : ℤ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpB₂
      have hD'sq : IsSquare ((D' : ℤ) : ZMod p) :=
        square_mod_prime_of_one_mod_eight_abs p hp D' hne (Nat.ModEq.of_dvd (hD'dvd hne) hpmod)
      obtain ⟨s, hs⟩ := hD'sq
      push_cast at hz hs hB₂z ⊢
      refine ⟨s / (B₂ : ZMod p), ?_⟩
      have : ((B₁ : ZMod p) * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)
          = (B₂ : ZMod p) ^ 2 * (((B₁ : ZMod p) * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)) / (B₂ : ZMod p) ^ 2 := by
        field_simp
      rw [this, show (B₂ : ZMod p) ^ 2 * (((B₁ : ZMod p) * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)) = (D' : ZMod p) by
        linear_combination hz, hs]
      field_simp
  obtain ⟨up, hup⟩ := rank_one_coupled_discriminant_nonzero p hp k (B₁ * c + m₁) (A * c ^ 2 + l * c + q) hp2k hdisc_sq
  have hcop : IsCoprime t₀ (p : ℤ) := by
    have hnat : t₀.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr ht₀.ne') hc
      have : (t₀.natAbs : ℤ) = t₀ := by rw [Int.natCast_natAbs, abs_of_pos ht₀]
      have hpt₀ : t₀ < (p : ℤ) := by
        have : t₀.natAbs ≤ Mn := Nat.le_of_dvd hMpos ⟨8 * (max 1 |D'|).natAbs * B₂.natAbs * (2 * k).natAbs, by rw [hMn]; ring⟩
        omega
      omega
    have := hnat.isCoprime
    rw [Int.natCast_natAbs, abs_of_pos ht₀] at this
    exact this
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨u, hu⟩ : ∃ u : ℤ, u = up * (a * t₀) + u₀ * (b * p) := ⟨_, rfl⟩
  have hu₀ : t₀ ∣ u - u₀ := ⟨a * (up - u₀), by rw [hu]; linear_combination u₀ * hab⟩
  have hup' : (p : ℤ) ∣ u - up := ⟨b * (u₀ - up), by rw [hu]; linear_combination up * hab⟩
  have hup2 : (p : ℤ) ∣ qOne A B₁ k l m₁ q c up := by rw [qOne_as_quadratic]; exact hup
  refine ⟨hc₀c, hct, u, up, hu₀, hup', hup2, ?_⟩
  rw [hct]
  apply IsCoprime.mul_dvd ⟨a, b, hab⟩
  · have hcc : c ≡ c₀ [ZMOD t₀] := by
      rw [Int.modEq_iff_dvd]; exact ⟨-j, by rw [hc]; ring⟩
    have huu : u ≡ u₀ [ZMOD t₀] := by
      rw [Int.modEq_iff_dvd]; obtain ⟨w, hw⟩ := hu₀; exact ⟨-w, by linear_combination -hw⟩
    have hQ : qOne A B₁ k l m₁ q c u ≡ qOne A B₁ k l m₁ q c₀ u₀ [ZMOD t₀] := by
      unfold qOne
      exact ((((((hcc.pow 2).mul_left A).add (((Int.ModEq.refl B₁).mul hcc).mul huu)).add ((huu.pow 2).mul_left k)).add
        (hcc.mul_left l)).add (huu.mul_left m₁)).add (Int.ModEq.refl q)
    rw [Int.modEq_iff_dvd] at hQ
    have := dvd_sub hdiv hQ
    simpa using this
  · have huu : u ≡ up [ZMOD p] := by
      rw [Int.modEq_iff_dvd]; obtain ⟨w, hw⟩ := hup'; exact ⟨-w, by linear_combination -hw⟩
    have hQ : qOne A B₁ k l m₁ q c u ≡ qOne A B₁ k l m₁ q c up [ZMOD p] := by
      unfold qOne
      exact (((((Int.ModEq.refl (A * c ^ 2)).add ((huu).mul_left (B₁ * c))).add ((huu.pow 2).mul_left k)).add
        (Int.ModEq.refl (l * c))).add (huu.mul_left m₁)).add (Int.ModEq.refl q)
    rw [Int.modEq_iff_dvd] at hQ
    have := dvd_sub hup2 hQ
    simpa using this

/-- Sanity: the baseline existence statement follows by choosing one prime. -/
theorem baseline_rankOne_step_of_allGoodPrime (A B₁ B₂ k l m₁ m₂ q c₀ u₀ : ℤ) (hB₂ : 0 < B₂)
    (hk : k ≠ 0) (ht₀ : 0 < B₂ * c₀ + m₂) (hdiv : (B₂ * c₀ + m₂) ∣ qOne A B₁ k l m₁ q c₀ u₀) :
    ∃ c u : ℤ, c₀ < c ∧ (B₂ * c + m₂) ∣ qOne A B₁ k l m₁ q c u := by
  have hM0 : rankOneModulusNat (dPrime A B₁ B₂ k l m₁ m₂ q) B₂ k (B₂ * c₀ + m₂) ≠ 0 := by
    unfold rankOneModulusNat
    have h1 : (max 1 |dPrime A B₁ B₂ k l m₁ m₂ q|).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |dPrime A B₁ B₂ k l m₁ m₂ q|; omega)
    have h2 : B₂.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hB₂.ne'
    have h3 : (2 * k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero two_ne_zero hk)
    have h4 : (B₂ * c₀ + m₂).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    positivity
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one _ hM0
  obtain ⟨hlt, -, u, -, -, -, -, hdvd⟩ :=
    rank_one_coupled_prime_step_allGoodPrime A B₁ B₂ k l m₁ m₂ q c₀ u₀ hB₂ hk ht₀ hdiv p hp hpM hpmod
  exact ⟨_, u, hlt, hdvd⟩

end DiophCompression.ResearchUpgrade
