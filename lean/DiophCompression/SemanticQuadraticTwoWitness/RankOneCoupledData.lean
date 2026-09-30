/-
  DiophCompression/SemanticQuadraticTwoWitness/RankOneCoupledData.lean — APAL Structural Theory Gate 5,
  必須F step 2 (leaf B1c) (s28, 2026-09-02, claude.ai direct).

  Branch B1c in DATA-CARRYING form, the rank-one analogue of the s27 B2 lemma
  `moving_modulus_prime_step_data`. The sealed `rank_one_coupled_prime_step` establishes the stage prime,
  the modulus recurrence `B₂c + m₂ = (B₂c₀ + m₂)·p`, the congruence `p ≡ 1 mod M` with
  `M = 8·max(1,|D'|)·B₂·|2k|·t₀`, and the CRT relation `t₀ ∣ u − u₀`, and then returns only
  "some larger fibre point". Here the same proof returns all of it, so the leaf can build a
  moving-modulus step orbit exactly as branch B2 does. The proof script is the sealed one; only the
  conclusion and the final `refine` changed. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankOneCoupled

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

theorem rank_one_coupled_prime_step_data (A B₁ B₂ k l m₁ m₂ q c₀ u₀ : ℤ) (hB₂ : 0 < B₂) (hk : k ≠ 0)
    (ht₀ : 0 < B₂ * c₀ + m₂) (hdiv : (B₂ * c₀ + m₂) ∣ qOne A B₁ k l m₁ q c₀ u₀) :
    ∃ (p M : ℕ) (c u : ℤ), p.Prime ∧ c₀ < c ∧
      M = 8 * (max 1 |dPrime A B₁ B₂ k l m₁ m₂ q|).natAbs * B₂.natAbs * (2 * k).natAbs
            * (B₂ * c₀ + m₂).natAbs ∧
      M < p ∧ p ≡ 1 [MOD M] ∧
      B₂ * c + m₂ = (B₂ * c₀ + m₂) * p ∧
      (B₂ * c₀ + m₂) ∣ u - u₀ ∧
      (B₂ * c + m₂) ∣ qOne A B₁ k l m₁ q c u := by
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℤ, t₀ = B₂ * c₀ + m₂ := ⟨_, rfl⟩
  rw [← ht₀def] at ht₀ hdiv
  obtain ⟨D', hD'⟩ : ∃ D' : ℤ, D' = dPrime A B₁ B₂ k l m₁ m₂ q := ⟨_, rfl⟩
  -- the modulus
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, Mn = 8 * (max 1 |D'|).natAbs * B₂.natAbs * (2 * k).natAbs * t₀.natAbs := ⟨_, rfl⟩
  have h1 : (max 1 |D'|).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |D'|; omega)
  have h2 : B₂.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hB₂.ne'
  have h3 : (2 * k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero two_ne_zero hk)
  have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
  have hM0 : Mn ≠ 0 := by
    rw [hMn]; positivity
  have hMpos : 0 < Mn := Nat.pos_of_ne_zero hM0
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  -- divisibility consequences of p ≡ 1 mod Mn
  have hMdvd : (Mn : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h'
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
  have hpt₀ : t₀ < (p : ℤ) := by
    have : t₀.natAbs ≤ Mn := Nat.le_of_dvd hMpos ⟨8 * (max 1 |D'|).natAbs * B₂.natAbs * (2 * k).natAbs, by rw [hMn]; ring⟩
    have : (t₀.natAbs : ℤ) = t₀ := by rw [Int.natCast_natAbs, abs_of_pos ht₀]
    omega
  -- p ∤ 2k and p ∤ B₂ (they divide p − 1)
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
  -- the new output
  obtain ⟨j, hj⟩ := hB₂dvd
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = c₀ + t₀ * j := ⟨_, rfl⟩
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
  -- root mod p of Q(c, ·)
  have hpt : (p : ℤ) ∣ B₂ * c + m₂ := ⟨t₀, by rw [hct]; ring⟩
  have hdisc_sq : IsSquare (((B₁ * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q) : ℤ) : ZMod p) := by
    have hid := dPrime_identity A B₁ B₂ k l m₁ m₂ q c
    rw [← hD'] at hid
    have hz : (((B₂ * c + m₂) * (B₁ ^ 2 * (B₂ * c + m₂) + 2 * B₁ * (B₂ * m₁ - B₁ * m₂)
        - 4 * k * A * (B₂ * c + m₂) + 8 * k * A * m₂ - 4 * k * l * B₂) : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.dvd.mul_right hpt _
    rw [← hid] at hz
    have hB₂z : ((B₂ : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpB₂
    have hD'sq : IsSquare ((D' : ℤ) : ZMod p) := by
      by_cases hne : D' = 0
      · rw [hne]; exact ⟨0, by simp⟩
      · exact square_mod_prime_of_one_mod_eight_abs p hp D' hne (Nat.ModEq.of_dvd (hD'dvd hne) hpmod)
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
  -- CRT: u ≡ u₀ (mod t₀), u ≡ up (mod p)
  have hcop : IsCoprime t₀ (p : ℤ) := by
    have hnat : t₀.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr ht₀.ne') hc
      have : (t₀.natAbs : ℤ) = t₀ := by rw [Int.natCast_natAbs, abs_of_pos ht₀]
      omega
    have := hnat.isCoprime
    rw [Int.natCast_natAbs, abs_of_pos ht₀] at this
    exact this
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨u, hu⟩ : ∃ u : ℤ, u = up * (a * t₀) + u₀ * (b * p) := ⟨_, rfl⟩
  have hu₀ : t₀ ∣ u - u₀ := ⟨a * (up - u₀), by rw [hu]; linear_combination u₀ * hab⟩
  have hup' : (p : ℤ) ∣ u - up := ⟨b * (u₀ - up), by rw [hu]; linear_combination up * hab⟩
  refine ⟨p, Mn, c, u, hp, hc₀c, by rw [hMn, hD', ht₀def], hpM, hpmod,
    by rw [hct, ht₀def], ht₀def ▸ hu₀, ?_⟩
  rw [hct]
  apply IsCoprime.mul_dvd ⟨a, b, hab⟩
  · -- t₀ ∣ Q(c,u): Q(c,u) ≡ Q(c₀,u₀) mod t₀
    have hcc : c ≡ c₀ [ZMOD t₀] := by
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
  · -- p ∣ Q(c,u): Q(c,u) ≡ Q(c,up) mod p
    have huu : u ≡ up [ZMOD p] := by
      rw [Int.modEq_iff_dvd]; obtain ⟨w, hw⟩ := hup'; exact ⟨-w, by linear_combination -hw⟩
    have hQ : qOne A B₁ k l m₁ q c u ≡ qOne A B₁ k l m₁ q c up [ZMOD p] := by
      unfold qOne
      exact (((((Int.ModEq.refl (A * c ^ 2)).add ((huu).mul_left (B₁ * c))).add ((huu.pow 2).mul_left k)).add
        (Int.ModEq.refl (l * c))).add (huu.mul_left m₁)).add (Int.ModEq.refl q)
    rw [Int.modEq_iff_dvd] at hQ
    have hup2 : (p : ℤ) ∣ qOne A B₁ k l m₁ q c up := by rw [qOne_as_quadratic]; exact hup
    have := dvd_sub hup2 hQ
    simpa using this

end DiophCompression.SemanticQuadraticTwoWitness

#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_coupled_prime_step_data
