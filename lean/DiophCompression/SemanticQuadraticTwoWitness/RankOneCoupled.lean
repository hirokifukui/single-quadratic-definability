/-
  DiophCompression/SemanticQuadraticTwoWitness/RankOneCoupled.lean — GPT r07 必須5 (s8, claude.ai direct).
  Rank-one witness block in normal form W = k u² (k ≠ 0). Coupled case B₂ ≠ 0: from a fiber element with
  t₀ = B₂c₀ + m₂ > 0, a prime p ≡ 1 (mod 8·max(1,|D'|)·B₂·2|k|·t₀) with p > t₀ gives c = c₀ + t₀(p−1)/B₂ and a
  witness u (CRT: u ≡ u₀ mod t₀, u ≡ root mod p) with t₀p ∣ Q(c,u); iterating, the fiber set is infinite; otherwise
  every fiber element has B₂c + m₂ ≤ 0, hence c ≤ |m₂|. The root mod p comes from the discriminant identity
  B₂²·disc_u ≡ D' (mod p) and quadratic reciprocity (D' ≠ 0) or the double root (D' = 0).
  Frozen statements: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02). Mathematics: CLASSIFICATION_2W.md §2b (revised s8).
-/
import DiophCompression.SemanticQuadraticTwoWitness.DefsScaled
import DiophCompression.SemanticQuadraticTwoWitness.Bridge2W
import DiophCompression.SemanticQuadratic.FiberDichotomy

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral

/-! ### Root extraction mod p -/

theorem rank_one_coupled_discriminant_nonzero (p : ℕ) (hp : p.Prime) (k b e : ℤ) (hk : ¬ (p : ℤ) ∣ 2 * k)
    (hd : IsSquare ((b ^ 2 - 4 * k * e : ℤ) : ZMod p)) : ∃ u : ℤ, (p : ℤ) ∣ k * u ^ 2 + b * u + e := by
  haveI := Fact.mk hp
  have h2k : ((2 * k : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hk
  push_cast at h2k hd
  obtain ⟨s, hs⟩ := hd
  obtain ⟨x, hx⟩ : ∃ x : ZMod p, x = (-(b : ZMod p) + s) / (2 * (k : ZMod p)) := ⟨_, rfl⟩
  refine ⟨(x.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  have hk0 : (k : ZMod p) ≠ 0 := right_ne_zero_of_mul h2k
  have h20 : (2 : ZMod p) ≠ 0 := left_ne_zero_of_mul h2k
  have hlin : 2 * (k : ZMod p) * x + b = s := by rw [hx]; field_simp; ring
  have key : (4 * (k : ZMod p)) * (k * x ^ 2 + b * x + e) = (2 * k * x + b) ^ 2 - (b ^ 2 - 4 * k * e) := by ring
  rw [hlin, hs] at key
  have key2 : (4 * (k : ZMod p)) * (k * x ^ 2 + b * x + e) = 0 := by rw [key]; ring
  have h4k : (4 * (k : ZMod p)) ≠ 0 := by
    have : (4 : ZMod p) * k = 2 * (2 * k) := by ring
    rw [this]; exact mul_ne_zero h20 h2k
  exact (mul_eq_zero.mp key2).resolve_left h4k

theorem rank_one_coupled_discriminant_zero (p : ℕ) (hp : p.Prime) (k b e : ℤ) (hk : ¬ (p : ℤ) ∣ 2 * k)
    (hd : (p : ℤ) ∣ b ^ 2 - 4 * k * e) : ∃ u : ℤ, (p : ℤ) ∣ k * u ^ 2 + b * u + e := by
  apply rank_one_coupled_discriminant_nonzero p hp k b e hk
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd]
  exact ⟨0, by simp⟩

/-! ### Reciprocity -/

theorem square_mod_prime_of_one_mod_eight_abs (p : ℕ) (hp : p.Prime) (D : ℤ) (hD : D ≠ 0)
    (h : p ≡ 1 [MOD 8 * D.natAbs]) : IsSquare ((D : ℤ) : ZMod p) := by
  haveI := Fact.mk hp
  apply ZMod.isSquare_of_jacobiSym_eq_one
  have h8 : p % 8 = 1 := by
    have := Nat.ModEq.of_mul_right _ h
    exact this
  have h4 : p % 4 = 1 := by omega
  have hodd : Odd p := by rw [Nat.odd_iff]; omega
  obtain ⟨e, m, hm, hDm⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hD)
  have hDdecomp : D = D.sign * ((2 : ℤ) ^ e * (m : ℤ)) := by
    have := Int.sign_mul_natAbs D
    rw [hDm] at this; push_cast at this; linear_combination -this
  rw [hDdecomp, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left]
  have hJ2 : jacobiSym 2 p = 1 := by
    rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_mod_eight, h8]; decide
  have hJs : jacobiSym D.sign p = 1 := by
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · rw [Int.sign_eq_neg_one_of_neg hneg, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four h4]
    · rw [Int.sign_eq_one_of_pos hpos, jacobiSym.one_left]
  have hJm : jacobiSym (m : ℤ) p = 1 := by
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four h4 hm]
    have hmdvd : m ∣ 8 * D.natAbs := ⟨8 * 2 ^ e, by rw [hDm]; ring⟩
    have hpm : p ≡ 1 [MOD m] := Nat.ModEq.of_dvd hmdvd h
    have hcast : ((p : ℤ) % (m : ℤ)) = (1 : ℤ) % (m : ℤ) := by
      have h1 : ((p % m : ℕ) : ℤ) = ((1 % m : ℕ) : ℤ) := by exact_mod_cast hpm
      rw [Int.natCast_mod, Int.natCast_mod, Nat.cast_one] at h1
      exact h1
    rw [jacobiSym.mod_left, hcast, ← jacobiSym.mod_left, jacobiSym.one_left]
  rw [hJ2, hJs, hJm]; simp

/-! ### The prime step -/

/-- The value of D' : B₂²·disc_u(c) ≡ D' (mod B₂c + m₂). -/
def dPrime (A B₁ B₂ k l m₁ m₂ q : ℤ) : ℤ :=
  (B₂ * m₁ - B₁ * m₂) ^ 2 - 4 * k * (A * m₂ ^ 2 - B₂ * l * m₂ + B₂ ^ 2 * q)

theorem dPrime_identity (A B₁ B₂ k l m₁ m₂ q c : ℤ) :
    B₂ ^ 2 * ((B₁ * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)) - dPrime A B₁ B₂ k l m₁ m₂ q
      = (B₂ * c + m₂) * (B₁ ^ 2 * (B₂ * c + m₂) + 2 * B₁ * (B₂ * m₁ - B₁ * m₂)
          - 4 * k * A * (B₂ * c + m₂) + 8 * k * A * m₂ - 4 * k * l * B₂) := by
  unfold dPrime; ring

theorem qOne_as_quadratic (A B₁ k l m₁ q c u : ℤ) :
    qOne A B₁ k l m₁ q c u = k * u ^ 2 + (B₁ * c + m₁) * u + (A * c ^ 2 + l * c + q) := by
  unfold qOne; ring

theorem rank_one_coupled_prime_step (A B₁ B₂ k l m₁ m₂ q c₀ u₀ : ℤ) (hB₂ : 0 < B₂) (hk : k ≠ 0)
    (ht₀ : 0 < B₂ * c₀ + m₂) (hdiv : (B₂ * c₀ + m₂) ∣ qOne A B₁ k l m₁ q c₀ u₀) :
    ∃ c u : ℤ, c₀ < c ∧ (B₂ * c + m₂) ∣ qOne A B₁ k l m₁ q c u := by
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
  refine ⟨c, u, hc₀c, ?_⟩
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
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_coupled_discriminant_zero
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_coupled_discriminant_nonzero
#print axioms DiophCompression.SemanticQuadraticTwoWitness.square_mod_prime_of_one_mod_eight_abs
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_coupled_prime_step
