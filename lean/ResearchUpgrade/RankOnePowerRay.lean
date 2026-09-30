/-
  RankOnePowerRay.lean — Gate-18 research program, Packet B3 for the rank-one coupled branch.
  ONE good prime p (chosen once, Dirichlet existence only — no density), then the prime-POWER ray
  c_E = c₀ + t₀·(p^E − 1)/B₂, B₂ c_E + m₂ = t₀ p^E, E ≥ 1. The witness at level E: CRT of the old
  modulus t₀ (u ≡ u₀) and p^E, where the mod-p^E root of the quadratic in u comes from elementary Hensel
  (B1) when D' ≠ 0 (the level-1 root is simple because p ∤ D'), and from the vertex −b/(2k) mod p^E when
  D' = 0 (p^E ∣ disc from `dPrime_identity`). The outputs are injective in E with envelope
  |c_E| ≤ (|c₀| + t₀)·p·p^E, hence `ExponentialInjection (rankOneOutputSet …)` — UNCONDITIONAL:
  the A5-1 analytic input is not used.
-/
import ResearchUpgrade.Hensel
import ResearchUpgrade.PrimeRay
import ResearchUpgrade.Shadow.FamilyR

namespace DiophCompression.ResearchUpgrade

open Polynomial DiophCompression.SemanticQuadratic DiophCompression.SemanticQuadraticTwoWitness

/-! ### Coprimality helpers -/

theorem isCoprime_prime_of_not_dvd (p : ℕ) (hp : p.Prime) (x : ℤ) (h : ¬ (p : ℤ) ∣ x) :
    IsCoprime (p : ℤ) x :=
  (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr h

/-! ### Roots of a quadratic modulo p^E -/

/-- Simple case: discriminant a non-zero square mod `p` ⇒ a root mod `p^E` for every `E ≥ 1` (Hensel). -/
theorem quad_root_pow_of_disc_unit (p : ℕ) (hp : p.Prime) (k b c : ℤ) (h2k : ¬ (p : ℤ) ∣ 2 * k)
    (hsq : IsSquare ((b ^ 2 - 4 * k * c : ℤ) : ZMod p)) (hdisc : ¬ (p : ℤ) ∣ b ^ 2 - 4 * k * c)
    (E : ℕ) (hE : 1 ≤ E) : ∃ u : ℤ, (p : ℤ) ^ E ∣ k * u ^ 2 + b * u + c := by
  obtain ⟨u₁, hu₁⟩ := rank_one_coupled_discriminant_nonzero p hp k b c h2k hsq
  set f : ℤ[X] := C k * X ^ 2 + C b * X + C c with hf
  have hev : ∀ u, f.eval u = k * u ^ 2 + b * u + c := by
    intro u; simp [hf, eval_add, eval_mul, eval_pow, eval_X]
  have hev' : ∀ u, f.derivative.eval u = 2 * k * u + b := by
    intro u
    simp [hf, derivative_add, derivative_mul, derivative_X, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hd : ¬ (p : ℤ) ∣ f.derivative.eval u₁ := by
    rw [hev']; intro hc; apply hdisc
    have key : b ^ 2 - 4 * k * c = (2 * k * u₁ + b) ^ 2 - 4 * k * (k * u₁ ^ 2 + b * u₁ + c) := by ring
    rw [key]
    exact dvd_sub (dvd_pow hc two_ne_zero) (hu₁.mul_left _)
  obtain ⟨u, hu, -⟩ := hensel_lift f p hp u₁ (by rw [hev]; exact hu₁) hd E hE
  exact ⟨u, by rwa [hev] at hu⟩

/-- Double-root case: `p^E ∣ disc` ⇒ the vertex `−b/(2k)` mod `p^E` is a root mod `p^E`. -/
theorem quad_root_pow_of_disc_zero (p : ℕ) (hp : p.Prime) (k b c : ℤ) (h2k : ¬ (p : ℤ) ∣ 2 * k)
    (hp2 : p ≠ 2) (E : ℕ) (hdisc : (p : ℤ) ^ E ∣ b ^ 2 - 4 * k * c) :
    ∃ u : ℤ, (p : ℤ) ^ E ∣ k * u ^ 2 + b * u + c := by
  have hcop : IsCoprime ((p : ℤ) ^ E) (2 * k) := (isCoprime_prime_of_not_dvd p hp _ h2k).pow_left
  obtain ⟨β, α, hαβ⟩ := hcop   -- β p^E + α (2k) = 1
  set u : ℤ := -(α * b) with hu
  have h1 : 2 * k * u + b = b * β * (p : ℤ) ^ E := by
    rw [hu]; linear_combination (-b) * hαβ
  have h4 : (p : ℤ) ^ E ∣ 4 * k * (k * u ^ 2 + b * u + c) := by
    have : 4 * k * (k * u ^ 2 + b * u + c) = (2 * k * u + b) ^ 2 - (b ^ 2 - 4 * k * c) := by ring
    rw [this, h1]
    exact dvd_sub ⟨b ^ 2 * β ^ 2 * (p : ℤ) ^ E, by ring⟩ hdisc
  have hp2' : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have h4k : ¬ (p : ℤ) ∣ 4 * k := by
    intro h
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have : (4 * k : ℤ) = 2 * (2 * k) := by ring
    rw [this] at h
    rcases hpZ.dvd_or_dvd h with h | h
    · exact hp2' h
    · exact h2k h
  have hcop4 : IsCoprime ((p : ℤ) ^ E) (4 * k) := (isCoprime_prime_of_not_dvd p hp _ h4k).pow_left
  exact ⟨u, hcop4.dvd_of_dvd_mul_left h4⟩

/-! ### The rank-one quadratic at a modulus `p^E ∣ B₂ c + m₂` -/

/-- Level-`E` root of `qOne(c, ·)` when `p^E ∣ B₂ c + m₂`, for a good prime `p`. -/
theorem rankOne_root_pow (A B₁ B₂ k l m₁ m₂ q : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h2k : ¬ (p : ℤ) ∣ 2 * k) (hpB₂ : ¬ (p : ℤ) ∣ B₂)
    (hsqD : dPrime A B₁ B₂ k l m₁ m₂ q ≠ 0 → IsSquare ((dPrime A B₁ B₂ k l m₁ m₂ q : ℤ) : ZMod p))
    (hpD : dPrime A B₁ B₂ k l m₁ m₂ q ≠ 0 → ¬ (p : ℤ) ∣ dPrime A B₁ B₂ k l m₁ m₂ q)
    (E : ℕ) (hE : 1 ≤ E) (c : ℤ) (hpt : (p : ℤ) ^ E ∣ B₂ * c + m₂) :
    ∃ u : ℤ, (p : ℤ) ^ E ∣ qOne A B₁ k l m₁ q c u := by
  haveI := Fact.mk hp
  set D' := dPrime A B₁ B₂ k l m₁ m₂ q with hD'
  have hid := dPrime_identity A B₁ B₂ k l m₁ m₂ q c
  rw [← hD'] at hid
  set disc := (B₁ * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q) with hdisc
  have hpt1 : (p : ℤ) ∣ B₂ * c + m₂ := (dvd_pow_self _ (by omega)).trans hpt
  have hroot : ∃ u : ℤ, (p : ℤ) ^ E ∣ k * u ^ 2 + (B₁ * c + m₁) * u + (A * c ^ 2 + l * c + q) := by
    by_cases hne : D' = 0
    · -- p^E ∣ B₂² disc ⇒ p^E ∣ disc
      have hB2 : (p : ℤ) ^ E ∣ B₂ ^ 2 * disc := by
        have : B₂ ^ 2 * disc = (B₂ * c + m₂) * (B₁ ^ 2 * (B₂ * c + m₂) + 2 * B₁ * (B₂ * m₁ - B₁ * m₂)
            - 4 * k * A * (B₂ * c + m₂) + 8 * k * A * m₂ - 4 * k * l * B₂) := by
          linear_combination hid + hne
        rw [this]; exact hpt.mul_right _
      have hcopB : IsCoprime ((p : ℤ) ^ E) (B₂ ^ 2) :=
        ((isCoprime_prime_of_not_dvd p hp _ hpB₂).pow_left).pow_right
      exact quad_root_pow_of_disc_zero p hp k _ _ h2k hp2 E (hcopB.dvd_of_dvd_mul_left hB2)
    · have hz : (((B₂ * c + m₂) * (B₁ ^ 2 * (B₂ * c + m₂) + 2 * B₁ * (B₂ * m₁ - B₁ * m₂)
          - 4 * k * A * (B₂ * c + m₂) + 8 * k * A * m₂ - 4 * k * l * B₂) : ℤ) : ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.dvd.mul_right hpt1 _
      rw [← hid] at hz
      have hB₂z : ((B₂ : ℤ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpB₂
      obtain ⟨s, hs⟩ := hsqD hne
      have hsq : IsSquare ((disc : ℤ) : ZMod p) := by
        rw [hdisc]
        rw [hdisc] at hz
        push_cast at hz hs hB₂z ⊢
        refine ⟨s / (B₂ : ZMod p), ?_⟩
        have : ((B₁ : ZMod p) * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)
            = (B₂ : ZMod p) ^ 2 * (((B₁ : ZMod p) * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)) / (B₂ : ZMod p) ^ 2 := by
          field_simp
        rw [this, show (B₂ : ZMod p) ^ 2 * (((B₁ : ZMod p) * c + m₁) ^ 2 - 4 * k * (A * c ^ 2 + l * c + q)) = (D' : ZMod p) by
          linear_combination hz, hs]
        field_simp
      have hndisc : ¬ (p : ℤ) ∣ disc := by
        intro hc; apply hpD hne
        have : D' = B₂ ^ 2 * disc - (B₂ * c + m₂) * (B₁ ^ 2 * (B₂ * c + m₂) + 2 * B₁ * (B₂ * m₁ - B₁ * m₂)
            - 4 * k * A * (B₂ * c + m₂) + 8 * k * A * m₂ - 4 * k * l * B₂) := by linear_combination -hid
        rw [this]
        exact dvd_sub (hc.mul_left _) (hpt1.mul_right _)
      exact quad_root_pow_of_disc_unit p hp k _ _ h2k hsq hndisc E hE
  obtain ⟨u, hu⟩ := hroot
  exact ⟨u, by rw [qOne_as_quadratic]; exact hu⟩

/-! ### CRT recombination with the old modulus -/

theorem rankOne_combine (A B₁ k l m₁ q c₀ u₀ c uN t₀ N : ℤ) (j : ℤ) (hc : c = c₀ + t₀ * j)
    (hdiv : t₀ ∣ qOne A B₁ k l m₁ q c₀ u₀) (hcop : IsCoprime t₀ N)
    (hN : N ∣ qOne A B₁ k l m₁ q c uN) : ∃ u : ℤ, t₀ * N ∣ qOne A B₁ k l m₁ q c u := by
  obtain ⟨a, b, hab⟩ := hcop
  set u : ℤ := uN * (a * t₀) + u₀ * (b * N) with hu
  have hu₀ : t₀ ∣ u - u₀ := ⟨a * (uN - u₀), by rw [hu]; linear_combination u₀ * hab⟩
  have hup' : N ∣ u - uN := ⟨b * (u₀ - uN), by rw [hu]; linear_combination uN * hab⟩
  refine ⟨u, IsCoprime.mul_dvd ⟨a, b, hab⟩ ?_ ?_⟩
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
  · have huu : u ≡ uN [ZMOD N] := by
      rw [Int.modEq_iff_dvd]; obtain ⟨w, hw⟩ := hup'; exact ⟨-w, by linear_combination -hw⟩
    have hQ : qOne A B₁ k l m₁ q c u ≡ qOne A B₁ k l m₁ q c uN [ZMOD N] := by
      unfold qOne
      exact (((((Int.ModEq.refl (A * c ^ 2)).add ((huu).mul_left (B₁ * c))).add ((huu.pow 2).mul_left k)).add
        (Int.ModEq.refl (l * c))).add (huu.mul_left m₁)).add (Int.ModEq.refl q)
    rw [Int.modEq_iff_dvd] at hQ
    have := dvd_sub hN hQ
    simpa using this

/-! ### B3 (rank one): the prime-power ray gives an exponential injection, unconditionally -/

theorem rankOne_exponentialInjection (A B₁ B₂ k l m₁ m₂ q c₀ u₀ : ℤ) (hB₂ : 0 < B₂) (hk : k ≠ 0)
    (ht₀ : 0 < B₂ * c₀ + m₂) (hdiv : (B₂ * c₀ + m₂) ∣ qOne A B₁ k l m₁ q c₀ u₀) :
    ExponentialInjection (rankOneOutputSet A B₁ B₂ k l m₁ m₂ q) := by
  -- one good prime, once
  set t₀ := B₂ * c₀ + m₂ with ht₀def
  set D' := dPrime A B₁ B₂ k l m₁ m₂ q with hD'
  set Mn : ℕ := rankOneModulusNat D' B₂ k t₀ with hMn
  have hM0 : Mn ≠ 0 := by
    rw [hMn]; unfold rankOneModulusNat
    have h1 : (max 1 |D'|).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |D'|; omega)
    have h2 : B₂.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hB₂.ne'
    have h3 : (2 * k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero two_ne_zero hk)
    have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    positivity
  have hMpos : 0 < Mn := Nat.pos_of_ne_zero hM0
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  have hMdvd : (Mn : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by have := hp.one_lt; omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by have := hp.one_lt; omega), Nat.cast_one] at h'
  have hMcast : (Mn : ℤ) = 8 * abs (max 1 (abs D')) * |B₂| * |2 * k| * |t₀| := by
    rw [hMn]; unfold rankOneModulusNat; push_cast; ring
  have hB₂dvd : B₂ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast, abs_of_pos hB₂]; exact ⟨8 * abs (max 1 (abs D')) * |2 * k| * |t₀|, by ring⟩
  have h2kdvd : 2 * k ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs (2 * k)).trans ⟨8 * abs (max 1 (abs D')) * |B₂| * |t₀|, by ring⟩
  have ht₀dvd : t₀ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs t₀).trans ⟨8 * abs (max 1 (abs D')) * |B₂| * |2 * k|, by ring⟩
  have h2dvd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨4 * abs (max 1 (abs D')) * |B₂| * |2 * k| * |t₀|, by ring⟩
  have notdvd : ∀ x : ℤ, x ∣ (p : ℤ) - 1 → ¬ (p : ℤ) ∣ x := by
    intro x hx hc
    have := dvd_trans hc hx
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have := hp.one_lt; omega
  have hp2k : ¬ (p : ℤ) ∣ 2 * k := notdvd _ h2kdvd
  have hpB₂ : ¬ (p : ℤ) ∣ B₂ := notdvd _ hB₂dvd
  have hpt₀ : ¬ (p : ℤ) ∣ t₀ := notdvd _ ht₀dvd
  have hp2 : p ≠ 2 := by
    intro h; apply notdvd 2 h2dvd; rw [h]; norm_num
  have hD'dvd : D' ≠ 0 → (8 * D'.natAbs : ℕ) ∣ Mn := by
    intro hne
    rw [hMn]; unfold rankOneModulusNat
    rw [show (max 1 |D'|).natAbs = D'.natAbs by rw [max_eq_right (Int.one_le_abs hne), Int.natAbs_abs]]
    exact ⟨B₂.natAbs * (2 * k).natAbs * t₀.natAbs, by ring⟩
  have hsqD : D' ≠ 0 → IsSquare ((D' : ℤ) : ZMod p) := fun hne =>
    square_mod_prime_of_one_mod_eight_abs p hp D' hne (Nat.ModEq.of_dvd (hD'dvd hne) hpmod)
  have hpD : D' ≠ 0 → ¬ (p : ℤ) ∣ D' := by
    intro hne
    apply notdvd
    refine dvd_trans ?_ hMdvd
    rw [hMcast, show abs (max 1 (abs D')) = |D'| by rw [max_eq_right (Int.one_le_abs hne), abs_abs]]
    exact (self_dvd_abs D').trans ⟨8 * |B₂| * |2 * k| * |t₀|, by ring⟩
  -- the ray c_E, E = e + 1
  have hpow : ∀ E : ℕ, B₂ ∣ (p : ℤ) ^ E - 1 := fun E =>
    hB₂dvd.trans (by simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 E)
  set g : ℕ → ℤ := fun e => c₀ + t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂) with hg
  have hmod : ∀ e, B₂ * g e + m₂ = t₀ * (p : ℤ) ^ (e + 1) := by
    intro e
    obtain ⟨j, hj⟩ := hpow (e + 1)
    have : ((p : ℤ) ^ (e + 1) - 1) / B₂ = j := by rw [hj]; exact Int.mul_ediv_cancel_left j hB₂.ne'
    simp only [hg]; rw [this]; linear_combination (-t₀) * hj - ht₀def
  have hpR : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hp2R : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hjpos : ∀ e, 0 ≤ ((p : ℤ) ^ (e + 1) - 1) / B₂ := fun e =>
    Int.ediv_nonneg (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith) hB₂.le
  refine ⟨((|c₀| + t₀) * p).toNat, p, g, ?_, hp.two_le, ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ (|c₀| + t₀) * p := by nlinarith [abs_nonneg c₀]
    have h' : (1 : ℤ) ≤ ((|c₀| + t₀) * p).toNat := by rw [Int.toNat_of_nonneg (by linarith)]; exact this
    exact_mod_cast h'
  · -- injective: B₂ g e + m₂ = t₀ p^(e+1) is strictly monotone in e
    intro e e' h
    have h1 := hmod e; have h2 := hmod e'
    rw [h] at h1
    have : (p : ℤ) ^ (e + 1) = (p : ℤ) ^ (e' + 1) := by
      have := h1.symm.trans h2; exact mul_left_cancel₀ ht₀.ne' this
    have := pow_right_injective₀ (by positivity) (ne_of_gt hpR) this
    omega
  · -- membership
    intro e
    have hE : 1 ≤ e + 1 := by omega
    have hpt : (p : ℤ) ^ (e + 1) ∣ B₂ * g e + m₂ := by rw [hmod e]; exact dvd_mul_left _ _
    obtain ⟨uN, huN⟩ := rankOne_root_pow A B₁ B₂ k l m₁ m₂ q p hp hp2 hp2k hpB₂ hsqD hpD (e + 1) hE (g e) hpt
    have hcop : IsCoprime t₀ ((p : ℤ) ^ (e + 1)) :=
      ((isCoprime_prime_of_not_dvd p hp t₀ hpt₀).pow_left).symm
    obtain ⟨u, hu⟩ := rankOne_combine A B₁ k l m₁ q c₀ u₀ (g e) uN t₀ ((p : ℤ) ^ (e + 1))
      (((p : ℤ) ^ (e + 1) - 1) / B₂) rfl hdiv hcop huN
    refine ⟨u, ?_⟩
    rw [hmod e]; exact hu
  · -- envelope: |g e| ≤ (|c₀| + t₀) p · p^e
    intro e
    have hj := hjpos e
    have hjle : ((p : ℤ) ^ (e + 1) - 1) / B₂ ≤ (p : ℤ) ^ (e + 1) := by
      have h1 : ((p : ℤ) ^ (e + 1) - 1) / B₂ ≤ (p : ℤ) ^ (e + 1) - 1 :=
        Int.ediv_le_self _ (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith)
      linarith
    have hpe : (1 : ℤ) ≤ (p : ℤ) ^ (e + 1) := one_le_pow₀ hpR.le
    have hA : (((|c₀| + t₀) * p).toNat : ℤ) = (|c₀| + t₀) * p := Int.toNat_of_nonneg (by positivity)
    rw [hA]
    have hge : |g e| ≤ |c₀| + t₀ * (p : ℤ) ^ (e + 1) := by
      calc |g e| = |c₀ + t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂)| := rfl
        _ ≤ |c₀| + |t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂)| := abs_add_le _ _
        _ = |c₀| + t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂) := by
            rw [abs_of_nonneg (mul_nonneg ht₀.le hj)]
        _ ≤ |c₀| + t₀ * (p : ℤ) ^ (e + 1) := by nlinarith
    calc |g e| ≤ |c₀| + t₀ * (p : ℤ) ^ (e + 1) := hge
      _ ≤ (|c₀| + t₀) * (p : ℤ) ^ (e + 1) := by nlinarith [abs_nonneg c₀]
      _ = (|c₀| + t₀) * p * (p : ℤ) ^ e := by ring

/-- The same exponential injection landing in the ℕ-fibre `castSet (fiberSet2 …)`, with `(c₀ : ℕ)`
so that every ray output is `≥ c₀ ≥ 0`. Mirrors `moving_exponentialInjection_castSet`. -/
theorem rankOne_exponentialInjection_castSet (A B₁ B₂ k l m₁ m₂ q : ℤ) (c₀ : ℕ) (u₀ : ℤ)
    (hB₂ : 0 < B₂) (hk : k ≠ 0) (ht₀ : 0 < B₂ * (c₀ : ℤ) + m₂)
    (hdiv : (B₂ * (c₀ : ℤ) + m₂) ∣ qOne A B₁ k l m₁ q (c₀ : ℤ) u₀) :
    ExponentialInjection (castSet (fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q)) := by
  -- one good prime, once
  set t₀ := B₂ * (c₀ : ℤ) + m₂ with ht₀def
  set D' := dPrime A B₁ B₂ k l m₁ m₂ q with hD'
  set Mn : ℕ := rankOneModulusNat D' B₂ k t₀ with hMn
  have hM0 : Mn ≠ 0 := by
    rw [hMn]; unfold rankOneModulusNat
    have h1 : (max 1 |D'|).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |D'|; omega)
    have h2 : B₂.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hB₂.ne'
    have h3 : (2 * k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero two_ne_zero hk)
    have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    positivity
  have hMpos : 0 < Mn := Nat.pos_of_ne_zero hM0
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  have hMdvd : (Mn : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by have := hp.one_lt; omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by have := hp.one_lt; omega), Nat.cast_one] at h'
  have hMcast : (Mn : ℤ) = 8 * abs (max 1 (abs D')) * |B₂| * |2 * k| * |t₀| := by
    rw [hMn]; unfold rankOneModulusNat; push_cast; ring
  have hB₂dvd : B₂ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast, abs_of_pos hB₂]; exact ⟨8 * abs (max 1 (abs D')) * |2 * k| * |t₀|, by ring⟩
  have h2kdvd : 2 * k ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs (2 * k)).trans ⟨8 * abs (max 1 (abs D')) * |B₂| * |t₀|, by ring⟩
  have ht₀dvd : t₀ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs t₀).trans ⟨8 * abs (max 1 (abs D')) * |B₂| * |2 * k|, by ring⟩
  have h2dvd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨4 * abs (max 1 (abs D')) * |B₂| * |2 * k| * |t₀|, by ring⟩
  have notdvd : ∀ x : ℤ, x ∣ (p : ℤ) - 1 → ¬ (p : ℤ) ∣ x := by
    intro x hx hc
    have := dvd_trans hc hx
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have := hp.one_lt; omega
  have hp2k : ¬ (p : ℤ) ∣ 2 * k := notdvd _ h2kdvd
  have hpB₂ : ¬ (p : ℤ) ∣ B₂ := notdvd _ hB₂dvd
  have hpt₀ : ¬ (p : ℤ) ∣ t₀ := notdvd _ ht₀dvd
  have hp2 : p ≠ 2 := by
    intro h; apply notdvd 2 h2dvd; rw [h]; norm_num
  have hD'dvd : D' ≠ 0 → (8 * D'.natAbs : ℕ) ∣ Mn := by
    intro hne
    rw [hMn]; unfold rankOneModulusNat
    rw [show (max 1 |D'|).natAbs = D'.natAbs by rw [max_eq_right (Int.one_le_abs hne), Int.natAbs_abs]]
    exact ⟨B₂.natAbs * (2 * k).natAbs * t₀.natAbs, by ring⟩
  have hsqD : D' ≠ 0 → IsSquare ((D' : ℤ) : ZMod p) := fun hne =>
    square_mod_prime_of_one_mod_eight_abs p hp D' hne (Nat.ModEq.of_dvd (hD'dvd hne) hpmod)
  have hpD : D' ≠ 0 → ¬ (p : ℤ) ∣ D' := by
    intro hne
    apply notdvd
    refine dvd_trans ?_ hMdvd
    rw [hMcast, show abs (max 1 (abs D')) = |D'| by rw [max_eq_right (Int.one_le_abs hne), abs_abs]]
    exact (self_dvd_abs D').trans ⟨8 * |B₂| * |2 * k| * |t₀|, by ring⟩
  -- the ray c_E, E = e + 1
  have hpow : ∀ E : ℕ, B₂ ∣ (p : ℤ) ^ E - 1 := fun E =>
    hB₂dvd.trans (by simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 E)
  set g : ℕ → ℤ := fun e => (c₀ : ℤ) + t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂) with hg
  have hmod : ∀ e, B₂ * g e + m₂ = t₀ * (p : ℤ) ^ (e + 1) := by
    intro e
    obtain ⟨j, hj⟩ := hpow (e + 1)
    have : ((p : ℤ) ^ (e + 1) - 1) / B₂ = j := by rw [hj]; exact Int.mul_ediv_cancel_left j hB₂.ne'
    simp only [hg]; rw [this]; linear_combination (-t₀) * hj - ht₀def
  have hpR : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hp2R : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hjpos : ∀ e, 0 ≤ ((p : ℤ) ^ (e + 1) - 1) / B₂ := fun e =>
    Int.ediv_nonneg (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith) hB₂.le
  have hgnn : ∀ e, 0 ≤ g e := fun e => by
    rw [hg]; have := hjpos e; positivity
  refine ⟨((|(c₀ : ℤ)| + t₀) * p).toNat, p, g, ?_, hp.two_le, ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ (|(c₀ : ℤ)| + t₀) * p := by nlinarith [abs_nonneg (c₀ : ℤ)]
    have h' : (1 : ℤ) ≤ ((|(c₀ : ℤ)| + t₀) * p).toNat := by
      rw [Int.toNat_of_nonneg (by linarith)]; exact this
    exact_mod_cast h'
  · -- injective: B₂ g e + m₂ = t₀ p^(e+1) is strictly monotone in e
    intro e e' h
    have h1 := hmod e; have h2 := hmod e'
    rw [h] at h1
    have : (p : ℤ) ^ (e + 1) = (p : ℤ) ^ (e' + 1) := by
      have := h1.symm.trans h2; exact mul_left_cancel₀ ht₀.ne' this
    have := pow_right_injective₀ (by positivity) (ne_of_gt hpR) this
    omega
  · -- membership in castSet (fiberSet2 …)
    intro e
    have hE : 1 ≤ e + 1 := by omega
    have hpt : (p : ℤ) ^ (e + 1) ∣ B₂ * g e + m₂ := by rw [hmod e]; exact dvd_mul_left _ _
    obtain ⟨uN, huN⟩ := rankOne_root_pow A B₁ B₂ k l m₁ m₂ q p hp hp2 hp2k hpB₂ hsqD hpD (e + 1) hE (g e) hpt
    have hcop : IsCoprime t₀ ((p : ℤ) ^ (e + 1)) :=
      ((isCoprime_prime_of_not_dvd p hp t₀ hpt₀).pow_left).symm
    obtain ⟨u, hu⟩ := rankOne_combine A B₁ k l m₁ q (c₀ : ℤ) u₀ (g e) uN t₀ ((p : ℤ) ^ (e + 1))
      (((p : ℤ) ^ (e + 1) - 1) / B₂) rfl hdiv hcop huN
    refine ⟨(g e).toNat, ?_, Int.toNat_of_nonneg (hgnn e)⟩
    apply mem_fiberSet2_of_dvd A B₁ B₂ k l m₁ m₂ q (g e).toNat u
    rw [Int.toNat_of_nonneg (hgnn e), hmod e]; exact hu
  · -- envelope: |g e| ≤ (|c₀| + t₀) p · p^e
    intro e
    have hj := hjpos e
    have hjle : ((p : ℤ) ^ (e + 1) - 1) / B₂ ≤ (p : ℤ) ^ (e + 1) := by
      have h1 : ((p : ℤ) ^ (e + 1) - 1) / B₂ ≤ (p : ℤ) ^ (e + 1) - 1 :=
        Int.ediv_le_self _ (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith)
      linarith
    have hpe : (1 : ℤ) ≤ (p : ℤ) ^ (e + 1) := one_le_pow₀ hpR.le
    have hA : (((|(c₀ : ℤ)| + t₀) * p).toNat : ℤ) = (|(c₀ : ℤ)| + t₀) * p :=
      Int.toNat_of_nonneg (by positivity)
    rw [hA]
    have hge : |g e| ≤ |(c₀ : ℤ)| + t₀ * (p : ℤ) ^ (e + 1) := by
      calc |g e| = |(c₀ : ℤ) + t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂)| := rfl
        _ ≤ |(c₀ : ℤ)| + |t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂)| := abs_add_le _ _
        _ = |(c₀ : ℤ)| + t₀ * (((p : ℤ) ^ (e + 1) - 1) / B₂) := by
            rw [abs_of_nonneg (mul_nonneg ht₀.le hj)]
        _ ≤ |(c₀ : ℤ)| + t₀ * (p : ℤ) ^ (e + 1) := by nlinarith
    calc |g e| ≤ |(c₀ : ℤ)| + t₀ * (p : ℤ) ^ (e + 1) := hge
      _ ≤ (|(c₀ : ℤ)| + t₀) * (p : ℤ) ^ (e + 1) := by nlinarith [abs_nonneg (c₀ : ℤ)]
      _ = (|(c₀ : ℤ)| + t₀) * p * (p : ℤ) ^ e := by ring

end DiophCompression.ResearchUpgrade
