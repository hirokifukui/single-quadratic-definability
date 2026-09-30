/-
  TCERBridge.lean — s56.  GPT R44 Packets B and C2 (GATE26): the ternary coset eventual-representation
  interface and the two-coset collision route in polar rank ≥ 3.

  * `TernaryCosetEventualRepresentation` (TCER) — a Prop, NOT proved here and NOT an axiom: it appears as an
    explicit hypothesis of `ternaryCosetCollision_of_TCER` and nowhere else.  The local condition is PRIMITIVE
    representability (`LocalPrimRep`), which is STRONGER than the ordinary local representability of the source:
    Kane–Kim (Selecta Math. 32, 2026, art. 5), consequence stated on p. 5 of the published version (built from the
    splitting Thm 1.2, the square-class support Thm 5.6, Shimura's Siegel–Weil formula for cosets and Duke's bound).
    The consequence applies after forgetting primitivity (s57, GATE27 #89; C1_TCER_CROSSWALK_s57).
  * `twoVisibleCosets` (B2) — two residue cosets of `e₁ + dℤ³` modulo a new prime `ℓ` representing `QS e₁` mod `ℓ`
    with different values of a given functional.
  * `localProgression` (B3) — one input progression on which the target is locally primitively represented by
    both cosets at EVERY prime and to every precision, with prescribed valuations at a finite bad set.  Three
    prime cases: primes of `2·d·det S` (CRT approach to `e₁`, then Hensel), `ℓ` (a common factor, a unit linear
    coefficient, Hensel), all others (Chevalley–Warning isotropic vector, then Hensel).
  * `squareClassEscapeProgression` (B4) — a residue class mod `q²` on which the quadratic has `q`-valuation 1,
    hence avoids every exceptional square class.
  * `ternaryCosetCollision_of_TCER` (C2) — TCER ⇒ two representations of one target value in the coset with
    different functional values.  Only the single represented value `QS e₁` is used, not totality.

  Statements frozen before installation (`~/lean/s56_evidence/freeze/B_FREEZE_s56.lean`, rulings R4/R5,
  Dr. Fukui 2026-09-25); frozen = installed by `#check`/`#print` output, planted control caught.
  Not here: B1 `fixedCoset_slice` (the return map from a datum; truth check pending) and the capstones C3/C4.

  Claim tags: [P] (std-3) for every theorem; TCER itself is [C] (conditional input, never discharged).
-/
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace TCERBridge

/-- The integer ternary form of a Gram matrix. -/
def QS (S : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) : ℤ := y ⬝ᵥ (S *ᵥ y)

/-- The base point `e₁` (a basis vector: primitive). -/
def e1 : Fin 3 → ℤ := Pi.single 0 1

/-- `N` is PRIMITIVELY represented by the coset `ρ + d ℤ³` at every finite prime, to every precision. -/
def LocalPrimRep (S : Matrix (Fin 3) (Fin 3) ℤ) (d : ℕ) (ρ : Fin 3 → ℤ) (N : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, ∃ x : Fin 3 → ℤ,
    ((p : ℤ) ^ e ∣ QS S (ρ + (d : ℤ) • x) - N) ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + (d : ℤ) • x) i

/-- **TCER** (R4): for a fixed positive definite integral ternary coset there are finitely many bad primes and
finitely many exceptional square classes; for every bound on the bad valuations, every sufficiently large integer
that is locally primitively represented, has those bounded valuations and lies in no exceptional class, is
represented by an actual point of the coset.  (Kane–Kim, Selecta Math. 32 (2026) art. 5, published version p. 5;
`LocalPrimRep` is stronger than the local condition there.)  NOT proved here; an explicit parameter. -/
def TernaryCosetEventualRepresentation : Prop :=
  ∀ (S : Matrix (Fin 3) (Fin 3) ℤ) (d : ℕ) (ρ : Fin 3 → ℤ),
    S.IsSymm → (∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) → 0 < d →
    ∃ (bad : Finset ℕ) (E : Finset ℕ), (∀ p ∈ bad, p.Prime) ∧ (∀ e ∈ E, 0 < e) ∧
      ∀ b : ℕ → ℕ, ∃ N₀ : ℤ, ∀ N : ℤ, N₀ ≤ N → LocalPrimRep S d ρ N →
        (∀ p ∈ bad, ¬ (p : ℤ) ^ (b p + 1) ∣ N) →
        (∀ e ∈ E, ¬ ∃ q : ℚ, (N : ℚ) = (e : ℚ) * q ^ 2) →
        ∃ x : Fin 3 → ℤ, QS S (ρ + (d : ℤ) • x) = N

/-! ### B2 helpers -/

def BS (S : Matrix (Fin 3) (Fin 3) ℤ) (x y : Fin 3 → ℤ) : ℤ := x ⬝ᵥ (S *ᵥ y)

theorem QS_sub_smul (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm) (x y : Fin 3 → ℤ) (c : ℤ) :
    QS S (x - c • y) = QS S x - 2 * c * BS S x y + c ^ 2 * QS S y := by
  have h01 : S 1 0 = S 0 1 := by rw [← hS.apply 0 1]
  have h02 : S 2 0 = S 0 2 := by rw [← hS.apply 0 2]
  have h12 : S 2 1 = S 1 2 := by rw [← hS.apply 1 2]
  simp only [QS, BS, dotProduct, mulVec, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h01, h02, h12]
  ring

theorem BS_e1 (S : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) :
    BS S e1 y = S 0 0 * y 0 + S 0 1 * y 1 + S 0 2 * y 2 := by
  simp [BS, e1, dotProduct, mulVec, Fin.sum_univ_three, Pi.single_apply]

theorem QS_e1 (S : Matrix (Fin 3) (Fin 3) ℤ) : QS S e1 = S 0 0 := by
  simp [QS, e1, dotProduct, mulVec, Fin.sum_univ_three, Pi.single_apply]

/-- **B2.**  Two residue cosets of the fixed coset `e₁ + dℤ³`, modulo a new prime `ℓ`, both representing `QS e₁`
modulo `ℓ` and with different output residues.  (Rational reflection in a vector `w` with `p·w ≠ 0 ≠ B(e₁, w)`,
reduced modulo a prime avoiding every denominator.) -/
theorem twoVisibleCosets (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) (d : ℕ) (hd : 0 < d)
    (p : Fin 3 → ℤ) (hp : p ≠ 0) :
    ∃ (ℓ : ℕ) (ρ₁ ρ₂ : Fin 3 → ℤ), ℓ.Prime ∧
      ¬ ℓ ∣ 2 * d * S.det.natAbs * (QS S e1).natAbs ∧
      (∀ i, ρ₁ i ≡ e1 i [ZMOD d]) ∧ (∀ i, ρ₂ i ≡ e1 i [ZMOD d]) ∧
      (∀ i, ρ₁ i ≡ e1 i [ZMOD ℓ]) ∧ QS S ρ₂ ≡ QS S e1 [ZMOD ℓ] ∧
      ¬ (p ⬝ᵥ ρ₁ ≡ p ⬝ᵥ ρ₂ [ZMOD ℓ]) := by
  classical
  have hN0 : 0 < QS S e1 := hpos e1 (by
    intro h; have := congrFun h 0; simp [e1] at this)
  -- a vector w with p·w ≠ 0 and B(e1, w) ≠ 0
  obtain ⟨w, hpw, hbw⟩ : ∃ w : Fin 3 → ℤ, p ⬝ᵥ w ≠ 0 ∧ BS S e1 w ≠ 0 := by
    have hS00 : 0 < S 0 0 := by rw [← QS_e1 S]; exact hN0
    by_cases h0 : p ⬝ᵥ e1 ≠ 0
    · refine ⟨e1, h0, ?_⟩
      rw [BS_e1]; simp [e1, Pi.single_apply]; omega
    · push_neg at h0
      have hp0 : p 0 = 0 := by simpa [e1, dotProduct, Fin.sum_univ_three, Pi.single_apply] using h0
      obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
        by_contra H; push_neg at H; exact hp (funext H)
      have hj0 : j ≠ 0 := by rintro rfl; exact hj hp0
      set ej : Fin 3 → ℤ := Pi.single j 1
      have hpej : p ⬝ᵥ ej = p j := by simp [ej, dotProduct, Pi.single_apply]
      by_cases hb : BS S e1 ej ≠ 0
      · exact ⟨ej, by rw [hpej]; exact hj, hb⟩
      · push_neg at hb
        refine ⟨e1 + ej, ?_, ?_⟩
        · rw [dotProduct_add, h0, hpej]; simpa using hj
        · have : BS S e1 (e1 + ej) = BS S e1 e1 + BS S e1 ej := by
            simp [BS, mulVec_add, dotProduct_add]
          rw [this, hb, BS_e1]; simp [e1, Pi.single_apply]; omega
  have hw0 : w ≠ 0 := by rintro rfl; simp at hpw
  have hQw : 0 < QS S w := hpos w hw0
  set β := BS S e1 w
  -- a prime ℓ larger than every quantity to be avoided
  set K : ℕ := 2 * d * S.det.natAbs * (QS S e1).natAbs * (QS S w).natAbs * (2 * β * (p ⬝ᵥ w)).natAbs
  obtain ⟨ℓ, hℓK, hℓ⟩ := Nat.exists_infinite_primes (K + 1)
  have hK0 : 0 < K := by
    have h1 : 0 < S.det.natAbs := by
      apply Int.natAbs_pos.mpr
      intro hdet
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
      have := hpos v hv0
      simp [QS, hv] at this
    have h2 : 0 < (QS S e1).natAbs := Int.natAbs_pos.mpr hN0.ne'
    have h3 : 0 < (QS S w).natAbs := Int.natAbs_pos.mpr hQw.ne'
    have h4 : 0 < (2 * β * (p ⬝ᵥ w)).natAbs := Int.natAbs_pos.mpr (by
      apply mul_ne_zero (mul_ne_zero (by norm_num) hbw) hpw)
    positivity
  have hnd : ∀ x : ℕ, x ∣ K → ¬ ℓ ∣ x := by
    intro x hx hℓx
    have := Nat.le_of_dvd hK0 (dvd_trans hℓx hx)
    omega
  have hℓ_main : ¬ ℓ ∣ 2 * d * S.det.natAbs * (QS S e1).natAbs :=
    hnd _ ⟨(QS S w).natAbs * (2 * β * (p ⬝ᵥ w)).natAbs, by ring⟩
  have hℓd : ¬ ℓ ∣ d := hnd _ ⟨2 * S.det.natAbs * (QS S e1).natAbs * (QS S w).natAbs * (2 * β * (p ⬝ᵥ w)).natAbs, by ring⟩
  have hℓQw : ¬ (ℓ : ℤ) ∣ QS S w := by
    intro h; apply hnd ((QS S w).natAbs) ⟨2 * d * S.det.natAbs * (QS S e1).natAbs * (2 * β * (p ⬝ᵥ w)).natAbs, by ring⟩
    exact Int.natCast_dvd.mp h
  have hℓ2βp : ¬ (ℓ : ℤ) ∣ 2 * β * (p ⬝ᵥ w) := by
    intro h; apply hnd ((2 * β * (p ⬝ᵥ w)).natAbs) ⟨2 * d * S.det.natAbs * (QS S e1).natAbs * (QS S w).natAbs, by ring⟩
    exact Int.natCast_dvd.mp h
  -- scalar c' ≡ 0 (mod d) with c' · Q(w) ≡ 2β (mod ℓ), built in the field ZMod ℓ
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hz : ∀ x : ℤ, ¬ (ℓ : ℤ) ∣ x → (x : ZMod ℓ) ≠ 0 := fun x hx h =>
    hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x ℓ).mp h)
  have ha : ((QS S w : ℤ) : ZMod ℓ) ≠ 0 := hz _ hℓQw
  have hdq : ((d : ℤ) : ZMod ℓ) ≠ 0 := hz _ (by intro h; exact hℓd (Int.natCast_dvd_natCast.mp h))
  have h2β : ((2 * β : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h; apply hℓ2βp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp (by push_cast at h ⊢; rw [h]; ring)
  have hpwz : ((p ⬝ᵥ w : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h; apply hℓ2βp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp (by push_cast at h ⊢; rw [h]; ring)
  set cbar : ZMod ℓ := ((2 * β : ℤ) : ZMod ℓ) / ((QS S w : ℤ) : ZMod ℓ)
  set u : ℤ := ((cbar / ((d : ℤ) : ZMod ℓ)).val : ℤ)
  set c' : ℤ := (d : ℤ) * u
  have hc'z : ((c' : ℤ) : ZMod ℓ) = cbar := by
    have hdq' : ((d : ℕ) : ZMod ℓ) ≠ 0 := by exact_mod_cast hdq
    simp only [c', u]; push_cast
    rw [ZMod.natCast_zmod_val]
    exact mul_div_cancel₀ cbar hdq'
  have hkey : ((c' * QS S w : ℤ) : ZMod ℓ) = ((2 * β : ℤ) : ZMod ℓ) := by
    rw [Int.cast_mul, hc'z]; exact div_mul_cancel₀ _ ha
  refine ⟨ℓ, e1, e1 - c' • w, hℓ, hℓ_main, fun i => Int.ModEq.refl _, fun i => ?_, fun i => Int.ModEq.refl _, ?_, ?_⟩
  · -- ρ₂ ≡ e1 (mod d)
    show (e1 - c' • w) i ≡ e1 i [ZMOD d]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Int.ModEq.symm
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-(u * w i), by simp only [c']; ring⟩
  · -- QS ρ₂ ≡ QS e1 (mod ℓ)
    rw [QS_sub_smul S hS]
    apply (ZMod.intCast_eq_intCast_iff _ _ ℓ).mp
    have : ((QS S e1 - 2 * c' * BS S e1 w + c' ^ 2 * QS S w : ℤ) : ZMod ℓ)
        = ((QS S e1 : ℤ) : ZMod ℓ) - ((c' : ℤ) : ZMod ℓ) * (((2 * β : ℤ) : ZMod ℓ) - ((c' * QS S w : ℤ) : ZMod ℓ)) := by
      push_cast; ring
    rw [this, hkey, sub_self, mul_zero, sub_zero]
  · -- different output residues
    intro h
    have h' := (ZMod.intCast_eq_intCast_iff _ _ ℓ).mpr h
    have e : ((p ⬝ᵥ e1 : ℤ) : ZMod ℓ) - ((p ⬝ᵥ (e1 - c' • w) : ℤ) : ZMod ℓ)
        = ((c' : ℤ) : ZMod ℓ) * ((p ⬝ᵥ w : ℤ) : ZMod ℓ) := by
      rw [dotProduct_sub, dotProduct_smul]; push_cast; simp [smul_eq_mul]
    rw [h', sub_self] at e
    have hc0 : ((c' : ℤ) : ZMod ℓ) ≠ 0 := by
      rw [hc'z]; simp only [cbar]; exact div_ne_zero h2β ha
    exact (mul_ne_zero hc0 hpwz) e.symm

/-! ### B4 helpers -/

theorem b4_valInt_one {q : ℕ} [hq : Fact q.Prime] {x : ℤ} (h1 : (q : ℤ) ∣ x) (h2 : ¬ (q : ℤ) ^ 2 ∣ x) :
    x ≠ 0 ∧ padicValInt q x = 1 := by
  have hx : x ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  refine ⟨hx, ?_⟩
  have hge : 1 ≤ padicValInt q x := by
    have := (padicValInt_dvd_iff (p := q) 1 x).mp (by simpa using h1)
    rcases this with h | h
    · exact absurd h hx
    · exact h
  have hlt : ¬ 2 ≤ padicValInt q x := by
    intro h; exact h2 ((padicValInt_dvd_iff (p := q) 2 x).mpr (Or.inr h))
  omega

theorem b4_not_squareClass {q : ℕ} [hq : Fact q.Prime] {x : ℤ} (hx : x ≠ 0) (hv : padicValInt q x = 1)
    (e : ℕ) (he : 0 < e) (hqe : ¬ q ∣ e) : ¬ ∃ s : ℚ, (x : ℚ) = (e : ℚ) * s ^ 2 := by
  rintro ⟨s, hs⟩
  have hs0 : s ≠ 0 := by
    rintro rfl; apply hx; exact_mod_cast (by simpa using hs : (x : ℚ) = 0)
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  have h1 : padicValRat q (x : ℚ) = 1 := by rw [padicValRat.of_int, hv]; rfl
  have h2 : padicValRat q ((e : ℚ) * s ^ 2) = padicValRat q (e : ℚ) + 2 * padicValRat q s := by
    rw [padicValRat.mul he0 (pow_ne_zero 2 hs0), padicValRat.pow hs0]
    push_cast; ring
  have h3 : padicValRat q (e : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd hqe]
  rw [hs, h2, h3] at h1
  omega

/-- **B4** (as drafted in `B4_DRAFT_s56.lean`). -/
theorem squareClassEscapeProgression (A B c : ℤ) (hA : 0 < A) (hc : 0 < c)
    (hdisc : B ^ 2 - 4 * A * c ≠ 0) (forbid : ℕ) (hforbid : 0 < forbid)
    (E : Finset ℕ) (hE : ∀ e ∈ E, 0 < e) :
    ∃ (q : ℕ) (k1 : ℤ), q.Prime ∧ ¬ q ∣ forbid ∧
      ¬ q ∣ 2 * A.natAbs * (B ^ 2 - 4 * A * c).natAbs ∧ (∀ e ∈ E, ¬ q ∣ e) ∧
      ∀ k : ℤ, k ≡ k1 [ZMOD (q : ℤ) ^ 2] →
        A * k ^ 2 + B * k + c ≠ 0 ∧ padicValInt q (A * k ^ 2 + B * k + c) = 1 ∧
        ∀ e ∈ E, ¬ ∃ s : ℚ, ((A * k ^ 2 + B * k + c : ℤ) : ℚ) = (e : ℚ) * s ^ 2 := by
  classical
  set Δ : ℤ := B ^ 2 - 4 * A * c with hΔ
  set PE : ℕ := ∏ e ∈ E, e with hPE
  have hPE0 : 0 < PE := Finset.prod_pos fun e he => hE e he
  set P : ℕ := 2 * A.natAbs * Δ.natAbs * forbid * PE with hP
  have hP0 : 0 < P := by
    have : 0 < A.natAbs := Int.natAbs_pos.mpr hA.ne'
    have : 0 < Δ.natAbs := Int.natAbs_pos.mpr hdisc
    positivity
  set T : ℤ := |B| + 1 with hT
  have hT1 : 1 ≤ T := by have := abs_nonneg B; omega
  set H : ℤ := 1 + B * P * T + A * c * P ^ 2 * T ^ 2 with hH
  have hPz : (1 : ℤ) ≤ P := by exact_mod_cast hP0
  have hH2 : 2 ≤ H := by
    have hAc : 1 ≤ A * c := by nlinarith
    have hPT : 1 ≤ (P : ℤ) * T := by nlinarith
    have hB : -(|B|) ≤ B := neg_abs_le B
    have key : (P : ℤ) * T * (A * c * P * T + B) ≥ (P : ℤ) * T * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : A * c * P * T ≥ (P : ℤ) * T := by nlinarith
      nlinarith
    nlinarith
  set q : ℕ := H.natAbs.minFac with hq
  have hH1 : H.natAbs ≠ 1 := by omega
  have hqp : q.Prime := Nat.minFac_prime hH1
  haveI : Fact q.Prime := ⟨hqp⟩
  have hqH : (q : ℤ) ∣ H := by
    have := Nat.minFac_dvd H.natAbs
    exact Int.natCast_dvd.mpr this
  have hqP : ¬ q ∣ P := by
    intro hdv
    have h1 : (q : ℤ) ∣ H - 1 := by
      have : H - 1 = (P : ℤ) * (B * T + A * c * P * T ^ 2) := by rw [hH]; ring
      rw [this]; exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hdv) _
    have : (q : ℤ) ∣ 1 := by
      have := (Int.dvd_sub hqH h1); simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) this
    have : q = 1 := by exact_mod_cast this
    exact hqp.one_lt.ne' this
  have hdvP : ∀ x : ℕ, x ∣ P → ¬ q ∣ x := fun x hx hqx => hqP (dvd_trans hqx hx)
  have hq_forbid : ¬ q ∣ forbid := hdvP _ ⟨2 * A.natAbs * Δ.natAbs * PE, by rw [hP]; ring⟩
  have hq_2AΔ : ¬ q ∣ 2 * A.natAbs * Δ.natAbs := hdvP _ ⟨forbid * PE, by rw [hP]; ring⟩
  have hq_E : ∀ e ∈ E, ¬ q ∣ e := by
    intro e he
    apply hdvP
    have : e ∣ PE := Finset.dvd_prod_of_mem _ he
    exact dvd_trans this ⟨2 * A.natAbs * Δ.natAbs * forbid, by rw [hP]; ring⟩
  have hqΔ : ¬ (q : ℤ) ∣ Δ := by
    intro h
    apply hq_2AΔ
    have : q ∣ Δ.natAbs := Int.natCast_dvd.mp h
    exact Dvd.dvd.mul_left this _
  -- the root k0 = c P T
  set F : ℤ → ℤ := fun k => A * k ^ 2 + B * k + c with hF
  set k0 : ℤ := c * P * T with hk0
  have hFk0 : F k0 = c * H := by simp only [hF, hk0, hH]; ring
  have hqF0 : (q : ℤ) ∣ F k0 := by rw [hFk0]; exact Dvd.dvd.mul_left hqH c
  have hderiv : ∀ k, (2 * A * k + B) ^ 2 = Δ + 4 * A * F k := by intro k; simp only [hF, hΔ]; ring
  have hqF' : ¬ (q : ℤ) ∣ 2 * A * k0 + B := by
    intro h
    have h2 : (q : ℤ) ∣ (2 * A * k0 + B) ^ 2 := Dvd.dvd.mul_left h _ |>.trans (by rw [pow_two])
    rw [hderiv] at h2
    have : (q : ℤ) ∣ 4 * A * F k0 := Dvd.dvd.mul_left hqF0 _
    exact hqΔ (by simpa using Int.dvd_sub h2 this)
  -- choose k1 with v_q(F k1) = 1
  obtain ⟨k1, hk1a, hk1b⟩ : ∃ k1 : ℤ, (q : ℤ) ∣ F k1 ∧ ¬ (q : ℤ) ^ 2 ∣ F k1 := by
    by_cases h : (q : ℤ) ^ 2 ∣ F k0
    · refine ⟨k0 + q, ?_, ?_⟩
      · have : F (k0 + q) = F k0 + q * (2 * A * k0 + B + A * q) := by simp only [hF]; ring
        rw [this]; exact dvd_add hqF0 (Dvd.intro _ rfl)
      · intro h'
        have e1 : F (k0 + q) = F k0 + q * (2 * A * k0 + B) + q ^ 2 * A := by simp only [hF]; ring
        rw [e1] at h'
        have : (q : ℤ) ^ 2 ∣ q * (2 * A * k0 + B) := by
          have := Int.dvd_sub (Int.dvd_sub h' h) (Dvd.intro A rfl)
          have e2 : F k0 + (q : ℤ) * (2 * A * k0 + B) + (q : ℤ) ^ 2 * A - F k0 - (q : ℤ) ^ 2 * A
              = (q : ℤ) * (2 * A * k0 + B) := by ring
          rwa [e2] at this
        rw [pow_two] at this
        have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqp.ne_zero
        exact hqF' ((mul_dvd_mul_iff_left hq0).mp this)
    · exact ⟨k0, hqF0, h⟩
  refine ⟨q, k1, hqp, hq_forbid, hq_2AΔ, hq_E, fun k hk => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, k = k1 + (q : ℤ) ^ 2 * j := by
    obtain ⟨j, hj⟩ := (Int.ModEq.dvd hk.symm)
    exact ⟨j, by linarith⟩
  have hFk : F k = F k1 + (q : ℤ) ^ 2 * (j * (2 * A * k1 + B + A * (q : ℤ) ^ 2 * j)) := by
    rw [hj]; simp only [hF]; ring
  have h1 : (q : ℤ) ∣ F k := by
    rw [hFk]; exact dvd_add hk1a (Dvd.dvd.mul_right (dvd_pow_self _ (by norm_num)) _)
  have h2 : ¬ (q : ℤ) ^ 2 ∣ F k := by
    intro h; apply hk1b
    have := Int.dvd_sub h (Dvd.intro _ rfl : (q : ℤ) ^ 2 ∣ (q : ℤ) ^ 2 * (j * (2 * A * k1 + B + A * (q : ℤ) ^ 2 * j)))
    rw [hFk] at this; simpa using this
  obtain ⟨hne, hv⟩ := b4_valInt_one h1 h2
  exact ⟨hne, hv, fun e he => b4_not_squareClass hne hv e (hE e he) (hq_E e he)⟩

/-! ### B3 engine: Hensel, Chevalley–Warning, the three prime cases -/

/-- Hensel step engine at the origin: `b = pᵍ u`, `p ∤ u`, `p^(2g+1) ∣ c`. -/
theorem b3_hensel0 {p : ℕ} (hp : p.Prime) (a b c u : ℤ) (g : ℕ)
    (hb : b = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u) (hc : (p : ℤ) ^ (2 * g + 1) ∣ c) :
    ∀ e : ℕ, ∃ τ : ℤ, (p : ℤ) ^ (e + (2 * g + 1)) ∣
      a * ((p : ℤ) ^ (g + 1) * τ) ^ 2 + b * ((p : ℤ) ^ (g + 1) * τ) + c := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (p : ℤ) u := (hpz.irreducible.coprime_iff_not_dvd).mpr hu
  obtain ⟨α, β, hαβ⟩ := hcop
  intro e
  induction e with
  | zero => exact ⟨0, by simpa using hc⟩
  | succ e ih =>
    obtain ⟨τ, r, hr⟩ := ih
    refine ⟨τ + (p : ℤ) ^ e * (-r * β),
      r * α + 2 * a * τ * (-r * β) + a * (p : ℤ) ^ e * (-r * β) ^ 2, ?_⟩
    linear_combination hr + ((p : ℤ) ^ (g + 1) * (p : ℤ) ^ e * (-r * β)) * hb
      + (-(p : ℤ) ^ (e + (2 * g + 1)) * r) * hαβ

/-- Hensel from an arbitrary starting point `t₀`. -/
theorem b3_hensel {p : ℕ} (hp : p.Prime) (a b c t0 u : ℤ) (g : ℕ)
    (hF0 : (p : ℤ) ^ (2 * g + 1) ∣ a * t0 ^ 2 + b * t0 + c)
    (hb : b + 2 * a * t0 = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u) :
    ∀ e : ℕ, ∃ τ : ℤ, (p : ℤ) ^ (e + (2 * g + 1)) ∣
      a * (t0 + (p : ℤ) ^ (g + 1) * τ) ^ 2 + b * (t0 + (p : ℤ) ^ (g + 1) * τ) + c := by
  intro e
  obtain ⟨τ, hτ⟩ := b3_hensel0 hp a (b + 2 * a * t0) (a * t0 ^ 2 + b * t0 + c) u g hb hu hF0 e
  refine ⟨τ, ?_⟩
  have : a * (t0 + (p : ℤ) ^ (g + 1) * τ) ^ 2 + b * (t0 + (p : ℤ) ^ (g + 1) * τ) + c
      = a * ((p : ℤ) ^ (g + 1) * τ) ^ 2 + (b + 2 * a * t0) * ((p : ℤ) ^ (g + 1) * τ)
        + (a * t0 ^ 2 + b * t0 + c) := by ring
  rw [this]; exact hτ

theorem b3_QS_add_smul (S : Matrix (Fin 3) (Fin 3) ℤ) (y z : Fin 3 → ℤ) (t : ℤ) :
    QS S (y + t • z) = QS S y + t * (y ⬝ᵥ (S *ᵥ z) + z ⬝ᵥ (S *ᵥ y)) + t ^ 2 * QS S z := by
  simp only [QS, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

theorem b3_QS_smul (S : Matrix (Fin 3) (Fin 3) ℤ) (z : Fin 3 → ℤ) (t : ℤ) :
    QS S (t • z) = t ^ 2 * QS S z := by
  simp only [QS, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- The polar coefficient along a basis direction, for symmetric `S`. -/
theorem b3_polar_single (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm) (y : Fin 3 → ℤ) (i : Fin 3) :
    y ⬝ᵥ (S *ᵥ Pi.single i 1) + Pi.single i 1 ⬝ᵥ (S *ᵥ y) = 2 * (S *ᵥ y) i := by
  have hsym : ∀ a b, S b a = S a b := fun a b => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hS a) b
  have h1 : y ⬝ᵥ (S *ᵥ Pi.single i 1) = (S *ᵥ y) i := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hsym i j]; ring
  have h2 : Pi.single i 1 ⬝ᵥ (S *ᵥ y) = (S *ᵥ y) i := by
    simp [single_dotProduct]
  rw [h1, h2]; ring

/-- Positive definite ⇒ non-singular. -/
theorem b3_det_ne_zero (S : Matrix (Fin 3) (Fin 3) ℤ)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) : S.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hSv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have := hpos v hv
  simp [QS, hSv] at this

/-- Modulo a prime not dividing `det S`, a vector not divisible by `p` has `S y` not divisible by `p`. -/
theorem b3_coord_not_dvd {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : ¬ (p : ℤ) ∣ S.det) (y : Fin 3 → ℤ) (hy : ¬ ∀ i, (p : ℤ) ∣ y i) :
    ∃ i, ¬ (p : ℤ) ∣ (S *ᵥ y) i := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra h
  push_neg at h
  set f : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hzero : (S.map f) *ᵥ (f ∘ y) = 0 := by
    funext i
    rw [← RingHom.map_mulVec]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h i)
  have hne : (f ∘ y) ≠ 0 := by
    intro h0
    apply hy
    intro i
    have := congrFun h0 i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have hdet0 : (S.map f).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hzero⟩
  apply hdet
  have : f S.det = 0 := by rw [RingHom.map_det]; exact hdet0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

/-- Chevalley–Warning: an isotropic vector modulo `p`, not divisible by `p`. -/
theorem b3_isotropic {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) :
    ∃ x : Fin 3 → ℤ, (¬ ∀ i, (p : ℤ) ∣ x i) ∧ (p : ℤ) ∣ QS S x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let f : MvPolynomial (Fin 3) (ZMod p) :=
    ∑ i, ∑ j, MvPolynomial.C ((S i j : ℤ) : ZMod p) * MvPolynomial.X i * MvPolynomial.X j
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      have h1 := MvPolynomial.totalDegree_mul
        (MvPolynomial.C ((S i j : ℤ) : ZMod p) * MvPolynomial.X i) (MvPolynomial.X j)
      have h2 := MvPolynomial.totalDegree_mul
        (MvPolynomial.C ((S i j : ℤ) : ZMod p)) (MvPolynomial.X (R := ZMod p) i)
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X] at h1 h2
      omega
    simp only [Fintype.card_fin]; omega
  have hdvd := char_dvd_card_solutions (K := ZMod p) p hdeg
  have hex : ∃ x : Fin 3 → ZMod p, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
    by_contra hcon
    push_neg at hcon
    have hu : Unique { x : Fin 3 → ZMod p // MvPolynomial.eval x f = 0 } :=
      { default := ⟨0, by simp [f]⟩
        uniq := fun a => Subtype.ext (by
          by_contra hne
          exact hcon a.1 hne a.2) }
    rw [Fintype.card_unique] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  obtain ⟨x, hx0, hx⟩ := hex
  refine ⟨fun i => ((x i).val : ℤ), ?_, ?_⟩
  · intro hall
    apply hx0
    funext i
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hall i)
    simpa using this
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hev : MvPolynomial.eval x f = ∑ i, ∑ j, ((S i j : ℤ) : ZMod p) * x i * x j := by
      simp [f, MvPolynomial.eval_sum]
    rw [hev] at hx
    simp only [QS, dotProduct, mulVec, Fin.sum_univ_three] at hx ⊢
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    linear_combination hx

/-- Hensel along one direction `w` inside the coset `ρ + Dℤ³`. -/
theorem b3_vec {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (ρ y x0 w : Fin 3 → ℤ) (D N : ℤ)
    (hy : y = ρ + D • x0) (h g : ℕ) (a' b' c' t0 u : ℤ)
    (hF : ∀ t : ℤ, QS S (y + (t * D) • w) - N = (p : ℤ) ^ h * (a' * t ^ 2 + b' * t + c'))
    (hF0 : (p : ℤ) ^ (2 * g + 1) ∣ a' * t0 ^ 2 + b' * t0 + c')
    (hb : b' + 2 * a' * t0 = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u)
    (hprim : ¬ ∀ i, (p : ℤ) ∣ (y + (t0 * D) • w) i) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i := by
  intro e
  obtain ⟨τ, hτ⟩ := b3_hensel hp a' b' c' t0 u g hF0 hb hu e
  have hx : ρ + D • (x0 + (t0 + (p : ℤ) ^ (g + 1) * τ) • w)
      = y + ((t0 + (p : ℤ) ^ (g + 1) * τ) * D) • w := by
    rw [hy]; funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨x0 + (t0 + (p : ℤ) ^ (g + 1) * τ) • w, ?_, ?_⟩
  · rw [hx, hF]
    exact Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans hτ) _
  · rw [hx]
    intro hall
    apply hprim
    intro i
    have h1 := hall i
    have h2 : (y + ((t0 + (p : ℤ) ^ (g + 1) * τ) * D) • w) i
        = (y + (t0 * D) • w) i + (p : ℤ) * ((p : ℤ) ^ g * τ * D * w i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h2] at h1
    exact (dvd_add_left (dvd_mul_right _ _)).mp h1

/-- The case `h = 0`, `t₀ = 0`. -/
theorem b3_vec0 {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (ρ y x0 w : Fin 3 → ℤ) (D N : ℤ)
    (hy : y = ρ + D • x0) (g : ℕ) (u : ℤ)
    (hb : D * (y ⬝ᵥ (S *ᵥ w) + w ⬝ᵥ (S *ᵥ y)) = (p : ℤ) ^ g * u) (hu : ¬ (p : ℤ) ∣ u)
    (hc : (p : ℤ) ^ (2 * g + 1) ∣ QS S y - N) (hprim : ¬ ∀ i, (p : ℤ) ∣ y i) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i :=
  b3_vec hp S ρ y x0 w D N hy 0 g (D ^ 2 * QS S w) (D * (y ⬝ᵥ (S *ᵥ w) + w ⬝ᵥ (S *ᵥ y)))
    (QS S y - N) 0 u (fun t => by rw [b3_QS_add_smul]; ring) (by simpa using hc) (by simpa using hb) hu
    (by simpa using hprim)

theorem b3_val_le {q : ℕ} (hq : q.Prime) {c : ℤ} (hc : c ≠ 0) : padicValInt q c ≤ c.natAbs := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h1 : (q : ℤ) ^ padicValInt q c ∣ c := (padicValInt_dvd_iff _ c).mpr (Or.inr le_rfl)
  have h2 : q ^ padicValInt q c ∣ c.natAbs := by
    have : ((q ^ padicValInt q c : ℕ) : ℤ) ∣ c := by push_cast; exact h1
    exact Int.natCast_dvd.mp this
  have h3 : q ^ padicValInt q c ≤ c.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hc) h2
  have h4 : padicValInt q c < q ^ padicValInt q c := Nat.lt_pow_self hq.one_lt
  omega

theorem b3_val {q : ℕ} (hq : q.Prime) {c N : ℤ} (hc : c ≠ 0) (h : (q : ℤ) ^ (c.natAbs + 1) ∣ N - c) :
    padicValInt q N = padicValInt q c := by
  haveI : Fact q.Prime := ⟨hq⟩
  set v := padicValInt q c with hv
  have hvle : v ≤ c.natAbs := b3_val_le hq hc
  have h1 : (q : ℤ) ^ (v + 1) ∣ N - c := (pow_dvd_pow _ (by omega)).trans h
  have h2 : (q : ℤ) ^ v ∣ c := (padicValInt_dvd_iff _ c).mpr (Or.inr le_rfl)
  have h3 : ¬ (q : ℤ) ^ (v + 1) ∣ c := by
    intro hd
    rcases (padicValInt_dvd_iff _ c).mp hd with h0 | h0
    · exact hc h0
    · omega
  have hN : ¬ (q : ℤ) ^ (v + 1) ∣ N := by
    intro hd; apply h3
    have := dvd_sub hd h1
    simpa using this
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
  have hge : v ≤ padicValInt q N := by
    have : (q : ℤ) ^ v ∣ N := by
      have := dvd_add ((pow_dvd_pow _ (Nat.le_succ v)).trans h1) h2
      simpa using this
    rcases (padicValInt_dvd_iff _ N).mp this with h0 | h0
    · exact absurd h0 hN0
    · exact h0
  have hle : padicValInt q N < v + 1 := by
    by_contra hcon
    exact hN ((padicValInt_dvd_iff _ N).mpr (Or.inr (by omega)))
  omega

theorem b3_QS_congr (S : Matrix (Fin 3) (Fin 3) ℤ) (n : ℤ) (ρ σ : Fin 3 → ℤ)
    (h : ∀ i, ρ i ≡ σ i [ZMOD n]) : QS S ρ ≡ QS S σ [ZMOD n] := by
  have hd : ∀ i, n ∣ ρ i - σ i := fun i => (h i).symm.dvd
  choose t ht using hd
  have hρ : ρ = σ + n • t := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linear_combination ht i
  rw [hρ, b3_QS_add_smul]
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-((σ ⬝ᵥ (S *ᵥ t) + t ⬝ᵥ (S *ᵥ σ)) + n * QS S t), by ring⟩

theorem b3_dvd_QS {p : ℤ} (S : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) (h : ∀ i, p ∣ y i) :
    p ∣ QS S y := by
  simp only [QS, dotProduct]
  exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (h i) _)

theorem b3_dvd_polar {p : ℤ} (S : Matrix (Fin 3) (Fin 3) ℤ) (x y : Fin 3 → ℤ) (h : ∀ i, p ∣ y i) :
    p ∣ x ⬝ᵥ (S *ᵥ y) + y ⬝ᵥ (S *ᵥ x) := by
  refine dvd_add ?_ ?_
  · simp only [dotProduct, mulVec]
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right
      (Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_right (h j) _)) _)
  · simp only [dotProduct]
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (h i) _)

/-- Case A: primes dividing `R` (`2·d·det S`), where the coset point `y` is `R^K`-close to `e₁`. -/
theorem b3_caseA {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (ρ y x0 v : Fin 3 → ℤ) (D R N c : ℤ) (K : ℕ) (i0 : Fin 3)
    (hy1 : y = e1 + R ^ K • v) (hy2 : y = ρ + D • x0) (hc : c = QS S e1) (hNc : R ^ K ∣ N - c)
    (hpR : (p : ℤ) ∣ R) (hb1 : D * (2 * (S *ᵥ e1) i0) ≠ 0)
    (hK : 2 * (D * (2 * (S *ᵥ e1) i0)).natAbs + 1 ≤ K) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g := padicValInt p (D * (2 * (S *ᵥ e1) i0)) with hgdef
  have hg : g ≤ (D * (2 * (S *ᵥ e1) i0)).natAbs := b3_val_le hp hb1
  have hgK : 2 * g + 1 ≤ K := by omega
  obtain ⟨u1, hu1⟩ : (p : ℤ) ^ g ∣ D * (2 * (S *ᵥ e1) i0) :=
    (padicValInt_dvd_iff _ _).mpr (Or.inr le_rfl)
  have hu1p : ¬ (p : ℤ) ∣ u1 := by
    rintro ⟨r, hr⟩
    have : (p : ℤ) ^ (g + 1) ∣ D * (2 * (S *ᵥ e1) i0) := ⟨r, by rw [hu1, hr]; ring⟩
    rcases (padicValInt_dvd_iff _ _).mp this with h0 | h0
    · exact hb1 h0
    · omega
  obtain ⟨s, hs⟩ : (p : ℤ) ^ K ∣ R ^ K := pow_dvd_pow_of_dvd hpR K
  obtain ⟨K', hK'⟩ : ∃ K', K = g + 1 + K' := ⟨K - (g + 1), by omega⟩
  have hSy : (S *ᵥ y) i0 = (S *ᵥ e1) i0 + R ^ K * (S *ᵥ v) i0 := by
    rw [hy1, mulVec_add, mulVec_smul]; simp
  have hb : D * (y ⬝ᵥ (S *ᵥ Pi.single i0 1) + Pi.single i0 1 ⬝ᵥ (S *ᵥ y))
      = (p : ℤ) ^ g * (u1 + (p : ℤ) * ((p : ℤ) ^ K' * s * (D * 2 * (S *ᵥ v) i0))) := by
    rw [b3_polar_single S hS y i0, hSy, hs, hK']
    linear_combination hu1
  have hu : ¬ (p : ℤ) ∣ u1 + (p : ℤ) * ((p : ℤ) ^ K' * s * (D * 2 * (S *ᵥ v) i0)) := by
    intro h
    exact hu1p ((dvd_add_left (dvd_mul_right _ _)).mp h)
  have hc' : (p : ℤ) ^ (2 * g + 1) ∣ QS S y - N := by
    have hdecomp : QS S y - N
        = R ^ K * ((e1 ⬝ᵥ (S *ᵥ v) + v ⬝ᵥ (S *ᵥ e1)) + R ^ K * QS S v) - (N - c) := by
      rw [hy1, b3_QS_add_smul, hc]; ring
    have h1 : R ^ K ∣ QS S y - N := by
      rw [hdecomp]; exact dvd_sub (dvd_mul_right _ _) hNc
    exact dvd_trans (pow_dvd_pow _ hgK) (dvd_trans (Dvd.intro s hs.symm) h1)
  have hprim : ¬ ∀ i, (p : ℤ) ∣ y i := by
    intro h
    have h0 := h 0
    rw [hy1] at h0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, Pi.single_eq_same] at h0
    have hm : (p : ℤ) ∣ R ^ K * v 0 := dvd_mul_of_dvd_left (dvd_pow hpR (by omega)) _
    have h1 : (p : ℤ) ∣ 1 := (dvd_add_left hm).mp h0
    have := Int.natCast_dvd.mp h1
    simp at this
    exact hp.one_lt.ne' this
  exact b3_vec0 hp S ρ y x0 (Pi.single i0 1) D N hy2 g _ hb hu hc' hprim

/-- Case B: the new prime `ℓ = p`, where the coset is `ρ + p·(…)` and only `QS ρ ≡ QS e₁ (mod p)` is known. -/
theorem b3_caseB {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (ρ y x0 : Fin 3 → ℤ) (d N c : ℤ)
    (hy2 : y = ρ + (d * p) • x0) (hρ : QS S ρ ≡ c [ZMOD p]) (hNc : (p : ℤ) ∣ N - c)
    (hpc : ¬ (p : ℤ) ∣ c) (hpd : ¬ (p : ℤ) ∣ d) (hp2 : ¬ (p : ℤ) ∣ 2) (hpdet : ¬ (p : ℤ) ∣ S.det) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + (d * p) • x) - N ∧
      ¬ ∀ i, (p : ℤ) ∣ (ρ + (d * p) • x) i := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hyρ : (p : ℤ) ∣ QS S y - QS S ρ := by
    rw [hy2, b3_QS_add_smul]
    exact ⟨d * (ρ ⬝ᵥ (S *ᵥ x0) + x0 ⬝ᵥ (S *ᵥ ρ)) + d * d * p * QS S x0, by ring⟩
  have hcρ : (p : ℤ) ∣ c - QS S ρ := hρ.dvd
  obtain ⟨c', hc'⟩ : (p : ℤ) ∣ QS S y - N := by
    rw [show QS S y - N = (QS S y - QS S ρ) - (c - QS S ρ) - (N - c) by ring]
    exact dvd_sub (dvd_sub hyρ hcρ) hNc
  have hyprim : ¬ ∀ i, (p : ℤ) ∣ y i := by
    intro h
    have h1 := b3_dvd_QS S y h
    apply hpc
    rw [show c = (c - QS S ρ) + (QS S y - (QS S y - QS S ρ)) by ring]
    exact dvd_add hcρ (dvd_sub h1 hyρ)
  obtain ⟨i, hi⟩ := b3_coord_not_dvd hp S hpdet y hyprim
  have hb'p : ¬ (p : ℤ) ∣ d * (2 * (S *ᵥ y) i) := by
    intro h
    rcases hpz.dvd_or_dvd h with h | h
    · exact hpd h
    rcases hpz.dvd_or_dvd h with h | h
    · exact hp2 h
    · exact hi h
  obtain ⟨α, β, hαβ⟩ := (hpz.irreducible.coprime_iff_not_dvd).mpr hb'p
  have hF : ∀ t : ℤ, QS S (y + (t * (d * p)) • Pi.single i 1) - N = (p : ℤ) ^ 1 *
      ((d ^ 2 * p * QS S (Pi.single i 1)) * t ^ 2 + (d * (2 * (S *ᵥ y) i)) * t + c') := by
    intro t
    rw [b3_QS_add_smul, b3_polar_single S hS y i]
    linear_combination hc'
  have hF0 : (p : ℤ) ^ (2 * 0 + 1) ∣ (d ^ 2 * p * QS S (Pi.single i 1)) * (-c' * β) ^ 2
      + (d * (2 * (S *ᵥ y) i)) * (-c' * β) + c' :=
    ⟨d ^ 2 * QS S (Pi.single i 1) * (-c' * β) ^ 2 + c' * α, by linear_combination (-c') * hαβ⟩
  have hu : ¬ (p : ℤ) ∣ (d * (2 * (S *ᵥ y) i)) + 2 * (d ^ 2 * p * QS S (Pi.single i 1)) * (-c' * β) := by
    intro h
    apply hb'p
    have hm : (p : ℤ) ∣ 2 * (d ^ 2 * p * QS S (Pi.single i 1)) * (-c' * β) :=
      ⟨2 * d ^ 2 * QS S (Pi.single i 1) * (-c' * β), by ring⟩
    exact (dvd_add_left hm).mp h
  have hprim : ¬ ∀ j, (p : ℤ) ∣ (y + ((-c' * β) * (d * p)) • (Pi.single i (1 : ℤ) : Fin 3 → ℤ)) j := by
    intro h
    apply hyprim
    intro j
    have h1 := h j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    have hm : (p : ℤ) ∣ (-c' * β) * (d * p) * (Pi.single i (1 : ℤ) : Fin 3 → ℤ) j :=
      ⟨(-c' * β) * d * (Pi.single i (1 : ℤ) : Fin 3 → ℤ) j, by ring⟩
    exact (dvd_add_left hm).mp h1
  exact b3_vec hp S ρ y x0 (Pi.single i 1) (d * p) N hy2 1 0 _ _ c' (-c' * β) _ hF hF0
    (by ring) hu hprim

/-- Case C: all other primes (`p ∤ 2·d·ℓ·det S`); Chevalley–Warning supplies the residue. -/
theorem b3_caseC {p : ℕ} (hp : p.Prime) (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (ρ : Fin 3 → ℤ) (D N : ℤ) (hpD : ¬ (p : ℤ) ∣ D) (hp2 : ¬ (p : ℤ) ∣ 2)
    (hpdet : ¬ (p : ℤ) ∣ S.det) :
    ∀ e : ℕ, ∃ x : Fin 3 → ℤ, (p : ℤ) ^ e ∣ QS S (ρ + D • x) - N ∧ ¬ ∀ i, (p : ℤ) ∣ (ρ + D • x) i := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨xh, hxprim, q, hq⟩ := b3_isotropic hp S
  obtain ⟨j, hj⟩ := b3_coord_not_dvd hp S hpdet xh hxprim
  have hs2 : ¬ (p : ℤ) ∣ 2 * (S *ᵥ xh) j := by
    intro h
    rcases hpz.dvd_or_dvd h with h | h
    · exact hp2 h
    · exact hj h
  obtain ⟨α2, β2, h2⟩ := (hpz.irreducible.coprime_iff_not_dvd).mpr hs2
  obtain ⟨v0, hv0⟩ : ∃ v0 : Fin 3 → ℤ,
      v0 = Pi.single j 1 + ((N - QS S (Pi.single j 1)) * β2) • xh := ⟨_, rfl⟩
  have hpol : Pi.single j 1 ⬝ᵥ (S *ᵥ xh) + xh ⬝ᵥ (S *ᵥ Pi.single j 1) = 2 * (S *ᵥ xh) j := by
    rw [add_comm, b3_polar_single S hS xh j]
  have hv0N : (p : ℤ) ∣ QS S v0 - N := by
    rw [hv0, b3_QS_add_smul, hpol, hq]
    exact ⟨-(N - QS S (Pi.single j 1)) * α2 + ((N - QS S (Pi.single j 1)) * β2) ^ 2 * q,
      by linear_combination (N - QS S (Pi.single j 1)) * h2⟩
  have hv0prim : ¬ ∀ i, (p : ℤ) ∣ v0 i := by
    intro h
    have hd := b3_dvd_polar S xh v0 h
    have hexp : xh ⬝ᵥ (S *ᵥ v0) + v0 ⬝ᵥ (S *ᵥ xh)
        = (xh ⬝ᵥ (S *ᵥ Pi.single j 1) + Pi.single j 1 ⬝ᵥ (S *ᵥ xh))
          + ((N - QS S (Pi.single j 1)) * β2) * (2 * QS S xh) := by
      rw [hv0]
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, QS]
      ring
    rw [hexp, b3_polar_single S hS xh j, hq] at hd
    have hm : (p : ℤ) ∣ ((N - QS S (Pi.single j 1)) * β2) * (2 * ((p : ℤ) * q)) :=
      ⟨((N - QS S (Pi.single j 1)) * β2) * 2 * q, by ring⟩
    exact hs2 ((dvd_add_left hm).mp hd)
  obtain ⟨γ, δ, hγ⟩ := ((hpz.irreducible.coprime_iff_not_dvd).mpr hpD).symm
  obtain ⟨y, hy⟩ : ∃ y : Fin 3 → ℤ, y = ρ + D • (γ • (v0 - ρ)) := ⟨_, rfl⟩
  have hyv : y = v0 + (p : ℤ) • (fun i => -δ * (v0 i - ρ i)) := by
    rw [hy]; funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (v0 i - ρ i) * hγ
  have hyN : (p : ℤ) ∣ QS S y - N := by
    rw [hyv, b3_QS_add_smul]
    have := hv0N
    obtain ⟨m, hm⟩ := this
    exact ⟨m + (v0 ⬝ᵥ (S *ᵥ (fun i => -δ * (v0 i - ρ i))) + (fun i => -δ * (v0 i - ρ i)) ⬝ᵥ (S *ᵥ v0))
      + (p : ℤ) * QS S (fun i => -δ * (v0 i - ρ i)), by linear_combination hm⟩
  have hyprim : ¬ ∀ i, (p : ℤ) ∣ y i := by
    intro h
    apply hv0prim
    intro i
    have h1 := h i
    rw [hyv] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    exact (dvd_add_left (dvd_mul_right _ _)).mp h1
  obtain ⟨i, hi⟩ := b3_coord_not_dvd hp S hpdet y hyprim
  have hu : ¬ (p : ℤ) ∣ D * (2 * (S *ᵥ y) i) := by
    intro h
    rcases hpz.dvd_or_dvd h with h | h
    · exact hpD h
    rcases hpz.dvd_or_dvd h with h | h
    · exact hp2 h
    · exact hi h
  exact b3_vec0 hp S ρ y (γ • (v0 - ρ)) (Pi.single i 1) D N hy 0 _
    (by rw [b3_polar_single S hS y i]; ring) hu (by simpa using hyN) hyprim

/-- One coset: local primitive representability along the whole progression `t = J k`. -/
theorem b3_one (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm) (d : ℕ) (hd : 0 < d)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓd : ¬ ℓ ∣ 2 * d * S.det.natAbs * (QS S e1).natAbs)
    (ρ : Fin 3 → ℤ) (hρd : ∀ i, ρ i ≡ e1 i [ZMOD d]) (hρℓ : QS S ρ ≡ QS S e1 [ZMOD ℓ])
    (i0 : Fin 3) (hi0 : (S *ᵥ e1) i0 ≠ 0) (K : ℕ)
    (hK : 2 * (((d * ℓ : ℕ) : ℤ) * (2 * (S *ᵥ e1) i0)).natAbs + 1 ≤ K)
    (J : ℕ) (hRJ : ((2 * d * S.det.natAbs : ℕ) : ℤ) ^ K ∣ (J : ℤ)) (hℓJ : (ℓ : ℤ) ∣ (J : ℤ))
    (A B k : ℤ) :
    LocalPrimRep S (d * ℓ) ρ (A * (J * k) ^ 2 + B * (J * k) + QS S e1) := by
  have hNJ : (J : ℤ) ∣ (A * (J * k) ^ 2 + B * (J * k) + QS S e1) - QS S e1 :=
    ⟨k * (A * J * k + B), by ring⟩
  have hDdl : ((d * ℓ : ℕ) : ℤ) = (d : ℤ) * (ℓ : ℤ) := by push_cast; ring
  have hℓpz : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hℓR : ¬ (ℓ : ℤ) ∣ ((2 * d * S.det.natAbs : ℕ) : ℤ) := by
    intro h
    exact hℓd (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mp h) _)
  obtain ⟨α, β, hαβ⟩ := ((hℓpz.irreducible.coprime_iff_not_dvd).mpr hℓR).pow_right (n := K)
  have hm : ∀ i, (d : ℤ) ∣ e1 i - ρ i := fun i => (hρd i).dvd
  choose m hm using hm
  obtain ⟨y, hy⟩ : ∃ y : Fin 3 → ℤ, y = ρ + ((d * ℓ : ℕ) : ℤ) • (α • m) := ⟨_, rfl⟩
  have hy1 : y = e1 + (((2 * d * S.det.natAbs : ℕ) : ℤ)) ^ K • (fun i => -(d : ℤ) * β * m i) := by
    rw [hy, hDdl]; funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-1 : ℤ) * hm i + ((d : ℤ) * m i) * hαβ
  unfold LocalPrimRep
  intro p hp e
  have hpR_iff : (p : ℤ) ∣ ((2 * d * S.det.natAbs : ℕ) : ℤ) ↔ p ∣ 2 * d * S.det.natAbs :=
    Int.natCast_dvd_natCast
  by_cases hpR : (p : ℤ) ∣ ((2 * d * S.det.natAbs : ℕ) : ℤ)
  · have hb1 : ((d * ℓ : ℕ) : ℤ) * (2 * (S *ᵥ e1) i0) ≠ 0 := by
      refine mul_ne_zero ?_ (mul_ne_zero two_ne_zero hi0)
      exact_mod_cast (Nat.mul_pos hd hℓ.pos).ne'
    exact b3_caseA hp S hS ρ y (α • m) _ _ _ _ _ K i0 hy1 hy rfl (hRJ.trans hNJ) hpR hb1 hK e
  · have hp_nd : ¬ p ∣ 2 * d * S.det.natAbs := fun h => hpR (hpR_iff.mpr h)
    have hp2 : ¬ (p : ℤ) ∣ 2 := by
      intro h
      apply hp_nd
      have : p ∣ 2 := by exact_mod_cast Int.natCast_dvd_natCast.mp (by exact_mod_cast h)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right this _) _
    have hpdet : ¬ (p : ℤ) ∣ S.det := by
      intro h
      exact hp_nd (Dvd.dvd.mul_left (Int.natCast_dvd.mp h) _)
    have hpd : ¬ (p : ℤ) ∣ (d : ℤ) := by
      intro h
      exact hp_nd (Dvd.dvd.mul_right (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mp h) _) _)
    by_cases hpℓ : p = ℓ
    · subst hpℓ
      have hpc : ¬ (p : ℤ) ∣ QS S e1 := by
        intro h
        exact hℓd (Dvd.dvd.mul_left (Int.natCast_dvd.mp h) _)
      rw [hDdl]
      have hy2 : y = ρ + ((d : ℤ) * p) • (α • m) := by rw [hy, hDdl]
      exact b3_caseB hp S hS ρ y (α • m) (d : ℤ) _ (QS S e1) hy2 hρℓ (hℓJ.trans hNJ) hpc hpd hp2 hpdet e
    · have hpD : ¬ (p : ℤ) ∣ ((d * ℓ : ℕ) : ℤ) := by
        intro h
        have h' : p ∣ d * ℓ := Int.natCast_dvd_natCast.mp h
        rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
        · exact hpd (Int.natCast_dvd_natCast.mpr h'')
        · exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h'')
      exact b3_caseC hp S hS ρ _ _ hpD hp2 hpdet e

/-- **B3.**  One input progression `t = J k` on which `N(t) = A t² + B t + QS e₁` is locally primitively represented by
BOTH cosets `ρᵢ + dℓ ℤ³` and has the valuation of `QS e₁` at every prime of a given finite bad set.  The cosets are
fixed before `J` is chosen. -/
theorem localProgression (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) (d : ℕ) (hd : 0 < d)
    (ℓ : ℕ) (ρ₁ ρ₂ : Fin 3 → ℤ) (hℓ : ℓ.Prime) (hℓd : ¬ ℓ ∣ 2 * d * S.det.natAbs * (QS S e1).natAbs)
    (h1d : ∀ i, ρ₁ i ≡ e1 i [ZMOD d]) (h2d : ∀ i, ρ₂ i ≡ e1 i [ZMOD d])
    (h1ℓ : ∀ i, ρ₁ i ≡ e1 i [ZMOD ℓ]) (h2ℓ : QS S ρ₂ ≡ QS S e1 [ZMOD ℓ])
    (A B : ℤ) (bad : Finset ℕ) (hbad : ∀ q ∈ bad, q.Prime) (M : ℕ) (hM : 0 < M) :
    ∃ J : ℕ, 0 < J ∧ M ∣ J ∧ ∀ k : ℤ,
      LocalPrimRep S (d * ℓ) ρ₁ (A * (J * k) ^ 2 + B * (J * k) + QS S e1) ∧
      LocalPrimRep S (d * ℓ) ρ₂ (A * (J * k) ^ 2 + B * (J * k) + QS S e1) ∧
      ∀ q ∈ bad, padicValInt q (A * (J * k) ^ 2 + B * (J * k) + QS S e1) = padicValInt q (QS S e1) := by
  classical
  have he1 : e1 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e1] at this
  have hc0 : QS S e1 ≠ 0 := (hpos e1 he1).ne'
  obtain ⟨i0, hi0⟩ : ∃ i0, (S *ᵥ e1) i0 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hc0
    have : S *ᵥ e1 = 0 := funext h
    simp [QS, this]
  have hdet := b3_det_ne_zero S hpos
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 * (((d * ℓ : ℕ) : ℤ) * (2 * (S *ᵥ e1) i0)).natAbs + 1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = ∏ q ∈ bad, q ^ ((QS S e1).natAbs + 1) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by
    rw [hQ]; exact Finset.prod_pos (fun q hq => pow_pos (hbad q hq).pos _)
  have hRpos : 0 < 2 * d * S.det.natAbs :=
    Nat.mul_pos (Nat.mul_pos two_pos hd) (Int.natAbs_pos.mpr hdet)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = M * ℓ * (2 * d * S.det.natAbs) ^ K * Q := ⟨_, rfl⟩
  refine ⟨J, ?_, ?_, fun k => ?_⟩
  · rw [hJ]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM hℓ.pos) (pow_pos hRpos _)) hQpos
  · exact ⟨ℓ * (2 * d * S.det.natAbs) ^ K * Q, by rw [hJ]; ring⟩
  have hRJ : ((2 * d * S.det.natAbs : ℕ) : ℤ) ^ K ∣ (J : ℤ) := by
    rw [← Nat.cast_pow]
    exact Int.natCast_dvd_natCast.mpr ⟨M * ℓ * Q, by rw [hJ]; ring⟩
  have hℓJ : (ℓ : ℤ) ∣ (J : ℤ) :=
    Int.natCast_dvd_natCast.mpr ⟨M * (2 * d * S.det.natAbs) ^ K * Q, by rw [hJ]; ring⟩
  refine ⟨b3_one S hS d hd ℓ hℓ hℓd ρ₁ h1d (b3_QS_congr S ℓ ρ₁ e1 h1ℓ) i0 hi0 K hK.ge J hRJ hℓJ A B k,
    b3_one S hS d hd ℓ hℓ hℓd ρ₂ h2d h2ℓ i0 hi0 K hK.ge J hRJ hℓJ A B k, fun q hq => ?_⟩
  apply b3_val (hbad q hq) hc0
  have hqJ : (q : ℤ) ^ ((QS S e1).natAbs + 1) ∣ (J : ℤ) := by
    rw [← Nat.cast_pow]
    refine Int.natCast_dvd_natCast.mpr (dvd_trans (Finset.dvd_prod_of_mem (fun r : ℕ => r ^ ((QS S e1).natAbs + 1)) hq) ?_)
    rw [← hQ]
    exact ⟨M * ℓ * (2 * d * S.det.natAbs) ^ K, by rw [hJ]; ring⟩
  exact hqJ.trans ⟨k * (A * J * k + B), by ring⟩

/-- **C2.**  Given TCER, a positive definite integral ternary coset `e₁ + dℤ³`, a non-zero integer functional `p` and an
integer quadratic `N(t) = A t² + B t + QS e₁` with `A > 0` and non-zero discriminant, some input `t = M k` of any
prescribed progression has two representations of `N(t)` in the coset with different `p`-values.  Only ONE represented
value (`N(0) = QS e₁`) is used, not totality. -/
theorem ternaryCosetCollision_of_TCER (hT : TernaryCosetEventualRepresentation)
    (S : Matrix (Fin 3) (Fin 3) ℤ) (hS : S.IsSymm)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < QS S y) (d : ℕ) (hd : 0 < d)
    (p : Fin 3 → ℤ) (hp : p ≠ 0) (A B : ℤ) (hA : 0 < A) (hdisc : B ^ 2 - 4 * A * QS S e1 ≠ 0)
    (M : ℕ) (hM : 0 < M) :
    ∃ (k : ℤ) (x x' : Fin 3 → ℤ),
      QS S (e1 + (d : ℤ) • x) = A * (M * k) ^ 2 + B * (M * k) + QS S e1 ∧
      QS S (e1 + (d : ℤ) • x') = A * (M * k) ^ 2 + B * (M * k) + QS S e1 ∧
      p ⬝ᵥ (e1 + (d : ℤ) • x) ≠ p ⬝ᵥ (e1 + (d : ℤ) • x') := by
  classical
  obtain ⟨ℓ, ρ₁, ρ₂, hℓ, hℓd, h1d, h2d, h1ℓ, h2ℓ, hsep⟩ := twoVisibleCosets S hS hpos d hd p hp
  have hdℓ : 0 < d * ℓ := Nat.mul_pos hd hℓ.pos
  obtain ⟨bad1, E1, hbad1, hE1, hT1⟩ := hT S (d * ℓ) ρ₁ hS hpos hdℓ
  obtain ⟨bad2, E2, hbad2, hE2, hT2⟩ := hT S (d * ℓ) ρ₂ hS hpos hdℓ
  have he1 : e1 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e1] at this
  have hc : 0 < QS S e1 := hpos e1 he1
  set c := QS S e1 with hcdef
  have hbadP : ∀ q ∈ bad1 ∪ bad2, q.Prime := by
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact hbad1 q h
    · exact hbad2 q h
  obtain ⟨J, hJ, hMJ, hloc⟩ :=
    localProgression S hS hpos d hd ℓ ρ₁ ρ₂ hℓ hℓd h1d h2d h1ℓ h2ℓ A B (bad1 ∪ bad2) hbadP M hM
  let b : ℕ → ℕ := fun q => (padicValInt q c)
  obtain ⟨N1, hN1⟩ := hT1 b
  obtain ⟨N2, hN2⟩ := hT2 b
  have hJpos : (0 : ℤ) < (J : ℤ) := by exact_mod_cast hJ
  have hAJ : 0 < A * (J : ℤ) ^ 2 := by positivity
  have hdiscJ : (B * (J : ℤ)) ^ 2 - 4 * (A * (J : ℤ) ^ 2) * c ≠ 0 := by
    have : (B * (J : ℤ)) ^ 2 - 4 * (A * (J : ℤ) ^ 2) * c = (J : ℤ) ^ 2 * (B ^ 2 - 4 * A * c) := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero 2 hJpos.ne') hdisc
  have hEpos : ∀ e ∈ E1 ∪ E2, 0 < e := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact hE1 e h
    · exact hE2 e h
  obtain ⟨q, k1, hq, -, -, -, hk⟩ :=
    squareClassEscapeProgression (A * (J : ℤ) ^ 2) (B * (J : ℤ)) c hAJ hc hdiscJ 1 one_pos (E1 ∪ E2) hEpos
  -- a large input in the class k ≡ k1 (mod q²)
  set T : ℤ := |N1| + |N2| with hT
  set s : ℤ := |k1| + |B * (J : ℤ)| + T + 1 with hs
  set k : ℤ := k1 + (q : ℤ) ^ 2 * s with hkdef
  have hq1 : (1 : ℤ) ≤ (q : ℤ) ^ 2 := by
    have : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.one_lt.le
    nlinarith
  have hs0 : 0 ≤ s := by positivity
  have hk_ge : |B * (J : ℤ)| + T + 1 ≤ k := by
    have h1 : s ≤ (q : ℤ) ^ 2 * s := by nlinarith
    have h2 : -|k1| ≤ k1 := neg_abs_le k1
    simp only [hkdef, hs] at h1 ⊢
    linarith
  have hk_mod : k ≡ k1 [ZMOD (q : ℤ) ^ 2] := by
    refine (Int.modEq_iff_dvd.mpr ⟨-s, ?_⟩)
    simp only [hkdef]; ring
  obtain ⟨hN0, -, hsq⟩ := hk k hk_mod
  set N : ℤ := A * (J : ℤ) ^ 2 * k ^ 2 + B * (J : ℤ) * k + c with hNdef
  have hNeq : A * ((J : ℤ) * k) ^ 2 + B * ((J : ℤ) * k) + QS S e1 = N := by
    simp only [hNdef, hcdef]; ring
  have hT0 : 0 ≤ T := by positivity
  have hBk : -(|B * (J : ℤ)| * k) ≤ B * (J : ℤ) * k := by
    have hk0 : 0 ≤ k := by
      have := abs_nonneg (B * (J : ℤ)); linarith
    have := neg_abs_le (B * (J : ℤ))
    nlinarith
  have hN_ge : T + 1 ≤ N := by
    have hu0 := abs_nonneg (B * (J : ℤ))
    have hk1 : 1 ≤ k := by linarith
    have hk0 : 0 ≤ k := by linarith
    have hAk : k ^ 2 ≤ A * (J : ℤ) ^ 2 * k ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg k) (show (1 : ℤ) ≤ A * (J : ℤ) ^ 2 from hAJ)
    have h1 : k * (T + 1) ≤ k * (k - |B * (J : ℤ)|) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have h2 : k * (k - |B * (J : ℤ)|) = k ^ 2 - |B * (J : ℤ)| * k := by ring
    have h3 : 1 * (T + 1) ≤ k * (T + 1) := mul_le_mul_of_nonneg_right hk1 (by linarith)
    have h4 : N = A * (J : ℤ) ^ 2 * k ^ 2 + B * (J : ℤ) * k + c := hNdef
    linarith
  have hN1le : N1 ≤ N := by
    have := le_abs_self N1; have := abs_nonneg N2; linarith
  have hN2le : N2 ≤ N := by
    have := le_abs_self N2; have := abs_nonneg N1; linarith
  obtain ⟨hL1, hL2, hval⟩ := hloc k
  rw [hNeq] at hL1 hL2 hval
  have hbadcond : ∀ bad : Finset ℕ, (∀ p ∈ bad, p ∈ bad1 ∪ bad2) →
      ∀ p ∈ bad, ¬ (p : ℤ) ^ (b p + 1) ∣ N := by
    intro bad hsub r hr hdiv
    have hrP : r.Prime := hbadP r (hsub r hr)
    haveI : Fact r.Prime := ⟨hrP⟩
    have hv : padicValInt r N = padicValInt r c := hval r (hsub r hr)
    rcases (padicValInt_dvd_iff (p := r) (b r + 1) N).mp hdiv with h | h
    · exact hN0 h
    · simp only [b] at h
      rw [hv] at h
      omega
  have hEcond : ∀ E : Finset ℕ, (∀ e ∈ E, e ∈ E1 ∪ E2) →
      ∀ e ∈ E, ¬ ∃ r : ℚ, (N : ℚ) = (e : ℚ) * r ^ 2 := by
    intro E hsub e he
    have := hsq e (hsub e he)
    simpa [hNdef] using this
  obtain ⟨x₁, hx₁⟩ := hN1 N hN1le hL1
    (hbadcond bad1 (fun r hr => Finset.mem_union_left _ hr))
    (hEcond E1 (fun e he => Finset.mem_union_left _ he))
  obtain ⟨x₂, hx₂⟩ := hN2 N hN2le hL2
    (hbadcond bad2 (fun r hr => Finset.mem_union_right _ hr))
    (hEcond E2 (fun e he => Finset.mem_union_right _ he))
  -- move each representation into the coset e₁ + dℤ³
  have hshift : ∀ ρ : Fin 3 → ℤ, (∀ i, ρ i ≡ e1 i [ZMOD d]) → ∀ y : Fin 3 → ℤ,
      ∃ x : Fin 3 → ℤ, e1 + (d : ℤ) • x = ρ + ((d * ℓ : ℕ) : ℤ) • y := by
    intro ρ hρ y
    have hdv : ∀ i, (d : ℤ) ∣ ρ i - e1 i := fun i => (hρ i).symm.dvd
    choose w hw using hdv
    refine ⟨fun i => w i + (ℓ : ℤ) * y i, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    have := hw i
    linear_combination -this
  obtain ⟨x, hx⟩ := hshift ρ₁ h1d x₁
  obtain ⟨x', hx'⟩ := hshift ρ₂ h2d x₂
  obtain ⟨m, hm⟩ := hMJ
  refine ⟨(m : ℤ) * k, x, x', ?_, ?_, ?_⟩
  · rw [hx, hx₁, hNdef, hm]; push_cast; ring
  · rw [hx', hx₂, hNdef, hm]; push_cast; ring
  · rw [hx, hx']
    intro heq
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at heq
    apply hsep
    refine Int.modEq_iff_dvd.mpr ⟨(d : ℤ) * (p ⬝ᵥ x₁ - p ⬝ᵥ x₂), ?_⟩
    push_cast at heq
    linear_combination -heq

end TCERBridge

end DiophCompression.ResearchUpgrade
