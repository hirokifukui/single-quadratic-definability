/-
  Sharpness.lean — Gate-18 research program, Packet A6.
  Two exact-sharpness case studies for the counting function `N_S(X) = fiberCountZZ S X`:

  A6-1  Pell `D = 2`, `S = {c | ∃ u, c² − 2u² = 1}`:  `N_S(X) = Θ(log X)`.
        Lower: an `ExponentialInjection` via the fundamental-unit orbit `X_{n+1} = 3X_n+4U_n`,
        `U_{n+1} = 2X_n+3U_n`, envelope `X_n ≤ 6ⁿ` (A = 1, B = 6) ⇒ `LogLowerBound`.
        Upper (the sharpness): a DESCENT `(c,v) ↦ (3c−4v, 3v−2c)` (no fundamental-unit theory)
        proving every positive solution is some `X_n`, hence `N_S(X) ≤ 2·log₃X + 3`.

  A6-2  `E = {m | ∃ n, m = 2^(2ⁿ)}`:  a doubly-logarithmic set, the separator.
        (a) a computable decision procedure `DecidablePred (· ∈ E)`;
        (b) `N_E(X) = log₂log₂X + 1` (exact) ⇒ the `≤ +2` / `≥` bounds;
        (c) A6-3: `E` is not a quadratic fibre (conditional on `FixedAPPrimeLowerBound`) — the log
            barrier forces `κ log X ≤ N_E(X) ≤ log₂log₂X + 2`, impossible by a growth lemma;
        (d) A6-4: the general separator — any infinite `S` whose count dips below every `κ log X`
            infinitely often is not a quadratic fibre.

  Every proof is complete; no new axiom; std-3 (propext, Classical.choice, Quot.sound). The `FixedAPPrimeLowerBound`
  hypothesis is kept explicit in the types of A6-3/A6-4 (it disappears only after Packet B2).
-/
import ResearchUpgrade.Counting
import ResearchUpgrade.PrimeRay
import ResearchUpgrade.Shadow.SummitClosureR

namespace DiophCompression.ResearchUpgrade

open MvPolynomial MPUP

/-! ## A6-1 : Pell `D = 2` -/

/-- The Pell-`2` output set `S = {c : ℤ | ∃ u, c² − 2u² = 1}`. -/
def pell2Set : Set ℤ := {c : ℤ | ∃ u : ℤ, c ^ 2 - 2 * u ^ 2 = 1}

/-- The fundamental-unit orbit `(X_n, U_n)` with `(X_0,U_0) = (1,0)` and
`(X_{n+1},U_{n+1}) = (3X_n+4U_n, 2X_n+3U_n)`. -/
def pellPair : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (pellPair n).1 + 4 * (pellPair n).2, 2 * (pellPair n).1 + 3 * (pellPair n).2)

/-- The `X`-coordinate of the orbit. -/
def pellX (n : ℕ) : ℤ := (pellPair n).1
/-- The `U`-coordinate of the orbit. -/
def pellU (n : ℕ) : ℤ := (pellPair n).2

@[simp] theorem pellX_zero : pellX 0 = 1 := rfl
@[simp] theorem pellU_zero : pellU 0 = 0 := rfl
theorem pellX_succ (n : ℕ) : pellX (n + 1) = 3 * pellX n + 4 * pellU n := rfl
theorem pellU_succ (n : ℕ) : pellU (n + 1) = 2 * pellX n + 3 * pellU n := rfl

/-- The norm is preserved along the orbit: `X_n² − 2U_n² = 1`. -/
theorem pell_norm (n : ℕ) : pellX n ^ 2 - 2 * pellU n ^ 2 = 1 := by
  induction n with
  | zero => simp
  | succ k ih => rw [pellX_succ, pellU_succ]; linear_combination ih

/-- `X_n ≥ 1` and `U_n ≥ 0`. -/
theorem pell_pos (n : ℕ) : 1 ≤ pellX n ∧ 0 ≤ pellU n := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ k ih =>
    obtain ⟨hX, hU⟩ := ih
    exact ⟨by rw [pellX_succ]; linarith, by rw [pellU_succ]; linarith⟩

/-- The orbit is strictly increasing, hence injective. -/
theorem pellX_strictMono : StrictMono pellX := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [pellX_succ]
  have := pell_pos n
  linarith [this.1, this.2]

/-- Each orbit point is a Pell solution. -/
theorem pellX_mem (n : ℕ) : pellX n ∈ pell2Set := ⟨pellU n, pell_norm n⟩

/-- The descent bound `4U_n ≤ 3X_n`, driving `X_{n+1} ≤ 6X_n`. -/
theorem pell_desc_bound (n : ℕ) : 4 * pellU n ≤ 3 * pellX n := by
  have hnorm := pell_norm n
  have hX := (pell_pos n).1
  have hU := (pell_pos n).2
  have key : (3 * pellX n - 4 * pellU n) * (3 * pellX n + 4 * pellU n) = 9 + 2 * pellU n ^ 2 := by
    linear_combination 9 * hnorm
  have hsum : (0 : ℤ) < 3 * pellX n + 4 * pellU n := by linarith
  have hprod : (0 : ℤ) < (3 * pellX n - 4 * pellU n) * (3 * pellX n + 4 * pellU n) := by
    rw [key]; positivity
  nlinarith [hprod, hsum]

/-- Envelope: `X_n ≤ 6ⁿ`. -/
theorem pellX_le_six_pow (n : ℕ) : pellX n ≤ 6 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep : pellX (k + 1) ≤ 6 * pellX k := by
      rw [pellX_succ]; linarith [pell_desc_bound k]
    calc pellX (k + 1) ≤ 6 * pellX k := hstep
      _ ≤ 6 * 6 ^ k := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 6 ^ (k + 1) := by rw [pow_succ]; ring

/-- Lower envelope: `3ⁿ ≤ X_n`. -/
theorem pellX_ge_pow (n : ℕ) : (3 : ℤ) ^ n ≤ pellX n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pellX_succ, pow_succ]
    nlinarith [ih, (pell_pos k).2, (pell_pos k).1]

/-! ### The descent: every positive solution is an orbit point -/

/-- Strong-induction core of the descent. -/
theorem pell2_forward (m : ℕ) :
    ∀ c : ℤ, c.toNat = m → 0 < c → c ∈ pell2Set → ∃ n, c = pellX n := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro c hcm hc hmem
    obtain ⟨u, hu⟩ := hmem
    set v := |u| with hvdef
    have hv0 : 0 ≤ v := abs_nonneg u
    have huv : c ^ 2 - 2 * v ^ 2 = 1 := by rw [hvdef, sq_abs]; exact hu
    by_cases hc3 : c ≤ 2
    · interval_cases c
      · exact ⟨0, rfl⟩
      · exfalso
        have h3 : 2 * v ^ 2 = 3 := by linear_combination -huv
        omega
    · replace hc3 := not_le.mp hc3
      have hc3' : 3 ≤ c := by omega
      have hv2 : 4 ≤ v ^ 2 := by
        nlinarith [huv, hc3',
          mul_nonneg (show (0 : ℤ) ≤ c - 3 by linarith) (show (0 : ℤ) ≤ c + 3 by linarith)]
      have hu'0 : 0 ≤ 3 * v - 2 * c := by
        have key : (3 * v - 2 * c) * (3 * v + 2 * c) = v ^ 2 - 4 := by linear_combination -4 * huv
        have hpr : 0 ≤ (3 * v - 2 * c) * (3 * v + 2 * c) := by rw [key]; linarith
        have hsum : 0 < 3 * v + 2 * c := by linarith
        nlinarith [hpr, hsum]
      have hc'1 : 1 ≤ 3 * c - 4 * v := by
        have key2 : (3 * c - 1 - 4 * v) * (3 * c - 1 + 4 * v) = (c - 3) ^ 2 := by
          linear_combination 8 * huv
        have hpr2 : 0 ≤ (3 * c - 1 - 4 * v) * (3 * c - 1 + 4 * v) := by rw [key2]; exact sq_nonneg _
        have hsum2 : 0 < 3 * c - 1 + 4 * v := by linarith
        nlinarith [hpr2, hsum2]
      have hlt2v : c < 2 * v := by
        have key3 : (2 * v - c) * (2 * v + c) = 2 * v ^ 2 - 1 := by linear_combination -huv
        have hpr3 : 0 < (2 * v - c) * (2 * v + c) := by rw [key3]; linarith
        have hsum3 : 0 < 2 * v + c := by linarith
        nlinarith [hpr3, hsum3]
      have hc'lt : 3 * c - 4 * v < c := by linarith
      have hn2 : (3 * c - 4 * v) ^ 2 - 2 * (3 * v - 2 * c) ^ 2 = 1 := by linear_combination huv
      have hc'mem : (3 * c - 4 * v) ∈ pell2Set := ⟨3 * v - 2 * c, hn2⟩
      obtain ⟨k, hk⟩ :=
        ih (3 * c - 4 * v).toNat (by omega) (3 * c - 4 * v) rfl (by linarith) hc'mem
      have hUeq : pellU k = 3 * v - 2 * c := by
        have hpn := pell_norm k
        rw [← hk] at hpn
        have h2 : 2 * pellU k ^ 2 = 2 * (3 * v - 2 * c) ^ 2 := by linarith [hpn, hn2]
        have h1 : pellU k ^ 2 = (3 * v - 2 * c) ^ 2 := by linarith
        have hpUk : 0 ≤ pellU k := (pell_pos k).2
        have hmul0 : (pellU k - (3 * v - 2 * c)) * (pellU k + (3 * v - 2 * c)) = 0 := by
          linear_combination h1
        rcases mul_eq_zero.mp hmul0 with h | h
        · linarith
        · omega
      refine ⟨k + 1, ?_⟩
      rw [pellX_succ, ← hk, hUeq]; ring

/-- A6-1 descent (sharpness core): a positive integer is a Pell-`2` solution iff it is an orbit point. -/
theorem pell2_pos_mem_iff {c : ℤ} (hc : 0 < c) : c ∈ pell2Set ↔ ∃ n, c = pellX n := by
  constructor
  · intro h; exact pell2_forward c.toNat c rfl hc h
  · rintro ⟨n, rfl⟩; exact pellX_mem n

/-! ### A6-1 lower bound: `ExponentialInjection` and `LogLowerBound` -/

/-- A6-1 lower bound leaf: `S` carries an exponential injection (A = 1, B = 6). -/
theorem exponentialInjection_pell2 : ExponentialInjection pell2Set := by
  refine ⟨1, 6, pellX, by norm_num, by norm_num, pellX_strictMono.injective,
    fun n => pellX_mem n, ?_⟩
  intro n
  have h0 : (0 : ℤ) ≤ pellX n := le_trans (by norm_num) (pell_pos n).1
  rw [abs_of_nonneg h0]
  simpa using pellX_le_six_pow n

/-- A6-1 lower bound: `N_S(X) ≥ κ log X` for suitable `κ`. -/
theorem logLowerBound_pell2 : LogLowerBound pell2Set :=
  logLowerBound_of_exponentialInjection exponentialInjection_pell2

/-! ### A6-1 upper bound (sharpness): `N_S(X) ≤ 2·log₃ X + 3` -/

/-- A6-1 upper bound (the sharpness): `N_S(X) ≤ 2·log X / log 3 + 3` for `X ≥ 1`. Proved by descent,
NOT via mathlib's fundamental-unit theory. -/
theorem pell2_count_le (X : ℕ) (hX : 1 ≤ X) :
    (fiberCountZZ pell2Set X : ℝ) ≤ 2 * Real.log X / Real.log 3 + 3 := by
  classical
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set L := Nat.log 3 X with hLdef
  have hcard : fiberCountZZ pell2Set X ≤ 2 * (L + 1) := by
    unfold fiberCountZZ
    have hsub : (Finset.Icc (-(X : ℤ)) (X : ℤ)).filter (fun c => c ∈ pell2Set) ⊆
        (Finset.range (L + 1)).image (fun n => pellX n) ∪
          (Finset.range (L + 1)).image (fun n => -pellX n) := by
      intro c hc
      rw [Finset.mem_filter, Finset.mem_Icc] at hc
      obtain ⟨⟨hlo, hhi⟩, hmem⟩ := hc
      rcases lt_trichotomy c 0 with hneg | hzero | hpos
      · have hncmem : -c ∈ pell2Set := by
          obtain ⟨u, hu⟩ := hmem
          exact ⟨u, by rw [neg_sq]; exact hu⟩
        obtain ⟨n, hn⟩ := (pell2_pos_mem_iff (by linarith)).mp hncmem
        have h3 : (3 : ℤ) ^ n ≤ (X : ℤ) := by
          calc (3 : ℤ) ^ n ≤ pellX n := pellX_ge_pow n
            _ = -c := hn.symm
            _ ≤ (X : ℤ) := by linarith
        have hnat : (3 : ℕ) ^ n ≤ X := by exact_mod_cast h3
        have hnle : n ≤ L := Nat.le_log_of_pow_le (by norm_num) hnat
        rw [Finset.mem_union]; right; rw [Finset.mem_image]
        exact ⟨n, Finset.mem_range.mpr (by omega), by rw [← hn]; ring⟩
      · exfalso
        rw [hzero] at hmem
        obtain ⟨u, hu⟩ := hmem
        nlinarith [sq_nonneg u, hu]
      · obtain ⟨n, hn⟩ := (pell2_pos_mem_iff hpos).mp hmem
        have h3 : (3 : ℤ) ^ n ≤ (X : ℤ) := by
          calc (3 : ℤ) ^ n ≤ pellX n := pellX_ge_pow n
            _ = c := hn.symm
            _ ≤ (X : ℤ) := hhi
        have hnat : (3 : ℕ) ^ n ≤ X := by exact_mod_cast h3
        have hnle : n ≤ L := Nat.le_log_of_pow_le (by norm_num) hnat
        rw [Finset.mem_union]; left; rw [Finset.mem_image]
        exact ⟨n, Finset.mem_range.mpr (by omega), hn.symm⟩
    calc ((Finset.Icc (-(X : ℤ)) (X : ℤ)).filter (fun c => c ∈ pell2Set)).card
        ≤ ((Finset.range (L + 1)).image (fun n => pellX n) ∪
            (Finset.range (L + 1)).image (fun n => -pellX n)).card := Finset.card_le_card hsub
      _ ≤ ((Finset.range (L + 1)).image (fun n => pellX n)).card
            + ((Finset.range (L + 1)).image (fun n => -pellX n)).card := Finset.card_union_le _ _
      _ ≤ (Finset.range (L + 1)).card + (Finset.range (L + 1)).card :=
            Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * (L + 1) := by rw [Finset.card_range]; ring
  -- pass to the reals
  have hpow : 3 ^ L ≤ X := Nat.pow_log_le_self 3 (by omega)
  have hpowR : (3 : ℝ) ^ L ≤ (X : ℝ) := by exact_mod_cast hpow
  have hlogle : (L : ℝ) * Real.log 3 ≤ Real.log X := by
    have := Real.log_le_log (by positivity) hpowR
    rwa [Real.log_pow] at this
  have hLlog : (L : ℝ) ≤ Real.log X / Real.log 3 := by
    rw [le_div_iff₀ hlog3]; linarith
  have hfiber : (fiberCountZZ pell2Set X : ℝ) ≤ 2 * (L : ℝ) + 2 := by
    have h2 : (fiberCountZZ pell2Set X : ℝ) ≤ ((2 * (L + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at h2; linarith
  rw [mul_div_assoc]
  linarith [hLlog, hfiber]

/-! ## A6-2 : `E = {m | ∃ n, m = 2^(2ⁿ)}` -/

/-- The doubly-exponential tower set `E`. -/
def expTowerSet : Set ℤ := {m : ℤ | ∃ n : ℕ, m = 2 ^ (2 ^ n)}

/-- `n ≤ 2^(2ⁿ)` (used to bound the search window of the decision procedure). -/
theorem le_expTower_nat (n : ℕ) : n ≤ 2 ^ (2 ^ n) :=
  le_trans (Nat.lt_two_pow_self).le
    (Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le)

/-- A6-2(a): a computable decision procedure for membership in `E` (search only the `n` with
`2^(2ⁿ) ≤ m`, crudely bounded by `m.toNat`). Kept as a `def` rather than a global `instance` so it
does not clash with the `Classical`-instance filter baked into `fiberCountZZ`. -/
@[reducible] def E_decidable : DecidablePred (· ∈ expTowerSet) := fun m =>
  decidable_of_iff (m ∈ (Finset.range (m.toNat + 1)).image (fun n => (2 : ℤ) ^ (2 ^ n))) (by
    rw [Finset.mem_image]
    simp only [expTowerSet, Set.mem_setOf_eq, Finset.mem_range]
    constructor
    · rintro ⟨n, -, hn⟩; exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩
      subst hn
      refine ⟨n, ?_, rfl⟩
      have hnat : n ≤ 2 ^ (2 ^ n) := le_expTower_nat n
      have hcast : ((2 : ℤ) ^ (2 ^ n)).toNat = 2 ^ (2 ^ n) := by
        rw [show ((2 : ℤ) ^ (2 ^ n)) = ((2 ^ (2 ^ n) : ℕ) : ℤ) by push_cast; ring]
        exact Int.toNat_natCast _
      omega)

/-- The generator `n ↦ 2^(2ⁿ)` is injective. -/
theorem expTower_injective : Function.Injective (fun n : ℕ => (2 : ℤ) ^ (2 ^ n)) := by
  intro a b hab
  have h1 : 2 ^ a = 2 ^ b := Int.pow_right_injective (by norm_num) hab
  exact Nat.pow_right_injective (le_refl 2) h1

/-- `E` is infinite. -/
theorem expTowerSet_infinite : expTowerSet.Infinite :=
  Set.infinite_of_injective_forall_mem expTower_injective (fun n => ⟨n, rfl⟩)

/-- A6-2(b) exact count: `N_E(X) = log₂ log₂ X + 1` for `X ≥ 2`. The elements of `E` in `[−X,X]`
are exactly `2^(2ⁿ)` for `n ≤ log₂ log₂ X`. -/
theorem fiberCountZZ_expTower_eq (X : ℕ) (hX : 2 ≤ X) :
    fiberCountZZ expTowerSet X = Nat.log 2 (Nat.log 2 X) + 1 := by
  classical
  set L := Nat.log 2 (Nat.log 2 X) with hLdef
  have hLX : Nat.log 2 X ≠ 0 := by
    have : 0 < Nat.log 2 X := Nat.log_pos (by norm_num) hX
    omega
  unfold fiberCountZZ
  rw [← Finset.card_range (L + 1)]
  refine (Finset.card_bij (fun n _ => (2 : ℤ) ^ (2 ^ n)) ?_ ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_range] at hn
    have hnL : n ≤ L := by omega
    have hpow : (2 : ℕ) ^ (2 ^ n) ≤ X :=
      Nat.pow_le_of_le_log (by omega) (Nat.pow_le_of_le_log hLX hnL)
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨n, rfl⟩⟩
    · have h1 : (0 : ℤ) ≤ (2 : ℤ) ^ (2 ^ n) := by positivity
      have h2 : (0 : ℤ) ≤ (X : ℤ) := by positivity
      linarith
    · exact_mod_cast hpow
  · intro a _ b _ hab
    exact expTower_injective hab
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨_, hcX⟩, n, hn⟩ := hc
    have hpow : (2 : ℕ) ^ (2 ^ n) ≤ X := by
      have : (2 : ℤ) ^ (2 ^ n) ≤ (X : ℤ) := by rw [← hn]; exact hcX
      exact_mod_cast this
    have hstep : 2 ^ n ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by norm_num) hpow
    have hnL : n ≤ L := Nat.le_log_of_pow_le (by norm_num) hstep
    exact ⟨n, Finset.mem_range.mpr (by omega), hn.symm⟩

/-- A6-2(b) upper bound: `N_E(X) ≤ log₂ log₂ X + 2`. -/
theorem fiberCountZZ_expTower_le (X : ℕ) (hX : 2 ≤ X) :
    fiberCountZZ expTowerSet X ≤ Nat.log 2 (Nat.log 2 X) + 2 := by
  rw [fiberCountZZ_expTower_eq X hX]; omega

/-- A6-2(b) lower bound: `log₂ log₂ X ≤ N_E(X)`. -/
theorem fiberCountZZ_expTower_ge (X : ℕ) (hX : 2 ≤ X) :
    Nat.log 2 (Nat.log 2 X) ≤ fiberCountZZ expTowerSet X := by
  rw [fiberCountZZ_expTower_eq X hX]; omega

/-! ### A growth lemma: `m + 2 < κ·2^m·log 2` eventually -/

/-- For every `κ > 0` and every `N`, some `m ≥ N` beats the linear term: `m + 2 < κ·2^m·log 2`.
Proof: `2^m = exp(m log 2) ≥ (m log2 / 2 + 1)² ≥ (m log2)²/4`, a quadratic in `m`. -/
theorem exists_growth (κ : ℝ) (hκ : 0 < κ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ (m : ℝ) + 2 < κ * 2 ^ m * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set d : ℝ := κ * Real.log 2 ^ 3 / 4 with hd
  have hd0 : 0 < d := by
    rw [hd]; exact div_pos (mul_pos hκ (pow_pos hlog2 3)) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((3 : ℝ) / d) (N : ℝ))
  have hm3 : (3 : ℝ) / d < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hmN : (N : ℝ) < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have h3d : (0 : ℝ) < 3 / d := div_pos (by norm_num) hd0
  have hmpos : 0 < m := by exact_mod_cast lt_trans h3d hm3
  have hdm : 3 < d * (m : ℝ) := by
    have := (div_lt_iff₀ hd0).mp hm3; linarith
  have hy : 0 ≤ (m : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg m) hlog2.le
  have e2m : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hhalf : (2 : ℝ) ^ m = (Real.exp ((m : ℝ) * Real.log 2 / 2)) ^ 2 := by
    rw [e2m, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hb1 : (m : ℝ) * Real.log 2 / 2 + 1 ≤ Real.exp ((m : ℝ) * Real.log 2 / 2) :=
    Real.add_one_le_exp _
  have ha0 : (0 : ℝ) ≤ (m : ℝ) * Real.log 2 / 2 + 1 := by linarith
  have hfinal : ((m : ℝ) * Real.log 2 / 2 + 1) ^ 2 ≤ (2 : ℝ) ^ m := by
    rw [hhalf]; exact pow_le_pow_left₀ ha0 hb1 2
  have hquad : ((m : ℝ) * Real.log 2) ^ 2 / 4 ≤ (2 : ℝ) ^ m := by
    have hexp : ((m : ℝ) * Real.log 2) ^ 2 / 4 ≤ ((m : ℝ) * Real.log 2 / 2 + 1) ^ 2 := by
      nlinarith [hy]
    linarith
  have hmul : κ * Real.log 2 * (((m : ℝ) * Real.log 2) ^ 2 / 4) ≤ κ * Real.log 2 * (2 : ℝ) ^ m :=
    mul_le_mul_of_nonneg_left hquad (mul_nonneg hκ.le hlog2.le)
  have hLHS : κ * Real.log 2 * (((m : ℝ) * Real.log 2) ^ 2 / 4) = d * (m : ℝ) ^ 2 := by
    rw [hd]; ring
  have hRHS : κ * Real.log 2 * (2 : ℝ) ^ m = κ * 2 ^ m * Real.log 2 := by ring
  have hstep : d * (m : ℝ) ^ 2 ≤ κ * 2 ^ m * Real.log 2 := by rw [← hLHS, ← hRHS]; exact hmul
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
  have hh : (0 : ℝ) < (d * (m : ℝ) - 3) * (m : ℝ) := mul_pos (by linarith) (by linarith)
  have hdm2 : 3 * (m : ℝ) < d * (m : ℝ) ^ 2 := by nlinarith [hh]
  refine ⟨m, by exact_mod_cast hmN.le, ?_⟩
  have hlin : (m : ℝ) + 2 ≤ 3 * (m : ℝ) := by linarith
  linarith [hstep, hdm2, hlin]

/-! ### A6-3 : `E` is not a quadratic fibre (conditional on `FixedAPPrimeLowerBound`) -/

/-- A6-3: no quadratic fibre equals `E`. The log barrier gives `κ log X ≤ N_E(X) ≤ log₂log₂X + 2`
for all large `X`; specialising to `X = 2^(2^m)` forces `κ·2^m·log 2 ≤ m + 2`, contradicted by
`exists_growth`. The hypothesis `hAP : FixedAPPrimeLowerBound` is explicit in the type. -/
theorem E_not_quadratic_fiber (hAP : FixedAPPrimeLowerBound) :
    ∀ (n r : ℕ) (P : Poly (n + 1) r) (_ : P.totalDegree ≤ 2) (a : Fin n → ℤ),
      fiberZZ P a ≠ expTowerSet := by
  intro n r P hP a hEq
  rcases logBarrier_of_quadratic hAP P hP a with hbdd | hlog
  · obtain ⟨B, hB⟩ := hbdd
    rw [hEq] at hB
    have hfin : expTowerSet.Finite := by
      apply Set.Finite.subset (Set.finite_Icc (-(B : ℤ)) (B : ℤ))
      intro c hc
      rw [Set.mem_Icc]; exact abs_le.mp (hB c hc)
    exact expTowerSet_infinite hfin
  · rw [hEq] at hlog
    obtain ⟨κ, X₀, hκ, hX₀, hbound⟩ := hlog
    obtain ⟨m, hmN, hgrow⟩ := exists_growth κ hκ X₀
    set Xm : ℕ := 2 ^ (2 ^ m) with hXm
    have hXmX₀ : X₀ ≤ Xm := by
      rw [hXm]
      calc X₀ ≤ m := hmN
        _ ≤ 2 ^ m := (Nat.lt_two_pow_self).le
        _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le
    have hXm2 : 2 ≤ Xm := by
      rw [hXm]; exact Nat.le_self_pow (pow_ne_zero m (by norm_num)) 2
    have hb := hbound Xm hXmX₀
    have hcount := fiberCountZZ_expTower_le Xm hXm2
    have hLm : Nat.log 2 (Nat.log 2 Xm) = m := by
      rw [hXm, Nat.log_pow (show (1 : ℕ) < 2 by norm_num), Nat.log_pow (show (1 : ℕ) < 2 by norm_num)]
    rw [hLm] at hcount
    have hlogXm : Real.log (Xm : ℝ) = (2 : ℝ) ^ m * Real.log 2 := by
      rw [hXm]; push_cast; rw [Real.log_pow]; push_cast; ring
    have hR : κ * Real.log (Xm : ℝ) ≤ (m : ℝ) + 2 := by
      calc κ * Real.log (Xm : ℝ) ≤ (fiberCountZZ expTowerSet Xm : ℝ) := hb
        _ ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hcount
        _ = (m : ℝ) + 2 := by push_cast; ring
    rw [hlogXm] at hR
    have hcontra : κ * 2 ^ m * Real.log 2 ≤ (m : ℝ) + 2 := by
      have heq : κ * 2 ^ m * Real.log 2 = κ * ((2 : ℝ) ^ m * Real.log 2) := by ring
      rw [heq]; exact hR
    linarith [hgrow, hcontra]

/-! ### A6-4 : the separator -/

/-- A6-4: any infinite `S` whose count dips below every `κ log X` infinitely often is not a quadratic
fibre. The log barrier makes `κ log X ≤ N_S(X)` eventually; the sub-log hypothesis contradicts it at
a frequent point. `hAP : FixedAPPrimeLowerBound` is explicit in the type. -/
theorem not_quadratic_fiber_of_sublog (hAP : FixedAPPrimeLowerBound) (S : Set ℤ)
    (hinf : S.Infinite)
    (hsub : ∀ κ : ℝ, 0 < κ →
      ∃ᶠ X : ℕ in Filter.atTop, (fiberCountZZ S X : ℝ) < κ * Real.log X) :
    ∀ (n r : ℕ) (P : Poly (n + 1) r) (_ : P.totalDegree ≤ 2) (a : Fin n → ℤ),
      fiberZZ P a ≠ S := by
  intro n r P hP a hEq
  rcases logBarrier_of_quadratic hAP P hP a with hbdd | hlog
  · obtain ⟨B, hB⟩ := hbdd
    rw [hEq] at hB
    have hfin : S.Finite := by
      apply Set.Finite.subset (Set.finite_Icc (-(B : ℤ)) (B : ℤ))
      intro c hc
      rw [Set.mem_Icc]; exact abs_le.mp (hB c hc)
    exact hinf hfin
  · rw [hEq] at hlog
    obtain ⟨κ, X₀, hκ, hX₀, hbound⟩ := hlog
    have hfreq := hsub κ hκ
    have hev : ∀ᶠ X : ℕ in Filter.atTop, X₀ ≤ X := Filter.eventually_atTop.2 ⟨X₀, fun X h => h⟩
    obtain ⟨X, hlt, hge⟩ := (hfreq.and_eventually hev).exists
    have hb := hbound X hge
    linarith [hb, hlt]

/-! ### CONTROLS : the descent on the standard chain `(17,12) → (3,2) → (1,0)` -/

/-- The descent `(c,v) ↦ (3c−4v, 3v−2c)` sends `(17,12) ↦ (3,2)`. -/
example : (3 * 17 - 4 * 12 : ℤ) = 3 ∧ (3 * 12 - 2 * 17 : ℤ) = 2 := by norm_num

/-- …and `(3,2) ↦ (1,0)`. -/
example : (3 * 3 - 4 * 2 : ℤ) = 1 ∧ (3 * 2 - 2 * 3 : ℤ) = 0 := by norm_num

/-- The orbit realises the chain: `X₂ = 17`, `U₂ = 12`, matching `17² − 2·12² = 1`. -/
example : pellX 2 = 17 ∧ pellU 2 = 12 := by decide

/-- `17` is a Pell-`2` solution and, by the descent, equals `X₂`. -/
example : (17 : ℤ) ∈ pell2Set ∧ (17 : ℤ) = pellX 2 :=
  ⟨⟨12, by norm_num⟩, by decide⟩

end DiophCompression.ResearchUpgrade
