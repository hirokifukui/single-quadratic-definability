/-
  NonResidue.lean — Gate-20 Packet N1, closing the last open leaf `NonResidueClass` of N1.1b.

  Main results (namespace `DiophCompression.ResearchUpgrade`):

  * `exists_large_nonresidue_prime` : a non-(rational-)square integer `n` is a quadratic
    non-residue at arbitrarily large primes, i.e. for every `N` there is a prime `p > N`
    with `jacobiSym n p = -1`.
  * `nonResidueClass_holds` : hence `NonResidueClass` (declared in
    `CharacterSeparationReduction.lean`) holds unconditionally.

  Mathematical route (classical):
    1. Reduce `n = b^2 * s` with `s` the (signed) squarefree part (`Nat.sq_mul_squarefree`);
       squares drop out of the Jacobi symbol, so `J(n | r) = J(s | r)` for `r` coprime to `n`.
    2. If `s` has an odd prime factor `q₁`, use quadratic reciprocity: build a residue class
       `r ≡ (nonresidue) (mod q₁)`, `r ≡ 1 (mod 8)`, `r ≡ 1 (mod other odd primes)` by CRT,
       so `J(s | r) = J(q₁ | r) · J(s/q₁ | r) = (-1)·(+1) = -1`.
    3. Otherwise `s ∈ {-1, 2, -2}`; use the supplementary laws (`χ₄`, `χ₈`, `χ₈'`) with
       `r ≡ 3` or `5 (mod 8)`.
    4. Dirichlet on primes in arithmetic progressions (`Nat.forall_exists_prime_gt_and_eq_mod`)
       produces a prime `p > N` in that class, and `jacobiSym.mod_right` transfers the value.

  Claim tags: [P] (std-3).  Baseline read-only; imports `CharacterSeparationReduction`.
-/
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.SetNotationForOrder
import ResearchUpgrade.CharacterSeparationReduction

open scoped NumberTheorySymbols

namespace DiophCompression.ResearchUpgrade

-- Helper 1: nonresidue existence
theorem exists_nat_nonresidue (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    ∃ c : ℕ, Nat.Coprime c q ∧ jacobiSym (c : ℤ) q = -1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n q]; exact hq2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod q) hchar
  have ha0 : a ≠ 0 := by rintro rfl; exact ha IsSquare.zero
  have hcast : ((a.val : ℤ) : ZMod q) = a := by
    push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
  have hunit : IsUnit a := isUnit_iff_ne_zero.mpr ha0
  refine ⟨a.val, ?_, ?_⟩
  · have : IsUnit ((a.val : ℕ) : ZMod q) := by
      rw [show ((a.val : ℕ) : ZMod q) = a from by exact_mod_cast hcast]; exact hunit
    exact (ZMod.isUnit_iff_coprime a.val q).mp this
  · rw [← jacobiSym.legendreSym.to_jacobiSym q (a.val : ℤ), legendreSym.eq_neg_one_iff, hcast]
    exact ha

-- Helper 2: split modulus D = q^i * (2^j * W), with W odd, coprime to q, absorbing all odd-coprime divisors
theorem split_modulus (D q : ℕ) (hq : q.Prime) (hD : D ≠ 0) :
    ∃ W : ℕ, Nat.Coprime q W ∧ Odd W ∧
      (∀ m : ℕ, m ∣ D → Nat.Coprime m q → Odd m → m ∣ W) ∧
      (∃ i j : ℕ, D = q ^ i * (2 ^ j * W)) := by
  set i := D.factorization q with hi
  set C := D / q ^ i with hC
  have hDeq : D = q ^ i * C := (Nat.ordProj_mul_ordCompl_eq_self D q).symm
  have hcopqC : Nat.Coprime q C := Nat.coprime_ordCompl hq hD
  have hCne : C ≠ 0 := by intro h; rw [h, Nat.mul_zero] at hDeq; exact hD hDeq
  set j := C.factorization 2 with hj
  set W := C / 2 ^ j with hW
  have hCeq : C = 2 ^ j * W := (Nat.ordProj_mul_ordCompl_eq_self C 2).symm
  have hcop2W : Nat.Coprime 2 W := Nat.coprime_ordCompl Nat.prime_two hCne
  have hWC : W ∣ C := Nat.ordCompl_dvd C 2
  refine ⟨W, hcopqC.coprime_dvd_right hWC, Nat.coprime_two_left.mp hcop2W, ?_, i, j, ?_⟩
  · intro m hmD hmq hmodd
    have hmC : m ∣ C := by
      rw [hDeq] at hmD
      exact (Nat.Coprime.pow_right _ hmq).dvd_of_dvd_mul_left hmD
    rw [hCeq] at hmC
    exact (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hmodd)).dvd_of_dvd_mul_left hmC
  · rw [hDeq, hCeq]

-- The key existence lemma (a non-square integer is a non-residue on a unit residue class)
theorem exists_nonresidue_witness (n : ℤ) (hn : ¬ ∃ h : ℚ, (n : ℚ) = h ^ 2) :
    ∃ r : ℕ, Odd r ∧ Nat.Coprime r (4 * n.natAbs) ∧ jacobiSym n r = -1 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn ⟨0, by norm_num⟩
  set D := n.natAbs with hDdef
  have hD0 : 0 < D := Int.natAbs_pos.mpr hn0
  have hDne : D ≠ 0 := hD0.ne'
  obtain ⟨a, b, hab, hsqf⟩ := Nat.sq_mul_squarefree D
  have ha0 : a ≠ 0 := hsqf.ne_zero
  have hb0 : b ≠ 0 := by rintro rfl; rw [pow_two, zero_mul, zero_mul] at hab; omega
  set s : ℤ := n.sign * (a : ℤ) with hsdef
  have hcast : (b : ℤ) ^ 2 * (a : ℤ) = (D : ℤ) := by rw [← hab]; push_cast; ring
  have hns : (n : ℤ) = (b : ℤ) ^ 2 * s := by
    have h : (b : ℤ) ^ 2 * s = n := by
      rw [hsdef, show (b:ℤ)^2 * (n.sign * a) = n.sign * ((b:ℤ)^2 * a) from by ring,
        hcast, Int.sign_mul_natAbs]
    exact h.symm
  have hsna : s.natAbs = a := by
    rw [hsdef, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn0, Int.natAbs_natCast, one_mul]
  have hbD : b ∣ D := ⟨b * a, by rw [← hab]; ring⟩
  have haD : a ∣ D := ⟨b ^ 2, by rw [← hab]; ring⟩
  have hval : ∀ r : ℕ, Nat.Coprime r D → jacobiSym n r = jacobiSym s r := by
    intro r hr
    have hbr : Nat.Coprime b r := (hr.coprime_dvd_right hbD).symm
    rw [hns, jacobiSym.mul_left,
      jacobiSym.sq_one' (by rw [Int.gcd_natCast_natCast]; exact hbr), one_mul]
  have hcop4 : ∀ r : ℕ, Odd r → Nat.Coprime r D → Nat.Coprime r (4 * D) := by
    intro r hro hrD
    have h2 : Nat.Coprime r 2 := Nat.coprime_two_right.mpr hro
    have h4 : Nat.Coprime r 4 := by
      have e : (4:ℕ) = 2 ^ 2 := by norm_num
      rw [e]; exact Nat.Coprime.pow_right 2 h2
    exact Nat.Coprime.mul_right h4 hrD
  by_cases hcase : ∃ q ∈ a.primeFactors, q ≠ 2
  · -- CASE 1
    obtain ⟨q, hqmem, hq2⟩ := hcase
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqodd : Odd q := hq.odd_of_ne_two hq2
    have hqa : q ∣ a := Nat.dvd_of_mem_primeFactors hqmem
    have hqs : (q : ℤ) ∣ s := by
      have hqa' : q ∣ s.natAbs := by rw [hsna]; exact hqa
      exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hqa')
    obtain ⟨s', hs'⟩ := hqs
    have hs'0 : s' ≠ 0 := by
      rintro rfl; rw [mul_zero] at hs'
      rw [hs'] at hsna; simp only [Int.natAbs_zero] at hsna; omega
    have haqt : a = q * s'.natAbs := by
      have h1 : s.natAbs = ((q:ℤ) * s').natAbs := by rw [hs']
      rw [hsna, Int.natAbs_mul, Int.natAbs_natCast] at h1; exact h1
    obtain ⟨c, hcq, hjc⟩ := exists_nat_nonresidue q hq hq2
    obtain ⟨W, hqW, hWodd, hLW, i, j, hDsplit⟩ := split_modulus D q hq hDne
    let cr1 := Nat.chineseRemainder hqW c 1
    set r1 := cr1.val with hr1def
    have hr1q : r1 ≡ c [MOD q] := cr1.2.1
    have hr1W : r1 ≡ 1 [MOD W] := cr1.2.2
    have hcop8qW : Nat.Coprime 8 (q * W) := by
      have h8q : Nat.Coprime 8 q := by
        have h : Nat.Coprime (2 ^ 3) q :=
          Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega))
        simpa using h
      have h8W : Nat.Coprime 8 W := by
        have h : Nat.Coprime (2 ^ 3) W := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hWodd)
        simpa using h
      exact Nat.Coprime.mul_right h8q h8W
    let cr2 := Nat.chineseRemainder hcop8qW 1 r1
    set r := cr2.val with hrdef
    have hr8 : r ≡ 1 [MOD 8] := cr2.2.1
    have hrqW : r ≡ r1 [MOD q * W] := cr2.2.2
    have hrq : r ≡ c [MOD q] := (hrqW.of_dvd (dvd_mul_right q W)).trans hr1q
    have hrW : r ≡ 1 [MOD W] := (hrqW.of_dvd (dvd_mul_left W q)).trans hr1W
    have hr8v : r % 8 = 1 := by have h := hr8; unfold Nat.ModEq at h; omega
    have hro : Odd r := by rw [Nat.odd_iff]; omega
    have hr4 : r % 4 = 1 := by omega
    have hrcq : Nat.Coprime r q := (Nat.ModEq.gcd_eq hrq).trans hcq
    have hrcW : Nat.Coprime r W := by
      have h : Nat.gcd r W = Nat.gcd 1 W := Nat.ModEq.gcd_eq hrW
      rw [Nat.gcd_one_left] at h; exact h
    have hrc2 : Nat.Coprime r 2 := Nat.coprime_two_right.mpr hro
    have hrD : Nat.Coprime r D := by
      rw [hDsplit]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hrcq)
        (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hrc2) hrcW)
    refine ⟨r, hro, hcop4 r hro hrD, ?_⟩
    rw [hval r hrD, hs', jacobiSym.mul_left]
    have hJq : jacobiSym (q : ℤ) r = -1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' hqodd hr4]
      rw [jacobiSym.mod_left' (a₁ := (r:ℤ)) (a₂ := (c:ℤ)) (b := q) ?_]
      · exact hjc
      · have h : r % q = c % q := hrq
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        rwa [Int.natCast_mod, Int.natCast_mod] at h2
    have hJs' : jacobiSym s' r = 1 := by
      rw [jacobiSym.mod_right s' hro]
      set t := s'.natAbs with htdef
      have ht0 : t ≠ 0 := by rw [htdef]; exact Int.natAbs_ne_zero.mpr hs'0
      have hta : t ∣ a := ⟨q, by rw [haqt]; ring⟩
      have htq : Nat.Coprime t q := by
        rcases Nat.coprime_or_dvd_of_prime hq t with h | h
        · exact h.symm
        · exfalso
          obtain ⟨u, hu⟩ := h
          have hqq : q * q ∣ a := ⟨u, by rw [haqt, hu]; ring⟩
          have := hsqf q hqq
          rw [Nat.isUnit_iff] at this
          have := hq.two_le; omega
      set e := t.factorization 2 with hedef
      set t0 := t / 2 ^ e with ht0def
      have hteq : t = 2 ^ e * t0 := (Nat.ordProj_mul_ordCompl_eq_self t 2).symm
      have hto_odd : Odd t0 := Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two ht0)
      have htoW : t0 ∣ W := by
        apply hLW
        · exact (Nat.ordCompl_dvd t 2).trans (hta.trans haD)
        · exact Nat.Coprime.coprime_dvd_left (Nat.ordCompl_dvd t 2) htq
        · exact hto_odd
      have he1 : e ≤ 1 := by
        have hts : Squarefree t := hsqf.squarefree_of_dvd hta
        exact (Nat.squarefree_iff_factorization_le_one ht0).mp hts 2
      have h4t8W : 4 * t ∣ 8 * W := by
        rw [hteq]
        have h1 : 4 * (2 ^ e * t0) = 2 ^ (e + 2) * t0 := by rw [pow_add]; ring
        rw [h1]
        have hp : (2:ℕ) ^ (e + 2) ∣ 2 ^ 3 := Nat.pow_dvd_pow 2 (by omega)
        calc 2 ^ (e + 2) * t0 ∣ 2 ^ 3 * W := Nat.mul_dvd_mul hp htoW
          _ = 8 * W := by norm_num
      have hr8W : r ≡ 1 [MOD 8 * W] :=
        (Nat.modEq_and_modEq_iff_modEq_mul (by
          have h : Nat.Coprime (2 ^ 3) W := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hWodd)
          simpa using h)).mp ⟨hr8, hrW⟩
      have hr4t : r ≡ 1 [MOD 4 * t] := hr8W.of_dvd h4t8W
      have hmod1 : r % (4 * t) = 1 := by
        have h1lt : 1 < 4 * t := by omega
        have h := hr4t; unfold Nat.ModEq at h
        rw [Nat.mod_eq_of_lt h1lt] at h; exact h
      rw [hmod1]; exact jacobiSym.one_right s'
    rw [hJq, hJs']; ring
  · -- CASE B
    simp only [not_exists, not_and, not_ne_iff] at hcase
    have ha2 : a ∣ 2 := by
      have hsub : a.primeFactors ⊆ ({2} : Finset ℕ) := by
        intro q hq; rw [Finset.mem_singleton]; exact hcase q hq
      have hp := Nat.prod_primeFactors_of_squarefree hsqf
      calc a = ∏ p ∈ a.primeFactors, p := hp.symm
        _ ∣ ∏ p ∈ ({2} : Finset ℕ), p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
        _ = 2 := by simp
    have haval : a = 1 ∨ a = 2 := (Nat.dvd_prime Nat.prime_two).mp ha2
    have hsval : s = -1 ∨ s = 2 ∨ s = -2 := by
      have hsn : s.natAbs = a := hsna
      have hs_ne1 : s ≠ 1 := by
        intro heq
        rw [heq, mul_one] at hns
        exact hn ⟨(b:ℚ), by rw [hns]; push_cast; ring⟩
      rcases haval with h1 | h2
      · rw [h1] at hsn
        rcases Int.natAbs_eq_iff.mp hsn with h | h
        · exact absurd (by simpa using h) hs_ne1
        · left; simpa using h
      · rw [h2] at hsn
        rcases Int.natAbs_eq_iff.mp hsn with h | h
        · right; left; simpa using h
        · right; right; simpa using h
    set k := D.factorization 2 with hkdef
    set W := D / 2 ^ k with hWdef
    have hDeqB : D = 2 ^ k * W := (Nat.ordProj_mul_ordCompl_eq_self D 2).symm
    have hcop2W : Nat.Coprime 2 W := Nat.coprime_ordCompl Nat.prime_two hDne
    have hWodd : Odd W := Nat.coprime_two_left.mp hcop2W
    have hcop8W : Nat.Coprime 8 W := by
      have h : Nat.Coprime (2 ^ 3) W := Nat.Coprime.pow_left 3 hcop2W
      simpa using h
    have build : ∀ σ : ℕ, σ % 2 = 1 → σ < 8 →
        ∃ r : ℕ, Odd r ∧ Nat.Coprime r (4 * D) ∧ r % 8 = σ ∧ Nat.Coprime r D := by
      intro σ hσ2 hσ8
      let cr := Nat.chineseRemainder hcop8W σ 1
      set r := cr.val with hrdef
      have hr8 : r ≡ σ [MOD 8] := cr.2.1
      have hrW : r ≡ 1 [MOD W] := cr.2.2
      have hr8v : r % 8 = σ := by
        have h := hr8; unfold Nat.ModEq at h; rw [Nat.mod_eq_of_lt hσ8] at h; exact h
      have hro : Odd r := by rw [Nat.odd_iff]; omega
      have hrcW : Nat.Coprime r W := by
        have h : Nat.gcd r W = Nat.gcd 1 W := Nat.ModEq.gcd_eq hrW
        rw [Nat.gcd_one_left] at h; exact h
      have hrc2 : Nat.Coprime r 2 := Nat.coprime_two_right.mpr hro
      have hrD : Nat.Coprime r D := by
        rw [hDeqB]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hrc2) hrcW
      exact ⟨r, hro, hcop4 r hro hrD, hr8v, hrD⟩
    rcases hsval with h | h | h
    · obtain ⟨r, hro, hr4D, hr8v, hrD⟩ := build 3 (by norm_num) (by norm_num)
      refine ⟨r, hro, hr4D, ?_⟩
      rw [hval r hrD, h, jacobiSym.at_neg_one hro, ZMod.χ₄_nat_three_mod_four (by omega)]
    · obtain ⟨r, hro, hr4D, hr8v, hrD⟩ := build 3 (by norm_num) (by norm_num)
      refine ⟨r, hro, hr4D, ?_⟩
      rw [hval r hrD, h, jacobiSym.at_two hro, ZMod.χ₈_nat_eq_if_mod_eight,
        if_neg (by omega), if_neg (by omega)]
    · obtain ⟨r, hro, hr4D, hr8v, hrD⟩ := build 5 (by norm_num) (by norm_num)
      refine ⟨r, hro, hr4D, ?_⟩
      rw [hval r hrD, h, jacobiSym.at_neg_two hro, ZMod.χ₈'_nat_eq_if_mod_eight,
        if_neg (by omega), if_neg (by omega)]

theorem exists_large_nonresidue_prime (n : ℤ) (hn : ¬ ∃ h : ℚ, (n : ℚ) = h ^ 2) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ jacobiSym n p = -1 := by
  obtain ⟨r, hro, hrcop, hjr⟩ := exists_nonresidue_witness n hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn ⟨0, by norm_num⟩
  set Q := 4 * n.natAbs with hQ
  have hQ0 : Q ≠ 0 := by rw [hQ]; have := Int.natAbs_pos.mpr hn0; omega
  haveI : NeZero Q := ⟨hQ0⟩
  have hunit : IsUnit ((r : ZMod Q)) := by rw [ZMod.isUnit_iff_coprime]; exact hrcop
  obtain ⟨p, hpN, hpp, hpr⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit N
  refine ⟨p, hpN, hpp, ?_⟩
  have hpmod : p ≡ r [MOD Q] := (ZMod.natCast_eq_natCast_iff p r Q).mp hpr
  have hpcop : Nat.Coprime p Q := (Nat.ModEq.gcd_eq hpmod).trans hrcop
  have hpodd : Odd p := by
    rcases hpp.eq_two_or_odd' with h2 | hodd
    · exfalso
      have h2Q : (2:ℕ) ∣ Q := ⟨2 * n.natAbs, by rw [hQ]; ring⟩
      have h2p : (2:ℕ) ∣ p := ⟨1, by omega⟩
      have hd : (2:ℕ) ∣ Nat.gcd p Q := Nat.dvd_gcd h2p h2Q
      have hg : Nat.gcd p Q = 1 := hpcop
      rw [hg] at hd; omega
    · exact hodd
  have hmod : p % (4 * n.natAbs) = r % (4 * n.natAbs) := by
    have h := hpmod; unfold Nat.ModEq at h; rwa [hQ] at h
  calc jacobiSym n p = jacobiSym n (p % (4 * n.natAbs)) := jacobiSym.mod_right n hpodd
    _ = jacobiSym n (r % (4 * n.natAbs)) := by rw [hmod]
    _ = jacobiSym n r := (jacobiSym.mod_right n hro).symm
    _ = -1 := hjr

theorem nonResidueClass_holds : NonResidueClass := by
  intro n M hM0 _ _ hnsq
  obtain ⟨p, hpM, hpp, hjp⟩ := exists_large_nonresidue_prime n hnsq M
  have hcop : Nat.Coprime p M := by
    rw [Nat.Prime.coprime_iff_not_dvd hpp]
    intro hpdvd
    have := Nat.le_of_dvd hM0 hpdvd
    omega
  exact ⟨p, hcop, hjp⟩

end DiophCompression.ResearchUpgrade
