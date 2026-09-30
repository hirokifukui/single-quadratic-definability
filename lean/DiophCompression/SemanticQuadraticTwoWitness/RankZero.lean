/-
  DiophCompression/SemanticQuadraticTwoWitness/RankZero.lean — rank-0 witness block (2W swarm 2026-08-27 worker W1,
  PASS 484s; re-audited by claude.ai s8: statement verbatim = frozen f396a2da, proof read in full). Body verbatim
  from the swarm file (md5 of the swarm copy in certificates/session8_20260827); only this header comment added.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Bridge2W
import DiophCompression.SemanticQuadratic.FiberDichotomy
namespace DiophCompression.SemanticQuadraticTwoWitness
open DiophCompression.SemanticQuadraticGeneral

open DiophCompression.SemanticQuadratic (fiberSet fq Dichotomy fbound fiber_dichotomy)

/-- Values representable as `u*a + v*b` are exactly the multiples of `gcd a b`. -/
theorem repr_iff (a b w : ℤ) :
    (∃ u v : ℤ, u * a + v * b = w) ↔ (↑(Int.gcd a b) : ℤ) ∣ w := by
  constructor
  · rintro ⟨u, v, rfl⟩
    exact dvd_add (Dvd.dvd.mul_left (Int.gcd_dvd_left a b) u)
      (Dvd.dvd.mul_left (Int.gcd_dvd_right a b) v)
  · rintro ⟨k, rfl⟩
    refine ⟨Int.gcdA a b * k, Int.gcdB a b * k, ?_⟩
    have h := Int.gcd_eq_gcd_ab a b
    rw [h]; ring

/-- `gcd` is bounded by the sum of absolute values. -/
theorem gcd_le_abs_add (m₁ m₂ : ℤ) : (↑(Int.gcd m₁ m₂) : ℤ) ≤ |m₁| + |m₂| := by
  have hg : Int.gcd m₁ m₂ ≤ m₁.natAbs + m₂.natAbs := by
    rcases Nat.eq_zero_or_pos m₁.natAbs with h | h
    · have : Int.gcd m₁ m₂ = m₂.natAbs := by
        simp only [Int.gcd, h, Nat.gcd_zero_left]
      omega
    · exact le_trans (Nat.le_of_dvd h (Nat.gcd_dvd_left _ _)) (Nat.le_add_right _ _)
  rw [Int.abs_eq_natAbs m₁, Int.abs_eq_natAbs m₂]
  exact_mod_cast hg

/-- Case (a): `B₁ = B₂ = 0`.  The fiber reduces to the one-witness rank-0 fiber
    `fiberSet A 0 0 l (gcd m₁ m₂) q`. -/
theorem rank_zero_caseA (A : ℤ) : Dichotomy2 A 0 0 0 0 0 := by
  obtain ⟨K, hK⟩ := fiber_dichotomy A 0 0
  refine ⟨K, fun l m₁ m₂ q => ?_⟩
  set g : ℤ := (↑(Int.gcd m₁ m₂) : ℤ) with hgdef
  have hset : fiberSet2 A 0 0 0 0 0 l m₁ m₂ q = fiberSet A 0 0 l g q := by
    ext c
    simp only [fiberSet2, fiberSet, fq2, fq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, h⟩
      have hd : g ∣ (A * (c:ℤ) ^ 2 + l * c + q) := by
        rw [hgdef, ← repr_iff]
        exact ⟨-u, -v, by linear_combination -h⟩
      obtain ⟨k, hk⟩ := hd
      exact ⟨-k, by linear_combination hk⟩
    · rintro ⟨u, h⟩
      have hd : g ∣ (A * (c:ℤ) ^ 2 + l * c + q) := ⟨-u, by linear_combination h⟩
      rw [hgdef, ← repr_iff] at hd
      obtain ⟨u', v', hk⟩ := hd
      exact ⟨-u', -v', by linear_combination -hk⟩
  rw [hset]
  rcases hK l g q with hinf | hbd
  · exact Or.inl hinf
  · refine Or.inr (fun c hc => le_trans (hbd c hc) ?_)
    have hgle : |g| ≤ |m₁| + |m₂| := by
      rw [hgdef, abs_of_nonneg (by positivity)]
      exact gcd_le_abs_add m₁ m₂
    have h1 : (1 + |l| + |g|) ≤ (1 + |l| + |m₁| + |m₂|) := by linarith
    have h2 : (0:ℤ) ≤ 1 + |l| + |g| := by positivity
    have hsq : (1 + |l| + |g|) ^ 2 ≤ (1 + |l| + |m₁| + |m₂|) ^ 2 := by nlinarith
    simp only [fbound, fbound2]
    have hKnn : (0:ℤ) ≤ (K:ℤ) := by positivity
    nlinarith [abs_nonneg q, hsq]

/-- Shift lemma for the reduced predicate: from a solution at `c₁` build one at `c₂`
    whenever `m''` divides the relevant increments. -/
theorem shift_pred (A B l m' m'' q c₁ c₂ : ℤ)
    (hd1 : m'' ∣ (B * c₂ - B * c₁))
    (hd2 : m'' ∣ ((A * c₂ ^ 2 + l * c₂) - (A * c₁ ^ 2 + l * c₁)))
    (h : ∃ s r : ℤ, s * (B * c₁ + m') + r * m'' = -(A * c₁ ^ 2 + l * c₁ + q)) :
    ∃ s r : ℤ, s * (B * c₂ + m') + r * m'' = -(A * c₂ ^ 2 + l * c₂ + q) := by
  obtain ⟨s, r, h⟩ := h
  obtain ⟨k1, hk1⟩ := hd1
  obtain ⟨k2, hk2⟩ := hd2
  exact ⟨s, r - s * k1 - k2, by linear_combination h + s * hk1 + hk2⟩

set_option maxHeartbeats 1600000 in
/-- Case (b): `(B₁, B₂) ≠ (0, 0)`. -/
theorem rank_zero_caseB (A B₁ B₂ : ℤ) (hB : ¬ (B₁ = 0 ∧ B₂ = 0)) :
    Dichotomy2 A B₁ B₂ 0 0 0 := by
  have hBpos : 0 < Int.gcd B₁ B₂ := by
    rcases Nat.eq_zero_or_pos (Int.gcd B₁ B₂) with h | h
    · exfalso; apply hB
      exact ⟨Int.natAbs_eq_zero.mp (Nat.eq_zero_of_gcd_eq_zero_left h),
        Int.natAbs_eq_zero.mp (Nat.eq_zero_of_gcd_eq_zero_right h)⟩
    · exact h
  obtain ⟨g, b₁, b₂, hgpos, hcop, hB1, hB2⟩ := Int.exists_gcd_one' hBpos
  set B : ℤ := (g : ℤ) with hBdef
  have hbez : b₁ * Int.gcdA b₁ b₂ + b₂ * Int.gcdB b₁ b₂ = 1 := by
    have h := Int.gcd_eq_gcd_ab b₁ b₂
    rw [hcop] at h; push_cast at h; linarith
  set x₁ := Int.gcdA b₁ b₂ with hx1
  set x₂ := Int.gcdB b₁ b₂ with hx2
  obtain ⟨K, hK⟩ := fiber_dichotomy A B 0
  -- Global bound multiplier
  set X : ℤ := |x₁| + |x₂| with hXdef
  have hXpos : 1 ≤ X := by
    rcases lt_or_ge X 1 with hlt | hge
    · exfalso
      have hx1z : x₁ = 0 := by
        have := abs_nonneg x₁; have := abs_nonneg x₂
        have : |x₁| = 0 := by omega
        exact abs_eq_zero.mp this
      have hx2z : x₂ = 0 := by
        have := abs_nonneg x₁; have := abs_nonneg x₂
        have : |x₂| = 0 := by omega
        exact abs_eq_zero.mp this
      rw [hx1z, hx2z] at hbez; simp at hbez
    · exact hge
  set Kb : ℕ := K * (X.natAbs) ^ 2 with hKbdef
  have hXnn : (0:ℤ) ≤ X := by positivity
  have hKb : (Kb : ℤ) = (K : ℤ) * X ^ 2 := by
    rw [hKbdef]; push_cast; rw [abs_of_nonneg hXnn]
  clear_value Kb X x₁ x₂ B
  refine ⟨Kb, fun l m₁ m₂ q => ?_⟩
  -- core membership equivalence via the unimodular substitution
  have hmem : ∀ C : ℤ,
      (∃ u v : ℤ, fq2 A B₁ B₂ 0 0 0 l m₁ m₂ q C u v = 0) ↔
      (∃ s r : ℤ, s * (B * C + (x₁ * m₁ + x₂ * m₂)) + r * (b₂ * m₁ - b₁ * m₂)
        = -(A * C ^ 2 + l * C + q)) := by
    intro C
    simp only [fq2]
    constructor
    · rintro ⟨u, v, h⟩
      rw [hB1, hB2] at h
      exact ⟨b₁ * u + b₂ * v, x₂ * u - x₁ * v, by linear_combination h + (u * m₁ + v * m₂) * hbez⟩
    · rintro ⟨s, r, h⟩
      rw [hB1, hB2]
      exact ⟨x₁ * s + b₂ * r, x₂ * s - b₁ * r, by linear_combination h + (s * B * C) * hbez⟩
  by_cases hm'' : b₂ * m₁ - b₁ * m₂ = 0
  · -- m'' = 0: reduce to one-witness fiber (A, B, 0) with (l, m', q)
    have hset : fiberSet2 A B₁ B₂ 0 0 0 l m₁ m₂ q = fiberSet A B 0 l (x₁ * m₁ + x₂ * m₂) q := by
      ext c
      simp only [fiberSet2, fiberSet, Set.mem_setOf_eq]
      rw [hmem (c : ℤ), hm'']
      constructor
      · rintro ⟨s, r, h⟩
        exact ⟨s, by simp only [fq]; linear_combination h⟩
      · rintro ⟨u, h⟩
        exact ⟨u, 0, by simp only [fq] at h; linear_combination h⟩
    rw [hset]
    rcases hK l (x₁ * m₁ + x₂ * m₂) q with hinf | hbd
    · exact Or.inl hinf
    · refine Or.inr (fun c hc => le_trans (hbd c hc) ?_)
      -- fbound K l m' q ≤ fbound2 Kb l m₁ m₂ q
      have hmp : |x₁ * m₁ + x₂ * m₂| ≤ X * (|m₁| + |m₂|) := by
        have ht := abs_add_le (x₁ * m₁) (x₂ * m₂)
        rw [abs_mul, abs_mul] at ht
        rw [hXdef]
        nlinarith [abs_nonneg m₁, abs_nonneg m₂, abs_nonneg x₁, abs_nonneg x₂, ht]
      simp only [fbound, fbound2]
      rw [hKb, mul_assoc]
      have hKnn : (0:ℤ) ≤ (K:ℤ) := by positivity
      apply mul_le_mul_of_nonneg_left _ hKnn
      -- goal: (1+|l|+|m'|)^2 + |q| ≤ X^2 * ((1+|l|+|m₁|+|m₂|)^2 + |q|)
      have hl0 := abs_nonneg l
      have hlin : 1 + |l| + |x₁ * m₁ + x₂ * m₂| ≤ X * (1 + |l| + |m₁| + |m₂|) := by
        nlinarith [hmp, hXpos, hl0,
          mul_nonneg (by linarith [hXpos] : (0:ℤ) ≤ X - 1) (by positivity : (0:ℤ) ≤ 1 + |l|)]
      have hbase : (0:ℤ) ≤ 1 + |l| + |x₁ * m₁ + x₂ * m₂| := by positivity
      have hsq : (1 + |l| + |x₁ * m₁ + x₂ * m₂|) ^ 2 ≤ X ^ 2 * (1 + |l| + |m₁| + |m₂|) ^ 2 := by
        nlinarith [hlin, hbase]
      have hX2 : (1:ℤ) ≤ X ^ 2 := by nlinarith [hXpos]
      nlinarith [hsq, mul_le_mul_of_nonneg_right hX2 (abs_nonneg q)]
  · -- m'' ≠ 0: periodic
    set S : Set ℕ := fiberSet2 A B₁ B₂ 0 0 0 l m₁ m₂ q with hSdef
    set M : ℕ := (b₂ * m₁ - b₁ * m₂).natAbs with hMdef
    have hMpos : 1 ≤ M := by
      rw [hMdef]; exact Nat.one_le_iff_ne_zero.mpr (fun hc => hm'' (Int.natAbs_eq_zero.mp hc))
    have hMdvd : (b₂ * m₁ - b₁ * m₂) ∣ (M : ℤ) := by
      rw [hMdef]; exact (Int.dvd_natAbs).mpr dvd_rfl
    have hper : ∀ c : ℕ, c ∈ S ↔ c + M ∈ S := by
      intro c
      simp only [hSdef, fiberSet2, Set.mem_setOf_eq]
      rw [hmem (c : ℤ), hmem ((c + M : ℕ) : ℤ)]
      constructor
      · intro h
        apply shift_pred A B l (x₁ * m₁ + x₂ * m₂) (b₂ * m₁ - b₁ * m₂) q (c : ℤ) ((c + M : ℕ) : ℤ)
          _ _ h
        · push_cast
          rw [show B * ((c:ℤ) + (M:ℤ)) - B * (c:ℤ) = B * (M:ℤ) from by ring]
          exact Dvd.dvd.mul_left hMdvd B
        · push_cast
          have : (A * ((c:ℤ) + ↑M) ^ 2 + l * (↑c + ↑M)) - (A * ↑c ^ 2 + l * ↑c)
              = (↑M) * (2 * A * ↑c + A * ↑M + l) := by ring
          rw [this]; exact Dvd.dvd.mul_right hMdvd _
      · intro h
        apply shift_pred A B l (x₁ * m₁ + x₂ * m₂) (b₂ * m₁ - b₁ * m₂) q ((c + M : ℕ) : ℤ) (c : ℤ)
          _ _ h
        · push_cast
          rw [show B * (c:ℤ) - B * ((c:ℤ) + (M:ℤ)) = B * (-(M:ℤ)) from by ring]
          exact Dvd.dvd.mul_left (Dvd.dvd.neg_right hMdvd) B
        · push_cast
          have : (A * (c:ℤ) ^ 2 + l * ↑c) - (A * ((c:ℤ) + ↑M) ^ 2 + l * (↑c + ↑M))
              = (↑M) * (-(2 * A * ↑c + A * ↑M + l)) := by ring
          rw [this]; exact Dvd.dvd.mul_right hMdvd _
    rcases periodic_infinite_or_empty S M hMpos hper with hinf | hemp
    · exact Or.inl hinf
    · refine Or.inr (fun c hc => ?_)
      rw [hemp] at hc
      simp only [Set.mem_empty_iff_false] at hc

theorem dichotomy2_rank_zero (A B₁ B₂ : ℤ) : Dichotomy2 A B₁ B₂ 0 0 0 := by
  by_cases hB : B₁ = 0 ∧ B₂ = 0
  · obtain ⟨h1, h2⟩ := hB
    subst h1; subst h2
    exact rank_zero_caseA A
  · exact rank_zero_caseB A B₁ B₂ hB

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_zero
