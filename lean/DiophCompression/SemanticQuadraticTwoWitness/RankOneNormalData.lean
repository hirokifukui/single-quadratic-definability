/-
  DiophCompression/SemanticQuadraticTwoWitness/RankOneNormalData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (rank-one normal form) (s28, 2026-09-02, claude.ai direct).

  The rank-one layer, complete in data-carrying form:
    * the unimodular witness change is a set EQUALITY, so the certificate transports (branch B1a is this
      transport at B₂ < 0);
    * branch B1c iterates `rank_one_coupled_prime_step_data` into an explicit moving-modulus orbit —
      outputs, stage primes and the recurrence `B₂c_{n+1} + m₂ = (B₂c_n + m₂)·p_n`;
    * branch B1b is `rank_one_uncoupled_data`.
  Each data form implies its sealed counterpart. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankOneUncoupledData
import DiophCompression.SemanticQuadraticTwoWitness.RankOneCoupledData
import DiophCompression.SemanticQuadraticTwoWitness.Unimodular

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

theorem dichotomy2Data_of_unimodular (A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t : ℤ) (hdet : p * t - r * s = 1 ∨ p * t - r * s = -1)
    (h : Dichotomy2Data A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
          (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
          (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
          (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)) :
    Dichotomy2Data A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K * (1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs) ^ 2, ?_⟩
  intro l m₁ m₂ q
  have hEq : fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q =
      fiberSet2 A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
        (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
        (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
        (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)
        l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q := by
    ext c
    simp only [fiberSet2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, huv⟩
      rcases hdet with hε | hε
      · refine ⟨t * u - r * v, p * v - s * u, ?_⟩
        have key := fq2_subst A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t l m₁ m₂ q (c : ℤ) (t * u - r * v) (p * v - s * u)
        rw [← key]
        have hu : p * (t * u - r * v) + r * (p * v - s * u) = u := by linear_combination u * hε
        have hv : s * (t * u - r * v) + t * (p * v - s * u) = v := by linear_combination v * hε
        rw [hu, hv]; exact huv
      · refine ⟨r * v - t * u, s * u - p * v, ?_⟩
        have key := fq2_subst A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t l m₁ m₂ q (c : ℤ) (r * v - t * u) (s * u - p * v)
        rw [← key]
        have hu : p * (r * v - t * u) + r * (s * u - p * v) = u := by linear_combination (-u) * hε
        have hv : s * (r * v - t * u) + t * (s * u - p * v) = v := by linear_combination (-v) * hε
        rw [hu, hv]; exact huv
    · rintro ⟨u, v, huv⟩
      exact ⟨p * u + r * v, s * u + t * v, by rw [fq2_subst]; exact huv⟩
  rcases hK l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q with hF | hBd
  · left; rw [hEq]; exact hF
  · right; intro c hc
    rw [hEq] at hc
    exact le_trans (hBd c hc) (fbound2_mono K p r s t l m₁ m₂ q)
/-! ### Branch B1c: the step data iterated into an orbit -/

theorem b1c_orbit (A B₁ B₂ k l m₁ m₂ q : ℤ) (hB₂ : 0 < B₂) (hk : k ≠ 0)
    (c₀ : ℕ) (hc₀ : c₀ ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q)
    (ht₀ : 0 < B₂ * (c₀ : ℤ) + m₂) :
    ∃ (cf : ℕ → ℕ) (pr : ℕ → ℕ), (∀ n, (pr n).Prime) ∧
      (∀ n, B₂ * (cf (n + 1) : ℤ) + m₂ = (B₂ * (cf n : ℤ) + m₂) * (pr n)) ∧
      (∀ n, cf n ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q) ∧ StrictMono cf ∧
      (∀ n, 0 < B₂ * (cf n : ℤ) + m₂) ∧
      (∀ n, ((8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) * B₂ * (B₂ * (cf n : ℤ) + m₂) : ℤ) < (pr n : ℤ)) ∧
      (∀ n, ((pr n : ℤ)) ≡ 1 [ZMOD (8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) * B₂ * (B₂ * (cf n : ℤ) + m₂)]) := by
  classical
  have step : ∀ x : {c : ℕ // c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q ∧ 0 < B₂ * (c : ℤ) + m₂},
      ∃ (y : {c : ℕ // c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q ∧ 0 < B₂ * (c : ℤ) + m₂}) (p : ℕ),
        p.Prime ∧ (x : ℕ) < (y : ℕ) ∧
        B₂ * (((y : ℕ) : ℕ) : ℤ) + m₂ = (B₂ * (((x : ℕ) : ℕ) : ℤ) + m₂) * p ∧
        ((8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) * B₂ * (B₂ * (((x : ℕ) : ℕ) : ℤ) + m₂) : ℤ) < (p : ℤ) ∧
        ((p : ℤ)) ≡ 1 [ZMOD (8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) * B₂ * (B₂ * (((x : ℕ) : ℕ) : ℤ) + m₂)] := by
    rintro ⟨c, hc, ht⟩
    obtain ⟨u, hu⟩ := (mem_rank_one_iff A B₁ B₂ k l m₁ m₂ q c).mp hc
    obtain ⟨p, M, c', u', hp, hlt, hMdef, hMp, hpmod, hrec, hcrt, hdvd⟩ :=
      rank_one_coupled_prime_step_data A B₁ B₂ k l m₁ m₂ q (c : ℤ) u hB₂ hk ht hu
    have hc0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
    have hc'0 : (0 : ℤ) ≤ c' := by linarith
    have hcast : ((c'.toNat : ℕ) : ℤ) = c' := Int.toNat_of_nonneg hc'0
    have hmem' : c'.toNat ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q := by
      rw [mem_rank_one_iff A B₁ B₂ k l m₁ m₂ q _, hcast]
      exact ⟨u', hdvd⟩
    have hpos' : 0 < B₂ * ((c'.toNat : ℕ) : ℤ) + m₂ := by
      rw [hcast, hrec]
      have : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
      positivity
    have hnn : (0 : ℤ) ≤ max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| :=
      le_trans zero_le_one (le_max_left _ _)
    have hMcast : ((M : ℕ) : ℤ)
        = (8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) * B₂ * (B₂ * (c : ℤ) + m₂) := by
      subst hMdef
      push_cast [abs_of_nonneg hnn, abs_of_pos hB₂, abs_of_pos ht]
      ring
    refine ⟨⟨c'.toNat, hmem', hpos'⟩, p, hp, ?_, ?_, ?_, ?_⟩
    · have : (c : ℤ) < ((c'.toNat : ℕ) : ℤ) := by rw [hcast]; exact hlt
      exact_mod_cast this
    · simp only
      rw [hcast, hrec]
    · show ((8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) * B₂ * (B₂ * (c : ℤ) + m₂) : ℤ) < (p : ℤ)
      rw [← hMcast]
      exact_mod_cast hMp
    · show ((p : ℤ)) ≡ 1 [ZMOD (8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) * B₂ * (B₂ * (c : ℤ) + m₂)]
      rw [← hMcast]
      simpa using Int.natCast_modEq_iff.mpr hpmod
  choose f pr hprime hlt hrec hpgt hpmod using step
  set x₀ : {c : ℕ // c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q ∧ 0 < B₂ * (c : ℤ) + m₂} :=
    ⟨c₀, hc₀, ht₀⟩ with hx₀
  set orb : ℕ → {c : ℕ // c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q ∧ 0 < B₂ * (c : ℤ) + m₂} :=
    fun n => Nat.rec x₀ (fun _ x => f x) n with horb
  refine ⟨fun n => (orb n : ℕ), fun n => pr (orb n), fun n => hprime (orb n), fun n => ?_,
    fun n => (orb n).2.1, ?_, fun n => (orb n).2.2, fun n => hpgt (orb n),
    fun n => hpmod (orb n)⟩
  · exact hrec (orb n)
  · refine strictMono_nat_of_lt_succ (fun n => ?_)
    exact hlt (orb n)

/-- Branch B1c in data form: either every fibre point has non-positive modulus (bounded, the sealed
    argument), or the orbit above is a moving-modulus family. -/
theorem rank_one_coupled_pos_data (A B₁ B₂ k : ℤ) (hk : k ≠ 0) (hB₂ : 0 < B₂) :
    Dichotomy2Data A B₁ B₂ k 0 0 := by
  refine ⟨1, fun l m₁ m₂ q => ?_⟩
  by_cases hex : ∃ c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q, 0 < B₂ * (c : ℤ) + m₂
  · left
    obtain ⟨c₀, hc₀, ht₀⟩ := hex
    obtain ⟨cf, pr, hprime, hrec, hmem, hmono, hmpos, hpgt, hpmod⟩ :=
      b1c_orbit A B₁ B₂ k l m₁ m₂ q hB₂ hk c₀ hc₀ ht₀
    have hmf : (0 : ℤ) < 8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k| := by
      have h1 : (1 : ℤ) ≤ max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| := le_max_left _ _
      have h2 : (0 : ℤ) < |2 * k| := abs_pos.mpr (mul_ne_zero two_ne_zero hk)
      positivity
    exact ⟨DiophCompression.StructuredFamily.movingModulus B₂ m₂
      (8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) hB₂ hmf cf pr hprime hmpos hpgt hpmod
      hrec hmem hmono⟩
  · right
    push Not at hex
    intro c hc
    have h := hex c hc
    have hc0 : (0 : ℤ) ≤ c := by positivity
    have h1 : (c : ℤ) ≤ B₂ * c := le_mul_of_one_le_left hc0 (by omega)
    have h2 : (c : ℤ) ≤ |m₂| := by linarith [neg_le_abs m₂]
    unfold fbound2
    have hl := abs_nonneg l; have hm₁ := abs_nonneg m₁; have hm₂ := abs_nonneg m₂; have hq := abs_nonneg q
    push_cast
    nlinarith
/-! ### Assembly of the rank-one normal form, in data form -/

theorem dichotomy2_rank_one_normal_data (A B₁ B₂ k : ℤ) (hk : k ≠ 0) :
    Dichotomy2Data A B₁ B₂ k 0 0 := by
  rcases lt_trichotomy B₂ 0 with hneg | hzero | hpos
  · -- branch B1a: the witness reflection v ↦ −v
    have h := rank_one_coupled_pos_data A B₁ (-B₂) k hk (by linarith)
    refine dichotomy2Data_of_unimodular A B₁ B₂ k 0 0 1 0 0 (-1) (Or.inr (by norm_num)) ?_
    norm_num
    exact h
  · subst hzero; exact rank_one_uncoupled_data A B₁ k
  · exact rank_one_coupled_pos_data A B₁ B₂ k hk hpos

theorem dichotomy2_rank_one_data (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ = 0)
    (hne : ¬ (C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0)) : Dichotomy2Data A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨p, r, s, t, k, hdet, hk, h1, h2, h3⟩ := rank_one_normal_form C₁₁ C₁₂ C₂₂ hd hne
  refine dichotomy2Data_of_unimodular A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t hdet ?_
  rw [h1, h2, h3]
  exact dichotomy2_rank_one_normal_data A _ _ k hk

/-- The data forms imply the sealed rank-one theorems. -/
theorem dichotomy2_rank_one_normal_of_data (A B₁ B₂ k : ℤ) (hk : k ≠ 0) :
    Dichotomy2 A B₁ B₂ k 0 0 :=
  dichotomy2_of_dichotomy2Data (dichotomy2_rank_one_normal_data A B₁ B₂ k hk)

theorem dichotomy2_rank_one_of_data (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ = 0)
    (hne : ¬ (C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0)) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ :=
  dichotomy2_of_dichotomy2Data (dichotomy2_rank_one_data A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hne)

end DiophCompression.SemanticQuadraticTwoWitness

#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2Data_of_unimodular
#print axioms DiophCompression.SemanticQuadraticTwoWitness.b1c_orbit
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_coupled_pos_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_normal_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_normal_of_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_of_data
