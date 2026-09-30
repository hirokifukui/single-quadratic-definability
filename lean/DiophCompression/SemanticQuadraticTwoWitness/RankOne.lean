/-
  DiophCompression/SemanticQuadraticTwoWitness/RankOne.lean — s8 (claude.ai direct): the rank-1 leaves.
  `dichotomy2_rank_one_normal` (W = k u², k ≠ 0): B₂ = 0 reduces to the r06 one-witness dichotomy (m₂ = 0) or
  to periodicity mod |m₂| (m₂ ≠ 0); B₂ < 0 is reflected to B₂ > 0 by the unimodular change v ↦ −v; B₂ > 0 uses
  the prime step `rank_one_coupled_prime_step` (fiber infinite) or the bound c ≤ |m₂|.
  `dichotomy2_rank_one`: normal form (W3a) + unimodular transfer (W3b).
  Frozen statements: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02) (verbatim f396a2da).
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankOneCoupled
import DiophCompression.SemanticQuadraticTwoWitness.RankOneNormalForm
import DiophCompression.SemanticQuadraticTwoWitness.Unimodular

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral
open DiophCompression.SemanticQuadratic (fq fiberSet fbound fiber_dichotomy)

theorem fq2_rank_one (A B₁ B₂ k l m₁ m₂ q c u v : ℤ) :
    fq2 A B₁ B₂ k 0 0 l m₁ m₂ q c u v = qOne A B₁ k l m₁ q c u + v * (B₂ * c + m₂) := by
  unfold fq2 qOne; ring

/-- Membership in the rank-one fiber is divisibility of Q(c,u) by B₂c + m₂. -/
theorem mem_rank_one_iff (A B₁ B₂ k l m₁ m₂ q : ℤ) (c : ℕ) :
    c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q ↔ ∃ u : ℤ, (B₂ * (c : ℤ) + m₂) ∣ qOne A B₁ k l m₁ q c u := by
  constructor
  · rintro ⟨u, v, huv⟩
    rw [fq2_rank_one] at huv
    exact ⟨u, ⟨-v, by linear_combination huv⟩⟩
  · rintro ⟨u, w, hw⟩
    exact ⟨u, -w, by rw [fq2_rank_one]; linear_combination hw⟩

/-! ### B₂ = 0 -/

theorem rank_one_uncoupled (A B₁ k : ℤ) : Dichotomy2 A B₁ 0 k 0 0 := by
  obtain ⟨K, hK⟩ := fiber_dichotomy A B₁ k
  refine ⟨K, fun l m₁ m₂ q => ?_⟩
  by_cases hm₂ : m₂ = 0
  · subst hm₂
    have hset : fiberSet2 A B₁ 0 k 0 0 l m₁ 0 q = fiberSet A B₁ k l m₁ q := by
      ext c
      simp only [fiberSet2, fiberSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨u, v, huv⟩; exact ⟨u, by rw [fq2_rank_one] at huv; unfold fq qOne at *; linear_combination huv⟩
      · rintro ⟨u, hu⟩; exact ⟨u, 0, by rw [fq2_rank_one]; unfold fq qOne at *; linear_combination hu⟩
    rw [hset]
    rcases hK l m₁ q with hinf | hbd
    · exact Or.inl hinf
    · refine Or.inr (fun c hc => ?_)
      have := hbd c hc
      unfold fbound at this; unfold fbound2
      simpa using this
  · -- periodic mod |m₂|
    have hM : 1 ≤ m₂.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm₂)
    have hper : ∀ c : ℕ, c ∈ fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q ↔ c + m₂.natAbs ∈ fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q := by
      intro c
      have hm₂' : (m₂.natAbs : ℤ) = |m₂| := Int.natCast_natAbs m₂
      have hdvd : m₂ ∣ ((c + m₂.natAbs : ℕ) : ℤ) - (c : ℤ) := by
        push_cast; rw [add_sub_cancel_left]; exact self_dvd_abs m₂
      have key : ∀ c₁ c₂ : ℤ, m₂ ∣ c₂ - c₁ → ∀ u : ℤ,
          (∃ v, fq2 A B₁ 0 k 0 0 l m₁ m₂ q c₁ u v = 0) → ∃ v, fq2 A B₁ 0 k 0 0 l m₁ m₂ q c₂ u v = 0 := by
        intro c₁ c₂ hd u ⟨v, hv⟩
        obtain ⟨w, hw⟩ := hd
        -- Q(c₂,u) − Q(c₁,u) = (c₂ − c₁)(A(c₂ + c₁) + B₁ u + l) = m₂ w (…)
        refine ⟨v - w * (A * (c₂ + c₁) + B₁ * u + l), ?_⟩
        rw [fq2_rank_one] at hv ⊢
        have : qOne A B₁ k l m₁ q c₂ u - qOne A B₁ k l m₁ q c₁ u = (c₂ - c₁) * (A * (c₂ + c₁) + B₁ * u + l) := by
          unfold qOne; ring
        simp only [zero_mul, zero_add] at hv ⊢
        linear_combination hv + this + (A * (c₂ + c₁) + B₁ * u + l) * hw
      constructor
      · rintro ⟨u, v, huv⟩
        obtain ⟨v', hv'⟩ := key (c : ℤ) _ hdvd u ⟨v, huv⟩
        exact ⟨u, v', hv'⟩
      · rintro ⟨u, v, huv⟩
        obtain ⟨v', hv'⟩ := key _ (c : ℤ) ((dvd_neg).mpr hdvd |> fun h => by
          rw [neg_sub] at h; exact h) u ⟨v, huv⟩
        exact ⟨u, v', hv'⟩
    rcases periodic_infinite_or_empty _ _ hM hper with hinf | hemp
    · exact Or.inl hinf
    · right; intro c hc; rw [hemp] at hc; exact absurd hc (Set.notMem_empty c)

/-! ### B₂ > 0 -/

theorem rank_one_coupled_pos (A B₁ B₂ k : ℤ) (hk : k ≠ 0) (hB₂ : 0 < B₂) : Dichotomy2 A B₁ B₂ k 0 0 := by
  refine ⟨1, fun l m₁ m₂ q => ?_⟩
  by_cases hex : ∃ c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q, 0 < B₂ * (c : ℤ) + m₂
  · left
    obtain ⟨c₀, hc₀, ht₀⟩ := hex
    -- iterate the prime step
    have hk' : ∀ n : ℕ, ∃ c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q, 0 < B₂ * (c : ℤ) + m₂ ∧ n ≤ c := by
      intro n
      induction n with
      | zero => exact ⟨c₀, hc₀, ht₀, Nat.zero_le _⟩
      | succ n ih =>
        obtain ⟨c, hc, ht, hnc⟩ := ih
        obtain ⟨u, hu⟩ := (mem_rank_one_iff A B₁ B₂ k l m₁ m₂ q c).mp hc
        obtain ⟨c', u', hlt, hdvd⟩ := rank_one_coupled_prime_step A B₁ B₂ k l m₁ m₂ q c u hB₂ hk ht hu
        have hc'0 : 0 ≤ c' := by have : (0 : ℤ) ≤ c := by positivity
                                 linarith
        have hcast : ((c'.toNat : ℕ) : ℤ) = c' := Int.toNat_of_nonneg hc'0
        have ht' : 0 < B₂ * ((c'.toNat : ℕ) : ℤ) + m₂ := by
          rw [hcast]; nlinarith
        refine ⟨c'.toNat, ?_, ht', ?_⟩
        · rw [mem_rank_one_iff A B₁ B₂ k l m₁ m₂ q _, hcast]; exact ⟨u', hdvd⟩
        · omega
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M0, hM0⟩
    obtain ⟨c, hc, -, hkc⟩ := hk' (M0 + 1)
    have := hM0 hc
    omega
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

/-! ### Assembly of the rank-one normal form -/

theorem dichotomy2_rank_one_normal (A B₁ B₂ k : ℤ) (hk : k ≠ 0) : Dichotomy2 A B₁ B₂ k 0 0 := by
  rcases lt_trichotomy B₂ 0 with hneg | hzero | hpos
  · -- reflect v ↦ −v
    have h := rank_one_coupled_pos A B₁ (-B₂) k hk (by linarith)
    refine dichotomy2_of_unimodular A B₁ B₂ k 0 0 1 0 0 (-1) (Or.inr (by norm_num)) ?_
    norm_num
    exact h
  · subst hzero; exact rank_one_uncoupled A B₁ k
  · exact rank_one_coupled_pos A B₁ B₂ k hk hpos

theorem dichotomy2_rank_one (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ = 0)
    (hne : ¬ (C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0)) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨p, r, s, t, k, hdet, hk, h1, h2, h3⟩ := rank_one_normal_form C₁₁ C₁₂ C₂₂ hd hne
  refine dichotomy2_of_unimodular A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t hdet ?_
  rw [h1, h2, h3]
  exact dichotomy2_rank_one_normal A _ _ k hk

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one_normal
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_rank_one
