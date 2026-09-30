/-
  PrimeRay.lean — Gate-18 research program, Packet A3-1 / A3-2 and the A5-1 input type.
  A3-1: `FixedBasePrimeRay S` — one modulus M, one affine law d·c_p = α·p + β, and for EVERY good
        prime p (prime, M < p, p ≡ 1 mod M) an output c_p ∈ S. All fields are data, not tags.
  A3-2: the output map p ↦ c_p is injective on good primes (α ≠ 0).
  Rays from A1 (rank ≥ 2 moving branch, d = b, α = t₀, β = −μ) and A2 (rank-one coupled branch,
  d = B₂, α = t₀, β = −m₂), into the ℤ-output sets of the respective divisibility relations.
  A5-1: `FixedAPPrimeLowerBound` — the external analytic input, stated exactly (∀ M ≥ 1, ∃ c > 0,
        Y₀, ∀ Y ≥ Y₀, π(Y; M, 1) ≥ c·Y/log Y). Not proved here; not an axiom; a hypothesis.
-/
import ResearchUpgrade.Counting
import ResearchUpgrade.AllGoodPrimeRankTwo
import ResearchUpgrade.AllGoodPrimeRankOne

namespace DiophCompression.ResearchUpgrade

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular
  DiophCompression.SemanticQuadraticTwoWitness

/-- `p` is a good prime for modulus `M`: prime, above `M`, `≡ 1 (mod M)`. -/
def GoodPrime (M p : ℕ) : Prop := p.Prime ∧ M < p ∧ p ≡ 1 [MOD M]

/-- A3-1. A fixed-base prime ray inside `S ⊆ ℤ`. -/
structure FixedBasePrimeRay (S : Set ℤ) where
  M : ℕ
  hM : 1 ≤ M
  α : ℤ
  β : ℤ
  d : ℤ
  hα : α ≠ 0
  hd : d ≠ 0
  c : ℕ → ℤ
  affine : ∀ p, GoodPrime M p → d * c p = α * p + β
  mem : ∀ p, GoodPrime M p → c p ∈ S

/-- A3-2. The output map of a ray is injective on good primes. -/
theorem FixedBasePrimeRay.injOn {S : Set ℤ} (R : FixedBasePrimeRay S) :
    Set.InjOn R.c {p | GoodPrime R.M p} := by
  intro p hp p' hp' h
  have h1 := R.affine p hp
  have h2 := R.affine p' hp'
  rw [h] at h1
  have : R.α * (p : ℤ) = R.α * p' := by linarith
  exact_mod_cast mul_left_cancel₀ R.hα this

/-- Output size along a ray: `|c_p| ≤ |α|·p + |β|` (using `|d| ≥ 1`). -/
theorem FixedBasePrimeRay.abs_le {S : Set ℤ} (R : FixedBasePrimeRay S) (p : ℕ)
    (hp : GoodPrime R.M p) : |R.c p| ≤ |R.α| * p + |R.β| := by
  have h := R.affine p hp
  have hd1 : 1 ≤ |R.d| := Int.one_le_abs R.hd
  have : |R.d| * |R.c p| = |R.α * p + R.β| := by rw [← abs_mul, h]
  have h3 : |R.α * (p : ℤ) + R.β| ≤ |R.α| * p + |R.β| := by
    calc |R.α * (p : ℤ) + R.β| ≤ |R.α * (p : ℤ)| + |R.β| := abs_add_le _ _
      _ = |R.α| * p + |R.β| := by rw [abs_mul, Nat.abs_cast]
  nlinarith [abs_nonneg (R.c p)]

/-! ### The ℤ-output sets of the two moving branches -/

/-- Outputs `c ∈ ℤ` of the rank ≥ 2 moving relation `(b c + μ) ∣ fqM(c, u)`. -/
def movingOutputSet {k : ℕ} (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) : Set ℤ :=
  {c | ∃ u : Fin k → ℤ, (b * c + μ) ∣ fqM A B C l m q c u}

/-- Outputs `c ∈ ℤ` of the rank-one coupled relation `(B₂ c + m₂) ∣ qOne(c, u)`. -/
def rankOneOutputSet (A B₁ B₂ k l m₁ m₂ q : ℤ) : Set ℤ :=
  {c | ∃ u : ℤ, (B₂ * c + m₂) ∣ qOne A B₁ k l m₁ q c u}

/-- A3 from A1: the rank ≥ 2 moving branch carries a fixed-base prime ray
(`d = b`, `α = t₀ = b c₀ + μ`, `β = −μ`, `M = 2|D|·b·t₀`). -/
def movingRay {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ) (u₀ : Fin k → ℤ) (hb : 0 < b)
    (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀) :
    FixedBasePrimeRay (movingOutputSet A B C b l m μ q) where
  M := movingModulusNat (C + Cᵀ).det b (b * c₀ + μ)
  hM := by
    unfold movingModulusNat
    have h1 : (C + Cᵀ).det.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN
    have h2 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
    have h4 : (b * c₀ + μ).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    have : 0 < 2 * (C + Cᵀ).det.natAbs * b.natAbs * (b * c₀ + μ).natAbs := by positivity
    omega
  α := b * c₀ + μ
  β := -μ
  d := b
  hα := ht₀.ne'
  hd := hb.ne'
  c := fun p => c₀ + (b * c₀ + μ) * (((p : ℤ) - 1) / b)
  affine := by
    intro p ⟨hp, hpM, hpmod⟩
    have h := (moving_modulus_prime_step_allGoodPrime hk A B C b l m μ q c₀ u₀ hb hN ht₀ hdiv
      p hp hpM hpmod).2.1
    linarith
  mem := by
    intro p ⟨hp, hpM, hpmod⟩
    obtain ⟨-, -, u, -, -, -, -, hdvd⟩ :=
      moving_modulus_prime_step_allGoodPrime hk A B C b l m μ q c₀ u₀ hb hN ht₀ hdiv p hp hpM hpmod
    exact ⟨u, hdvd⟩

/-- A3 from A2: the rank-one coupled branch carries a fixed-base prime ray
(`d = B₂`, `α = t₀ = B₂ c₀ + m₂`, `β = −m₂`, `M = 8·max(1,|D'|)·B₂·|2k|·t₀`). -/
def rankOneRay (A B₁ B₂ k l m₁ m₂ q c₀ u₀ : ℤ) (hB₂ : 0 < B₂) (hk : k ≠ 0)
    (ht₀ : 0 < B₂ * c₀ + m₂) (hdiv : (B₂ * c₀ + m₂) ∣ qOne A B₁ k l m₁ q c₀ u₀) :
    FixedBasePrimeRay (rankOneOutputSet A B₁ B₂ k l m₁ m₂ q) where
  M := rankOneModulusNat (dPrime A B₁ B₂ k l m₁ m₂ q) B₂ k (B₂ * c₀ + m₂)
  hM := by
    unfold rankOneModulusNat
    have h1 : (max 1 |dPrime A B₁ B₂ k l m₁ m₂ q|).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |dPrime A B₁ B₂ k l m₁ m₂ q|; omega)
    have h2 : B₂.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hB₂.ne'
    have h3 : (2 * k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero two_ne_zero hk)
    have h4 : (B₂ * c₀ + m₂).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    have : 0 < 8 * (max 1 |dPrime A B₁ B₂ k l m₁ m₂ q|).natAbs * B₂.natAbs * (2 * k).natAbs
        * (B₂ * c₀ + m₂).natAbs := by positivity
    omega
  α := B₂ * c₀ + m₂
  β := -m₂
  d := B₂
  hα := ht₀.ne'
  hd := hB₂.ne'
  c := fun p => c₀ + (B₂ * c₀ + m₂) * (((p : ℤ) - 1) / B₂)
  affine := by
    intro p ⟨hp, hpM, hpmod⟩
    have h := (rank_one_coupled_prime_step_allGoodPrime A B₁ B₂ k l m₁ m₂ q c₀ u₀ hB₂ hk ht₀ hdiv
      p hp hpM hpmod).2.1
    linarith
  mem := by
    intro p ⟨hp, hpM, hpmod⟩
    obtain ⟨-, -, u, -, -, -, -, hdvd⟩ :=
      rank_one_coupled_prime_step_allGoodPrime A B₁ B₂ k l m₁ m₂ q c₀ u₀ hB₂ hk ht₀ hdiv p hp hpM hpmod
    exact ⟨u, hdvd⟩

/-! ### A5-1: the external prime-counting input, stated exactly -/

/-- `π(Y; M, 1)` = number of primes `p ≤ Y` with `p ≡ 1 (mod M)`. -/
def primeCountAP (M Y : ℕ) : ℕ :=
  ((Finset.range (Y + 1)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD M])).card

/-- A5-1. `∀ M ≥ 1, ∃ c > 0, Y₀, ∀ Y ≥ Y₀, π(Y; M, 1) ≥ c·Y/log Y`. No uniformity in `M`.
This is the ONLY analytic input of the A5 route; it is a hypothesis, never an axiom. -/
def FixedAPPrimeLowerBound : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∃ (c : ℝ) (Y₀ : ℕ), 0 < c ∧ 2 ≤ Y₀ ∧
    ∀ Y : ℕ, Y₀ ≤ Y → c * Y / Real.log Y ≤ (primeCountAP M Y : ℝ)

/-- Counting along a ray (Finset form, no analysis): good primes `p ≤ Y` give distinct outputs
in `[−X, X]` once `|α|·Y + |β| ≤ X`, so `N_S(X) ≥ π(Y; M, 1) − M` (the primes `≤ M` are dropped). -/
theorem fiberCountZZ_ge_primeCountAP {S : Set ℤ} (R : FixedBasePrimeRay S) (X Y : ℕ)
    (hXY : |R.α| * Y + |R.β| ≤ X) :
    primeCountAP R.M Y ≤ fiberCountZZ S X + R.M := by
  classical
  unfold primeCountAP fiberCountZZ
  set G := (Finset.range (Y + 1)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD R.M]) with hG
  set Ggood := G.filter (fun p => R.M < p) with hGg
  set Gsmall := G.filter (fun p => ¬ R.M < p) with hGs
  have hsplit : G.card = Ggood.card + Gsmall.card := by
    rw [hGg, hGs]; exact (Finset.filter_card_add_filter_neg_card_eq_card _).symm
  have hsmall : Gsmall.card ≤ R.M := by
    calc Gsmall.card ≤ ((Finset.range (R.M + 1)).filter (fun p : ℕ => p.Prime)).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [hGs, hG, Finset.mem_filter, Finset.mem_range] at hp
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hp.1.2.1⟩
      _ ≤ R.M := by
          calc ((Finset.range (R.M + 1)).filter (fun p : ℕ => p.Prime)).card
              ≤ ((Finset.range (R.M + 1)).erase 0).card := by
                apply Finset.card_le_card
                intro p hp
                simp only [Finset.mem_filter, Finset.mem_range] at hp
                simp only [Finset.mem_erase, Finset.mem_range]
                exact ⟨hp.2.ne_zero, hp.1⟩
            _ = R.M := by rw [Finset.card_erase_of_mem (by simp), Finset.card_range]; rfl
  have hgood : Ggood.card ≤ ((Finset.Icc (-(X : ℤ)) (X : ℤ)).filter (fun c => c ∈ S)).card := by
    have hinj : Set.InjOn R.c ↑Ggood := by
      intro p hp p' hp' h
      rw [Finset.mem_coe] at hp hp'
      simp only [hGg, hG, Finset.mem_filter, Finset.mem_range] at hp hp'
      exact R.injOn ⟨hp.1.2.1, hp.2, hp.1.2.2⟩ ⟨hp'.1.2.1, hp'.2, hp'.1.2.2⟩ h
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    have hgp : GoodPrime R.M p := by
      simp only [hGg, hG, Finset.mem_filter, Finset.mem_range] at hp
      exact ⟨hp.1.2.1, hp.2, hp.1.2.2⟩
    have hpY : p ≤ Y := by
      simp only [hGg, hG, Finset.mem_filter, Finset.mem_range] at hp; omega
    have hb := R.abs_le p hgp
    have hpY' : (p : ℤ) ≤ Y := by exact_mod_cast hpY
    have : |R.c p| ≤ (X : ℤ) := by
      calc |R.c p| ≤ |R.α| * p + |R.β| := hb
        _ ≤ |R.α| * Y + |R.β| := by nlinarith [abs_nonneg R.α]
        _ ≤ X := hXY
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨abs_le.mp this, R.mem p hgp⟩
  omega

end DiophCompression.ResearchUpgrade
