/-
  QuotientRankZero.lean — r11 (GPT r10 必須G): the quotient-rank-0 leaf of the singular tree.
  Statements frozen in QuotientRankZero_STATEMENTS.lean (md5 bcc6ed09) before proofs.
  (s11, claude.ai direct.) Route: entirely elementary — no primes. Master identity
  b²(Ac²+lc+q) = (bc+μ)(Abc+bl−Aμ) + (Aμ²−blμ+b²q), numerically re-verified before writing
  (A=2,b=3,μ=5,l=7,q=11,c=1: 180 = 8·17 + 44). For b ≠ 0 and vanishing remainder the fiber is
  governed by the congruence Abc ≡ Aμ−bl (mod b²): solvable ⇒ an arithmetic progression lies in
  the fiber (infinite); unsolvable ⇒ the fiber sits inside {bc+μ = 0} (at most one point).
-/
import DiophCompression.SemanticQuadraticSingular.DefsSingularGeneral
import DiophCompression.SemanticQuadraticTwoWitness.Bridge2W

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix
open DiophCompression.SemanticQuadraticTwoWitness (periodic_infinite_or_empty)

/-- Divisor absolute-value bound. -/
theorem abs_le_abs_of_dvd {a b : ℤ} (h : a ∣ b) (hb : b ≠ 0) : |a| ≤ |b| :=
  Int.le_of_dvd (abs_pos.mpr hb) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr h))

/-- Triangle bound for a difference. -/
theorem abs_sub_le' (a b : ℤ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  calc |a + -b| ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

/-- GPT r10 必須G theorem 1 (name verbatim): dividing the quadratic remainder by the linear
modulus leaves the fixed remainder A μ² − b l μ + b² q. -/
theorem linear_modulus_divides_quadratic_remainder (A l q b μ c : ℤ)
    (h : (b * c + μ) ∣ (A * c ^ 2 + l * c + q)) :
    (b * c + μ) ∣ (A * μ ^ 2 - b * l * μ + b ^ 2 * q) := by
  have key : A * μ ^ 2 - b * l * μ + b ^ 2 * q
      = b ^ 2 * (A * c ^ 2 + l * c + q)
        - (b * c + μ) * (A * (b * c + μ) + (b * l - 2 * A * μ)) := by
    ring
  rw [key]
  exact dvd_sub (h.mul_left _) (Dvd.intro _ rfl)

/-- GPT r10 必須G theorem 2 (name verbatim): for positive slope, either the fixed remainder
vanishes (and every large enough modulus divides the fiber value on an explicit family) or the
modulus is bounded by the remainder. -/
theorem quotient_rank_zero_bounded_or_infinite (A b l μ q : ℤ) (hb : 0 < b) :
    (A * μ ^ 2 - b * l * μ + b ^ 2 * q = 0) ∨
      ∀ c : ℤ, (b * c + μ) ∣ b ^ 2 * (A * c ^ 2 + l * c + q) →
        (b * c + μ) ∣ (A * μ ^ 2 - b * l * μ + b ^ 2 * q) ∧
          (A * μ ^ 2 - b * l * μ + b ^ 2 * q ≠ 0 →
            |b * c + μ| ≤ |A * μ ^ 2 - b * l * μ + b ^ 2 * q|) := by
  by_cases hR : A * μ ^ 2 - b * l * μ + b ^ 2 * q = 0
  · exact Or.inl hR
  · refine Or.inr (fun c hdvd => ?_)
    have key : A * μ ^ 2 - b * l * μ + b ^ 2 * q
        = b ^ 2 * (A * c ^ 2 + l * c + q)
          - (b * c + μ) * (A * (b * c + μ) + (b * l - 2 * A * μ)) := by
      ring
    have hd : (b * c + μ) ∣ (A * μ ^ 2 - b * l * μ + b ^ 2 * q) := by
      rw [key]
      exact dvd_sub hdvd (Dvd.intro _ rfl)
    exact ⟨hd, fun hR' => abs_le_abs_of_dvd hd hR'⟩

/-- The k = 0 fiber value in scalar form. -/
theorem fqSG_zero (A : ℤ) (B : Fin 0 → ℤ) (C : Matrix (Fin 0) (Fin 0) ℤ) (b l : ℤ)
    (m : Fin 0 → ℤ) (μ q c : ℤ) (u : Fin 0 → ℤ) (w : ℤ) :
    fqSG A B C b l m μ q c u w = A * c ^ 2 + l * c + q + (b * c + μ) * w := by
  simp only [fqSG, fqM, witnessQuad, dotProduct, Finset.univ_eq_empty, Finset.sum_empty]
  ring

/-- The k = 0 fiber membership in scalar form. -/
theorem mem_fiberSetSG_zero (A : ℤ) (B : Fin 0 → ℤ) (C : Matrix (Fin 0) (Fin 0) ℤ) (b l : ℤ)
    (m : Fin 0 → ℤ) (μ q : ℤ) (c : ℕ) :
    c ∈ fiberSetSG A B C b l m μ q ↔
      ∃ w : ℤ, A * (c : ℤ) ^ 2 + l * c + q + (b * c + μ) * w = 0 := by
  constructor
  · rintro ⟨u, w, hw⟩
    exact ⟨w, by rw [← fqSG_zero A B C b l m μ q c u w]; exact hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨fun i => i.elim0, w, by rw [fqSG_zero]; exact hw⟩

/-- Scalar solvability is divisibility. -/
theorem exists_w_iff_dvd (F d : ℤ) : (∃ w : ℤ, F + d * w = 0) ↔ d ∣ F := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨-w, by linarith⟩
  · rintro ⟨e, he⟩
    exact ⟨-e, by rw [he]; ring⟩

set_option maxHeartbeats 1600000 in
/-- GPT r10 必須G theorem 3 (name verbatim): the quotient-rank-0 dichotomy, i.e. `DichotomySG`
at k = 0 for every (A, b). -/
theorem quotient_rank_zero_dichotomy (A b : ℤ) (B : Fin 0 → ℤ) (C : Matrix (Fin 0) (Fin 0) ℤ) :
    DichotomySG A B C b := by
  refine ⟨A.natAbs + b.natAbs + b.natAbs ^ 2 + 2, fun l m μ q => ?_⟩
  set R : ℤ := A * μ ^ 2 - b * l * μ + b ^ 2 * q with hRdef
  set KZ : ℤ := ((A.natAbs + b.natAbs + b.natAbs ^ 2 + 2 : ℕ) : ℤ) with hKZdef
  have hKZ : KZ = |A| + |b| + |b| ^ 2 + 2 := by
    rw [hKZdef]
    push_cast [Int.natCast_natAbs]
    ring
  have hfb : fboundSG (A.natAbs + b.natAbs + b.natAbs ^ 2 + 2) l m μ q
      = KZ * ((1 + |l| + |μ|) ^ 2 + |q|) := by
    simp only [fboundSG, Finset.univ_eq_empty, Finset.sum_empty, add_zero, hKZdef]
  have hshape : (0 : ℤ) ≤ (1 + |l| + |μ|) ^ 2 + |q| := by positivity
  have hKZ2 : (2 : ℤ) ≤ KZ := by
    rw [hKZ]
    nlinarith [abs_nonneg A, abs_nonneg b, sq_nonneg |b|]
  clear_value R KZ
  by_cases hb : b = 0
  · -- fixed modulus μ
    subst hb
    by_cases hμ : μ = 0
    · -- no coupled variable: A c² + l c + q = 0
      subst hμ
      by_cases hA : A = 0
      · by_cases hl : l = 0
        · by_cases hq : q = 0
          · left
            apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => n)
              Function.injective_id
            intro n
            rw [mem_fiberSetSG_zero]
            exact ⟨0, by simp [hA, hl, hq]⟩
          · right
            intro c hc
            rw [mem_fiberSetSG_zero] at hc
            obtain ⟨w, hw⟩ := hc
            simp [hA, hl] at hw
            exact absurd hw hq
        · right
          intro c hc
          rw [mem_fiberSetSG_zero] at hc
          obtain ⟨w, hw⟩ := hc
          simp [hA] at hw
          have hlc : l * (c : ℤ) = -q := by linarith
          have h1 : |l| * (c : ℤ) = |q| := by
            rw [← Int.abs_natCast c, ← abs_mul, hlc, abs_neg]
          have h2 : 1 ≤ |l| := Int.one_le_abs (by exact_mod_cast hl)
          have hcle : (c : ℤ) ≤ |q| := by
            nlinarith [Int.natCast_nonneg c,
              mul_nonneg (Int.natCast_nonneg c) (sub_nonneg.mpr h2)]
          rw [hfb]
          calc (c : ℤ) ≤ |q| := hcle
            _ ≤ KZ * ((1 + |l| + |0|) ^ 2 + |q|) := by
              nlinarith [abs_nonneg l, abs_nonneg q, sq_nonneg (1 + |l|), hKZ2]
      · right
        intro c hc
        rw [mem_fiberSetSG_zero] at hc
        obtain ⟨w, hw⟩ := hc
        simp at hw
        have hA1 : 1 ≤ |A| := Int.one_le_abs (by exact_mod_cast hA)
        have h1 : A * (c : ℤ) ^ 2 = -(l * c + q) := by linarith
        have h2 : |A| * (c : ℤ) ^ 2 = |l * (c : ℤ) + q| := by
          calc |A| * (c : ℤ) ^ 2 = |A| * |(c : ℤ)| ^ 2 := by rw [Int.abs_natCast]
            _ = |A * (c : ℤ) ^ 2| := by rw [abs_mul, abs_pow]
            _ = |l * (c : ℤ) + q| := by rw [h1, abs_neg]
        have h3 : |l * (c : ℤ) + q| ≤ |l| * c + |q| := by
          calc |l * (c : ℤ) + q| ≤ |l * (c : ℤ)| + |q| := abs_add_le _ _
            _ = |l| * c + |q| := by rw [abs_mul, Int.abs_natCast]
        have hkey : (c : ℤ) ^ 2 ≤ |l| * c + |q| := by nlinarith [Int.natCast_nonneg c]
        have hcle : (c : ℤ) ≤ |l| + |q| + 1 := by
          nlinarith [Int.natCast_nonneg c, abs_nonneg l, abs_nonneg q]
        rw [hfb]
        simp only [abs_zero, add_zero]
        nlinarith [hcle, hKZ2, abs_nonneg l, abs_nonneg q,
          mul_nonneg (sub_nonneg.mpr hKZ2) (show (0:ℤ) ≤ (1 + |l|) ^ 2 + |q| by positivity),
          mul_nonneg (show (0:ℤ) ≤ 1 + |l| by positivity) (abs_nonneg l)]
    · -- μ ≠ 0: divisibility, μ-periodic
      have hM : 1 ≤ μ.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hμ)
      have hμd : μ ∣ |μ| := (dvd_abs μ μ).mpr dvd_rfl
      have hper : ∀ c : ℕ, c ∈ fiberSetSG A B C 0 l m μ q ↔
          c + μ.natAbs ∈ fiberSetSG A B C 0 l m μ q := by
        intro c
        rw [mem_fiberSetSG_zero, mem_fiberSetSG_zero]
        simp only [zero_mul, zero_add]
        rw [exists_w_iff_dvd, exists_w_iff_dvd]
        constructor
        · intro h
          push_cast
          have hEq : A * ((c : ℤ) + |μ|) ^ 2 + l * ((c : ℤ) + |μ|) + q
              = |μ| * (A * (2 * (c : ℤ) + |μ|) + l)
                + (A * (c : ℤ) ^ 2 + l * (c : ℤ) + q) := by ring
          rw [hEq]
          exact dvd_add (hμd.mul_right _) h
        · intro h
          push_cast at h
          have hEq : A * (c : ℤ) ^ 2 + l * (c : ℤ) + q
              = (A * ((c : ℤ) + |μ|) ^ 2 + l * ((c : ℤ) + |μ|) + q)
                - |μ| * (A * (2 * (c : ℤ) + |μ|) + l) := by ring
          rw [hEq]
          exact dvd_sub h (hμd.mul_right _)
      rcases periodic_infinite_or_empty (fiberSetSG A B C 0 l m μ q) μ.natAbs hM hper
          with hinf | hemp
      · exact Or.inl hinf
      · right
        rw [hemp]
        intro c hc
        exact absurd hc (Set.notMem_empty c)
  · -- b ≠ 0
    have hb1 : 1 ≤ |b| := Int.one_le_abs (by exact_mod_cast hb)
    by_cases hR : R = 0
    · by_cases hcong : ∃ c₀ : ℤ, (b ^ 2) ∣ (A * b * c₀ + b * l - A * μ)
      · -- infinite: an arithmetic progression lies in the fiber
        left
        obtain ⟨c₀, hc₀⟩ := hcong
        have hb2pos : (0 : ℤ) < b ^ 2 := by positivity
        have hb2 : (b : ℤ) ^ 2 ≠ 0 := ne_of_gt hb2pos
        set T : ℕ := (b ^ 2).natAbs with hT
        have hTpos : 0 < T := Int.natAbs_pos.mpr hb2
        have hTZ : (T : ℤ) = b ^ 2 := Int.natAbs_of_nonneg (le_of_lt hb2pos)
        set c₁ : ℤ := c₀ + (T : ℤ) * (|c₀| + 1) with hc₁
        have hc₁nn : 0 ≤ c₁ := by
          have h1 : (1 : ℤ) ≤ (T : ℤ) := by exact_mod_cast hTpos
          nlinarith [abs_nonneg c₀, neg_abs_le c₀]
        have hc₁cong : (b ^ 2) ∣ (A * b * c₁ + b * l - A * μ) := by
          have he : A * b * c₁ + b * l - A * μ
              = (A * b * c₀ + b * l - A * μ) + b ^ 2 * (A * b * (|c₀| + 1)) := by
            rw [hc₁, hTZ]; ring
          rw [he]
          exact dvd_add hc₀ (Dvd.intro _ rfl)
        have hinj : Function.Injective (fun t : ℕ => c₁.toNat + T * t) := by
          intro t₁ t₂ h
          exact Nat.eq_of_mul_eq_mul_left hTpos (Nat.add_left_cancel h)
        apply Set.infinite_of_injective_forall_mem hinj
        intro t
        rw [mem_fiberSetSG_zero, exists_w_iff_dvd]
        set c : ℤ := ((c₁.toNat + T * t : ℕ) : ℤ) with hc
        have hcZ : c = c₁ + (T : ℤ) * t := by
          rw [hc]; push_cast; rw [Int.toNat_of_nonneg hc₁nn]
        have hcong2 : (b ^ 2) ∣ (A * b * c + b * l - A * μ) := by
          have he : A * b * c + b * l - A * μ
              = (A * b * c₁ + b * l - A * μ) + b ^ 2 * (A * b * t) := by
            rw [hcZ, hTZ]; ring
          rw [he]
          exact dvd_add hc₁cong (Dvd.intro _ rfl)
        obtain ⟨e, he⟩ := hcong2
        refine ⟨e, ?_⟩
        apply mul_left_cancel₀ hb2
        calc b ^ 2 * (A * c ^ 2 + l * c + q)
            = (b * c + μ) * (A * b * c + b * l - A * μ) + R := by rw [hRdef]; ring
          _ = (b * c + μ) * (b ^ 2 * e) + 0 := by rw [he, hR]
          _ = b ^ 2 * ((b * c + μ) * e) := by ring
      · -- unsolvable congruence: fiber inside {bc + μ = 0}
        right
        intro c hc
        rw [mem_fiberSetSG_zero, exists_w_iff_dvd] at hc
        by_cases hzero : b * (c : ℤ) + μ = 0
        · have hcb : (c : ℤ) * b = -μ := by linarith
          have h1 : |(c : ℤ)| * |b| = |μ| := by
            rw [← abs_mul, hcb, abs_neg]
          have hcle : (c : ℤ) ≤ |μ| := by
            have h3 : |(c : ℤ)| = (c : ℤ) := Int.abs_natCast c
            nlinarith [Int.natCast_nonneg c]
          rw [hfb]
          calc (c : ℤ) ≤ |μ| := hcle
            _ ≤ (1 + |l| + |μ|) ^ 2 + |q| := by
              nlinarith [abs_nonneg l, abs_nonneg μ, abs_nonneg q]
            _ ≤ KZ * ((1 + |l| + |μ|) ^ 2 + |q|) :=
            le_mul_of_one_le_left hshape (by linarith)
        · exfalso
          apply hcong
          obtain ⟨g, hg⟩ := hc
          have hkey : b ^ 2 * (A * (c : ℤ) ^ 2 + l * (c : ℤ) + q)
              = (b * (c : ℤ) + μ) * (A * b * (c : ℤ) + b * l - A * μ) + R := by
            rw [hRdef]; ring
          rw [hg, hR, add_zero] at hkey
          have hkey2 : (b * (c : ℤ) + μ) * (b ^ 2 * g)
              = (b * (c : ℤ) + μ) * (A * b * (c : ℤ) + b * l - A * μ) := by
            linarith [hkey]
          exact ⟨c, ⟨g, (mul_left_cancel₀ hzero hkey2).symm⟩⟩
    · -- R ≠ 0: modulus bounded by |R|
      right
      intro c hc
      rw [mem_fiberSetSG_zero, exists_w_iff_dvd] at hc
      have hμshape : |μ| ≤ (1 + |l| + |μ|) ^ 2 + |q| := by
        nlinarith [abs_nonneg l, abs_nonneg μ, abs_nonneg q]
      have hRb : |R| ≤ (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|) := by
        have h1 : |R| ≤ |A| * |μ| ^ 2 + |b| * |l| * |μ| + |b| ^ 2 * |q| := by
          rw [hRdef]
          calc |A * μ ^ 2 - b * l * μ + b ^ 2 * q|
              ≤ |A * μ ^ 2 - b * l * μ| + |b ^ 2 * q| := abs_add_le _ _
            _ ≤ |A * μ ^ 2| + |b * l * μ| + |b ^ 2 * q| := by
                have := abs_sub_le' (A * μ ^ 2) (b * l * μ)
                linarith
            _ = |A| * |μ| ^ 2 + |b| * |l| * |μ| + |b| ^ 2 * |q| := by
                rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow]
        have hμ2 : |μ| ^ 2 ≤ (1 + |l| + |μ|) ^ 2 := by
          nlinarith [abs_nonneg l, abs_nonneg μ]
        have hlμ : |l| * |μ| ≤ (1 + |l| + |μ|) ^ 2 := by
          nlinarith [abs_nonneg l, abs_nonneg μ]
        have p1 : |A| * |μ| ^ 2 ≤ |A| * ((1 + |l| + |μ|) ^ 2 + |q|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
          linarith [abs_nonneg q]
        have p2 : |b| * |l| * |μ| ≤ |b| * ((1 + |l| + |μ|) ^ 2 + |q|) := by
          have h2' : |l| * |μ| ≤ (1 + |l| + |μ|) ^ 2 + |q| := by linarith [abs_nonneg q]
          calc |b| * |l| * |μ| = |b| * (|l| * |μ|) := by ring
            _ ≤ |b| * ((1 + |l| + |μ|) ^ 2 + |q|) :=
                mul_le_mul_of_nonneg_left h2' (abs_nonneg b)
        have p3 : |b| ^ 2 * |q| ≤ |b| ^ 2 * ((1 + |l| + |μ|) ^ 2 + |q|) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg |b|)
          nlinarith [abs_nonneg l, abs_nonneg μ]
        have hdist : (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
            = |A| * ((1 + |l| + |μ|) ^ 2 + |q|) + |b| * ((1 + |l| + |μ|) ^ 2 + |q|)
              + |b| ^ 2 * ((1 + |l| + |μ|) ^ 2 + |q|) := by ring
        linarith [h1, p1, p2, p3]
      by_cases hzero : b * (c : ℤ) + μ = 0
      · have hcb : (c : ℤ) * b = -μ := by linarith
        have h1 : |(c : ℤ)| * |b| = |μ| := by rw [← abs_mul, hcb, abs_neg]
        have hcle : (c : ℤ) ≤ |μ| := by
          have h3 : |(c : ℤ)| = (c : ℤ) := Int.abs_natCast c
          nlinarith [Int.natCast_nonneg c]
        rw [hfb]
        calc (c : ℤ) ≤ |μ| := hcle
          _ ≤ (1 + |l| + |μ|) ^ 2 + |q| := hμshape
          _ ≤ KZ * ((1 + |l| + |μ|) ^ 2 + |q|) :=
            le_mul_of_one_le_left hshape (by linarith)
      · have hdR : (b * (c : ℤ) + μ) ∣ R := by
          rw [hRdef]
          exact linear_modulus_divides_quadratic_remainder A l q b μ c hc
        have habs : |b * (c : ℤ) + μ| ≤ |R| := abs_le_abs_of_dvd hdR hR
        have hbc : |b * (c : ℤ)| ≤ |R| + |μ| := by
          have he : b * (c : ℤ) = (b * (c : ℤ) + μ) - μ := by ring
          calc |b * (c : ℤ)| = |(b * (c : ℤ) + μ) - μ| := by rw [← he]
            _ ≤ |b * (c : ℤ) + μ| + |μ| := abs_sub_le' _ _
            _ ≤ |R| + |μ| := by linarith
        have hcle : (c : ℤ) ≤ |R| + |μ| := by
          have h4 : |b * (c : ℤ)| = |b| * (c : ℤ) := by
            rw [abs_mul, Int.abs_natCast]
          nlinarith [Int.natCast_nonneg c]
        rw [hfb]
        calc (c : ℤ) ≤ |R| + |μ| := hcle
          _ ≤ (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
              + ((1 + |l| + |μ|) ^ 2 + |q|) := add_le_add hRb hμshape
          _ ≤ KZ * ((1 + |l| + |μ|) ^ 2 + |q|) := by
            rw [hKZ]
            have hdist2 : (|A| + |b| + |b| ^ 2 + 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
                = (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
                  + 2 * ((1 + |l| + |μ|) ^ 2 + |q|) := by ring
            linarith [hshape]


/-! ### s28 必須F step 3: the k₀ = 0 leaf in data form (all three infinite branches are
    progressions: the identity family, the μ-periodic family, and the b² progression). -/

set_option maxHeartbeats 2000000 in
theorem quotient_rank_zero_dichotomy_data (A b : ℤ) (B : Fin 0 → ℤ) (C : Matrix (Fin 0) (Fin 0) ℤ) :
    DichotomySGData A B C b := by
  refine ⟨A.natAbs + b.natAbs + b.natAbs ^ 2 + 2, fun l m μ q => ?_⟩
  set R : ℤ := A * μ ^ 2 - b * l * μ + b ^ 2 * q with hRdef
  set KZ : ℤ := ((A.natAbs + b.natAbs + b.natAbs ^ 2 + 2 : ℕ) : ℤ) with hKZdef
  have hKZ : KZ = |A| + |b| + |b| ^ 2 + 2 := by
    rw [hKZdef]
    push_cast [Int.natCast_natAbs]
    ring
  have hfb : fboundSG (A.natAbs + b.natAbs + b.natAbs ^ 2 + 2) l m μ q
      = KZ * ((1 + |l| + |μ|) ^ 2 + |q|) := by
    simp only [fboundSG, Finset.univ_eq_empty, Finset.sum_empty, add_zero, hKZdef]
  have hshape : (0 : ℤ) ≤ (1 + |l| + |μ|) ^ 2 + |q| := by positivity
  have hKZ2 : (2 : ℤ) ≤ KZ := by
    rw [hKZ]
    nlinarith [abs_nonneg A, abs_nonneg b, sq_nonneg |b|]
  clear_value R KZ
  by_cases hb : b = 0
  · -- fixed modulus μ
    subst hb
    by_cases hμ : μ = 0
    · -- no coupled variable: A c² + l c + q = 0
      subst hμ
      by_cases hA : A = 0
      · by_cases hl : l = 0
        · by_cases hq : q = 0
          · refine Or.inl ⟨DiophCompression.StructuredFamily.progression 0 1 le_rfl (fun n => ?_)⟩
            simp only [Nat.zero_add, Nat.one_mul]
            rw [mem_fiberSetSG_zero]
            exact ⟨0, by simp [hA, hl, hq]⟩
          · right
            intro c hc
            rw [mem_fiberSetSG_zero] at hc
            obtain ⟨w, hw⟩ := hc
            simp [hA, hl] at hw
            exact absurd hw hq
        · right
          intro c hc
          rw [mem_fiberSetSG_zero] at hc
          obtain ⟨w, hw⟩ := hc
          simp [hA] at hw
          have hlc : l * (c : ℤ) = -q := by linarith
          have h1 : |l| * (c : ℤ) = |q| := by
            rw [← Int.abs_natCast c, ← abs_mul, hlc, abs_neg]
          have h2 : 1 ≤ |l| := Int.one_le_abs (by exact_mod_cast hl)
          have hcle : (c : ℤ) ≤ |q| := by
            nlinarith [Int.natCast_nonneg c,
              mul_nonneg (Int.natCast_nonneg c) (sub_nonneg.mpr h2)]
          rw [hfb]
          calc (c : ℤ) ≤ |q| := hcle
            _ ≤ KZ * ((1 + |l| + |0|) ^ 2 + |q|) := by
              nlinarith [abs_nonneg l, abs_nonneg q, sq_nonneg (1 + |l|), hKZ2]
      · right
        intro c hc
        rw [mem_fiberSetSG_zero] at hc
        obtain ⟨w, hw⟩ := hc
        simp at hw
        have hA1 : 1 ≤ |A| := Int.one_le_abs (by exact_mod_cast hA)
        have h1 : A * (c : ℤ) ^ 2 = -(l * c + q) := by linarith
        have h2 : |A| * (c : ℤ) ^ 2 = |l * (c : ℤ) + q| := by
          calc |A| * (c : ℤ) ^ 2 = |A| * |(c : ℤ)| ^ 2 := by rw [Int.abs_natCast]
            _ = |A * (c : ℤ) ^ 2| := by rw [abs_mul, abs_pow]
            _ = |l * (c : ℤ) + q| := by rw [h1, abs_neg]
        have h3 : |l * (c : ℤ) + q| ≤ |l| * c + |q| := by
          calc |l * (c : ℤ) + q| ≤ |l * (c : ℤ)| + |q| := abs_add_le _ _
            _ = |l| * c + |q| := by rw [abs_mul, Int.abs_natCast]
        have hkey : (c : ℤ) ^ 2 ≤ |l| * c + |q| := by nlinarith [Int.natCast_nonneg c]
        have hcle : (c : ℤ) ≤ |l| + |q| + 1 := by
          nlinarith [Int.natCast_nonneg c, abs_nonneg l, abs_nonneg q]
        rw [hfb]
        simp only [abs_zero, add_zero]
        nlinarith [hcle, hKZ2, abs_nonneg l, abs_nonneg q,
          mul_nonneg (sub_nonneg.mpr hKZ2) (show (0:ℤ) ≤ (1 + |l|) ^ 2 + |q| by positivity),
          mul_nonneg (show (0:ℤ) ≤ 1 + |l| by positivity) (abs_nonneg l)]
    · -- μ ≠ 0: divisibility, μ-periodic
      have hM : 1 ≤ μ.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hμ)
      have hμd : μ ∣ |μ| := (dvd_abs μ μ).mpr dvd_rfl
      have hper : ∀ c : ℕ, c ∈ fiberSetSG A B C 0 l m μ q ↔
          c + μ.natAbs ∈ fiberSetSG A B C 0 l m μ q := by
        intro c
        rw [mem_fiberSetSG_zero, mem_fiberSetSG_zero]
        simp only [zero_mul, zero_add]
        rw [exists_w_iff_dvd, exists_w_iff_dvd]
        constructor
        · intro h
          push_cast
          have hEq : A * ((c : ℤ) + |μ|) ^ 2 + l * ((c : ℤ) + |μ|) + q
              = |μ| * (A * (2 * (c : ℤ) + |μ|) + l)
                + (A * (c : ℤ) ^ 2 + l * (c : ℤ) + q) := by ring
          rw [hEq]
          exact dvd_add (hμd.mul_right _) h
        · intro h
          push_cast at h
          have hEq : A * (c : ℤ) ^ 2 + l * (c : ℤ) + q
              = (A * ((c : ℤ) + |μ|) ^ 2 + l * ((c : ℤ) + |μ|) + q)
                - |μ| * (A * (2 * (c : ℤ) + |μ|) + l) := by ring
          rw [hEq]
          exact dvd_sub h (hμd.mul_right _)
      rcases DiophCompression.periodicProgression_or_empty
          (fiberSetSG A B C 0 l m μ q) μ.natAbs hM hper with hinf | hemp
      · exact Or.inl (hinf.elim fun F =>
          ⟨DiophCompression.PeriodicProgression.toStructuredFamily F⟩)
      · right
        rw [hemp]
        intro c hc
        exact absurd hc (Set.notMem_empty c)
  · -- b ≠ 0
    have hb1 : 1 ≤ |b| := Int.one_le_abs (by exact_mod_cast hb)
    by_cases hR : R = 0
    · by_cases hcong : ∃ c₀ : ℤ, (b ^ 2) ∣ (A * b * c₀ + b * l - A * μ)
      · -- infinite: an arithmetic progression lies in the fiber
        left
        obtain ⟨c₀, hc₀⟩ := hcong
        have hb2pos : (0 : ℤ) < b ^ 2 := by positivity
        have hb2 : (b : ℤ) ^ 2 ≠ 0 := ne_of_gt hb2pos
        set T : ℕ := (b ^ 2).natAbs with hT
        have hTpos : 0 < T := Int.natAbs_pos.mpr hb2
        have hTZ : (T : ℤ) = b ^ 2 := Int.natAbs_of_nonneg (le_of_lt hb2pos)
        set c₁ : ℤ := c₀ + (T : ℤ) * (|c₀| + 1) with hc₁
        have hc₁nn : 0 ≤ c₁ := by
          have h1 : (1 : ℤ) ≤ (T : ℤ) := by exact_mod_cast hTpos
          nlinarith [abs_nonneg c₀, neg_abs_le c₀]
        have hc₁cong : (b ^ 2) ∣ (A * b * c₁ + b * l - A * μ) := by
          have he : A * b * c₁ + b * l - A * μ
              = (A * b * c₀ + b * l - A * μ) + b ^ 2 * (A * b * (|c₀| + 1)) := by
            rw [hc₁, hTZ]; ring
          rw [he]
          exact dvd_add hc₀ (Dvd.intro _ rfl)
        refine ⟨DiophCompression.StructuredFamily.progression c₁.toNat T hTpos (fun t => ?_)⟩
        rw [mem_fiberSetSG_zero, exists_w_iff_dvd]
        set c : ℤ := ((c₁.toNat + T * t : ℕ) : ℤ) with hc
        have hcZ : c = c₁ + (T : ℤ) * t := by
          rw [hc]; push_cast; rw [Int.toNat_of_nonneg hc₁nn]
        have hcong2 : (b ^ 2) ∣ (A * b * c + b * l - A * μ) := by
          have he : A * b * c + b * l - A * μ
              = (A * b * c₁ + b * l - A * μ) + b ^ 2 * (A * b * t) := by
            rw [hcZ, hTZ]; ring
          rw [he]
          exact dvd_add hc₁cong (Dvd.intro _ rfl)
        obtain ⟨e, he⟩ := hcong2
        refine ⟨e, ?_⟩
        apply mul_left_cancel₀ hb2
        calc b ^ 2 * (A * c ^ 2 + l * c + q)
            = (b * c + μ) * (A * b * c + b * l - A * μ) + R := by rw [hRdef]; ring
          _ = (b * c + μ) * (b ^ 2 * e) + 0 := by rw [he, hR]
          _ = b ^ 2 * ((b * c + μ) * e) := by ring
      · -- unsolvable congruence: fiber inside {bc + μ = 0}
        right
        intro c hc
        rw [mem_fiberSetSG_zero, exists_w_iff_dvd] at hc
        by_cases hzero : b * (c : ℤ) + μ = 0
        · have hcb : (c : ℤ) * b = -μ := by linarith
          have h1 : |(c : ℤ)| * |b| = |μ| := by
            rw [← abs_mul, hcb, abs_neg]
          have hcle : (c : ℤ) ≤ |μ| := by
            have h3 : |(c : ℤ)| = (c : ℤ) := Int.abs_natCast c
            nlinarith [Int.natCast_nonneg c]
          rw [hfb]
          calc (c : ℤ) ≤ |μ| := hcle
            _ ≤ (1 + |l| + |μ|) ^ 2 + |q| := by
              nlinarith [abs_nonneg l, abs_nonneg μ, abs_nonneg q]
            _ ≤ KZ * ((1 + |l| + |μ|) ^ 2 + |q|) :=
            le_mul_of_one_le_left hshape (by linarith)
        · exfalso
          apply hcong
          obtain ⟨g, hg⟩ := hc
          have hkey : b ^ 2 * (A * (c : ℤ) ^ 2 + l * (c : ℤ) + q)
              = (b * (c : ℤ) + μ) * (A * b * (c : ℤ) + b * l - A * μ) + R := by
            rw [hRdef]; ring
          rw [hg, hR, add_zero] at hkey
          have hkey2 : (b * (c : ℤ) + μ) * (b ^ 2 * g)
              = (b * (c : ℤ) + μ) * (A * b * (c : ℤ) + b * l - A * μ) := by
            linarith [hkey]
          exact ⟨c, ⟨g, (mul_left_cancel₀ hzero hkey2).symm⟩⟩
    · -- R ≠ 0: modulus bounded by |R|
      right
      intro c hc
      rw [mem_fiberSetSG_zero, exists_w_iff_dvd] at hc
      have hμshape : |μ| ≤ (1 + |l| + |μ|) ^ 2 + |q| := by
        nlinarith [abs_nonneg l, abs_nonneg μ, abs_nonneg q]
      have hRb : |R| ≤ (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|) := by
        have h1 : |R| ≤ |A| * |μ| ^ 2 + |b| * |l| * |μ| + |b| ^ 2 * |q| := by
          rw [hRdef]
          calc |A * μ ^ 2 - b * l * μ + b ^ 2 * q|
              ≤ |A * μ ^ 2 - b * l * μ| + |b ^ 2 * q| := abs_add_le _ _
            _ ≤ |A * μ ^ 2| + |b * l * μ| + |b ^ 2 * q| := by
                have := abs_sub_le' (A * μ ^ 2) (b * l * μ)
                linarith
            _ = |A| * |μ| ^ 2 + |b| * |l| * |μ| + |b| ^ 2 * |q| := by
                rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow]
        have hμ2 : |μ| ^ 2 ≤ (1 + |l| + |μ|) ^ 2 := by
          nlinarith [abs_nonneg l, abs_nonneg μ]
        have hlμ : |l| * |μ| ≤ (1 + |l| + |μ|) ^ 2 := by
          nlinarith [abs_nonneg l, abs_nonneg μ]
        have p1 : |A| * |μ| ^ 2 ≤ |A| * ((1 + |l| + |μ|) ^ 2 + |q|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
          linarith [abs_nonneg q]
        have p2 : |b| * |l| * |μ| ≤ |b| * ((1 + |l| + |μ|) ^ 2 + |q|) := by
          have h2' : |l| * |μ| ≤ (1 + |l| + |μ|) ^ 2 + |q| := by linarith [abs_nonneg q]
          calc |b| * |l| * |μ| = |b| * (|l| * |μ|) := by ring
            _ ≤ |b| * ((1 + |l| + |μ|) ^ 2 + |q|) :=
                mul_le_mul_of_nonneg_left h2' (abs_nonneg b)
        have p3 : |b| ^ 2 * |q| ≤ |b| ^ 2 * ((1 + |l| + |μ|) ^ 2 + |q|) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg |b|)
          nlinarith [abs_nonneg l, abs_nonneg μ]
        have hdist : (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
            = |A| * ((1 + |l| + |μ|) ^ 2 + |q|) + |b| * ((1 + |l| + |μ|) ^ 2 + |q|)
              + |b| ^ 2 * ((1 + |l| + |μ|) ^ 2 + |q|) := by ring
        linarith [h1, p1, p2, p3]
      by_cases hzero : b * (c : ℤ) + μ = 0
      · have hcb : (c : ℤ) * b = -μ := by linarith
        have h1 : |(c : ℤ)| * |b| = |μ| := by rw [← abs_mul, hcb, abs_neg]
        have hcle : (c : ℤ) ≤ |μ| := by
          have h3 : |(c : ℤ)| = (c : ℤ) := Int.abs_natCast c
          nlinarith [Int.natCast_nonneg c]
        rw [hfb]
        calc (c : ℤ) ≤ |μ| := hcle
          _ ≤ (1 + |l| + |μ|) ^ 2 + |q| := hμshape
          _ ≤ KZ * ((1 + |l| + |μ|) ^ 2 + |q|) :=
            le_mul_of_one_le_left hshape (by linarith)
      · have hdR : (b * (c : ℤ) + μ) ∣ R := by
          rw [hRdef]
          exact linear_modulus_divides_quadratic_remainder A l q b μ c hc
        have habs : |b * (c : ℤ) + μ| ≤ |R| := abs_le_abs_of_dvd hdR hR
        have hbc : |b * (c : ℤ)| ≤ |R| + |μ| := by
          have he : b * (c : ℤ) = (b * (c : ℤ) + μ) - μ := by ring
          calc |b * (c : ℤ)| = |(b * (c : ℤ) + μ) - μ| := by rw [← he]
            _ ≤ |b * (c : ℤ) + μ| + |μ| := abs_sub_le' _ _
            _ ≤ |R| + |μ| := by linarith
        have hcle : (c : ℤ) ≤ |R| + |μ| := by
          have h4 : |b * (c : ℤ)| = |b| * (c : ℤ) := by
            rw [abs_mul, Int.abs_natCast]
          nlinarith [Int.natCast_nonneg c]
        rw [hfb]
        calc (c : ℤ) ≤ |R| + |μ| := hcle
          _ ≤ (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
              + ((1 + |l| + |μ|) ^ 2 + |q|) := add_le_add hRb hμshape
          _ ≤ KZ * ((1 + |l| + |μ|) ^ 2 + |q|) := by
            rw [hKZ]
            have hdist2 : (|A| + |b| + |b| ^ 2 + 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
                = (|A| + |b| + |b| ^ 2) * ((1 + |l| + |μ|) ^ 2 + |q|)
                  + 2 * ((1 + |l| + |μ|) ^ 2 + |q|) := by ring
            linarith [hshape]

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.linear_modulus_divides_quadratic_remainder
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_zero_bounded_or_infinite
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_zero_dichotomy
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_zero_dichotomy_data
