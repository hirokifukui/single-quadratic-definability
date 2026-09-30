/-
  DiophCompression/SemanticQuadratic/LeafDataD3D6.lean — APAL Structural Theory Gate 5, 必須F step 2
  pilot (leaves D3, D4, D6) (s28, 2026-09-02, claude.ai direct).

  The three lightest leaves of the branch table, re-proved in DATA-CARRYING form. The original proofs
  already build the family `c ↦ c₀ + s·t` with its witnesses and hand it to `fiberSet_infinite_of_family`,
  which throws the data away and returns `Set.Infinite`. Here the same proofs return the family itself, so
  the leaf can feed the 必須D packagers instead of a bare infinitude. The proof scripts are the ORIGINALS,
  transformed only by (i) replacing that one call with the smart constructor `linearFamily_nonempty`
  (identical argument order) and (ii) in D4, changing the conclusion of the `where` helper accordingly.
  The bounded branches are untouched, and each data form is shown to imply the sealed leaf. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.FiberDefs
import DiophCompression.SemanticQuadratic.Class_D4

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- The linear family a degenerate leaf produces: base `c₀`, positive step `s`, witnesses `ut`. -/
structure LinearFiberFamily (A B C l m q : ℤ) where
  c₀ : ℕ
  s : ℕ
  s_pos : 1 ≤ s
  ut : ℕ → ℤ
  fam : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (ut t) = 0

/-- Smart constructor with EXACTLY the argument order of `fiberSet_infinite_of_family`, so that the
    original proof scripts convert by a single identifier substitution. -/
theorem linearFamily_nonempty (A B C l m q : ℤ) (c₀ : ℕ) (s : ℕ) (hs : 1 ≤ s)
    (ut : ℕ → ℤ) (hfam : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (ut t) = 0) :
    Nonempty (LinearFiberFamily A B C l m q) :=
  ⟨⟨c₀, s, hs, ut, hfam⟩⟩

/-- Soundness: the family really does make the fibre infinite. -/
theorem fiberSet_infinite_of_linearFamily {A B C l m q : ℤ} (F : LinearFiberFamily A B C l m q) :
    (fiberSet A B C l m q).Infinite := by
  apply Set.infinite_of_not_bddAbove
  intro ⟨M, hM⟩
  have hmem : F.c₀ + F.s * (M + 1) ∈ fiberSet A B C l m q := ⟨F.ut (M + 1), F.fam (M + 1)⟩
  have := hM hmem
  have hs := F.s_pos
  nlinarith

/-- The data-carrying dichotomy of a degenerate leaf. -/
def DichotomyLinearData (A B C : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m q : ℤ, Nonempty (LinearFiberFamily A B C l m q) ∨
    ∀ c ∈ fiberSet A B C l m q, (c : ℤ) ≤ fbound K l m q

/-- The data form implies the sealed form: nothing is lost by strengthening. -/
theorem dichotomy_of_dichotomyLinearData {A B C : ℤ} (h : DichotomyLinearData A B C) :
    Dichotomy A B C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m q => ?_⟩
  rcases hK l m q with hfam | hb
  · exact Or.inl (hfam.elim fun F => fiberSet_infinite_of_linearFamily F)
  · exact Or.inr hb

/-! ### Branch D3 (disc = 0, C = 0) in data form -/

theorem dichotomy_degenerate_C_zero_data (A B C : ℤ) (h : disc A B C = 0) (hC : C = 0) : DichotomyLinearData A B C := by
  subst hC
  have hB : B = 0 := by
    unfold disc at h
    have : B ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  subst hB
  refine ⟨(|A| + 1).toNat, ?_⟩
  have hK : (((|A| + 1).toNat : ℕ) : ℤ) = |A| + 1 := by
    rw [Int.toNat_of_nonneg]; have := abs_nonneg A; omega
  intro l m q
  by_cases hm : m = 0
  · subst hm
    by_cases hA : A = 0
    · subst hA
      by_cases hl : l = 0
      · subst hl
        by_cases hq : q = 0
        · subst hq
          left
          exact linearFamily_nonempty 0 0 0 0 0 0 0 1 le_rfl (fun _ => 0)
            (fun t => by simp [fq])
        · right
          intro c hc
          obtain ⟨u, hu⟩ := hc
          simp [fq] at hu
          exact absurd hu hq
      · right
        intro c hc
        obtain ⟨u, hu⟩ := hc
        simp only [fq] at hu
        have hlc : l * (c : ℤ) = -q := by linarith
        have h1 : |l| * |(c : ℤ)| = |q| := by rw [← abs_mul, hlc, abs_neg]
        have hl1 : 1 ≤ |l| := Int.one_le_abs hl
        have hc0 : |(c : ℤ)| = c := abs_of_nonneg (by exact_mod_cast Nat.zero_le c)
        rw [hc0] at h1
        unfold fbound; rw [hK]; simp only [abs_zero, add_zero, zero_add]
        have := abs_nonneg l; have := abs_nonneg q
        have hcl : (c : ℤ) ≤ |q| := by nlinarith
        nlinarith [sq_nonneg (1 + |l|)]
    · right
      intro c hc
      obtain ⟨u, hu⟩ := hc
      simp only [fq] at hu
      have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
      have hA1 : 1 ≤ |A| := Int.one_le_abs hA
      -- |A| c^2 = |l c + q| ≤ |l| c + |q|
      have h1 : |A| * (c : ℤ) ^ 2 ≤ |l| * c + |q| := by
        have e : A * (c : ℤ) ^ 2 = -(l * c + q) := by linarith
        have : |A| * (c : ℤ) ^ 2 = |l * c + q| := by
          rw [← abs_of_nonneg (sq_nonneg (c : ℤ)), ← abs_mul, e, abs_neg]
        rw [this]
        calc |l * (c : ℤ) + q| ≤ |l * c| + |q| := abs_add_le _ _
          _ = |l| * c + |q| := by rw [abs_mul, abs_of_nonneg hc0]
      have h2 : (c : ℤ) ≤ |l| + |q| := by
        by_contra hcon
        push Not at hcon
        have hpos : (0 : ℤ) < c := by have := abs_nonneg l; have := abs_nonneg q; omega
        nlinarith [abs_nonneg l, abs_nonneg q]
      unfold fbound; rw [hK, abs_zero, add_zero]
      have := abs_nonneg A; have := abs_nonneg l; have := abs_nonneg q
      nlinarith [sq_nonneg (1 + |l|), mul_nonneg (abs_nonneg A) (abs_nonneg l),
        mul_nonneg (abs_nonneg A) (abs_nonneg q), mul_nonneg (abs_nonneg A) (sq_nonneg (1 + |l|))]
  · -- m ≠ 0: infinite if nonempty
    by_cases hne : ∃ c ∈ fiberSet A 0 0 l m q, True
    · left
      obtain ⟨c₀, ⟨u₀, hu₀⟩, -⟩ := hne
      have hs : 1 ≤ (m ^ 2).toNat := by
        have : 1 ≤ m ^ 2 := by nlinarith [Int.one_le_abs hm, sq_abs m, abs_nonneg m]
        omega
      refine linearFamily_nonempty A 0 0 l m q c₀ (m ^ 2).toNat hs
        (fun t => u₀ - (2 * A * c₀ * m * t + A * m ^ 3 * t ^ 2 + l * m * t)) ?_
      intro t
      have hm2 : (((m ^ 2).toNat : ℕ) : ℤ) = m ^ 2 := Int.toNat_of_nonneg (sq_nonneg m)
      push_cast
      rw [hm2]
      simp only [fq] at hu₀ ⊢
      linear_combination hu₀
    · right
      intro c hc
      exact absurd ⟨c, hc, trivial⟩ hne

/-! ### Branch D6 (disc > 0 a square, C = 0) in data form -/

theorem dichotomy_square_C_zero_data (A B C : ℤ) (h : 0 < disc A B C) (hC : C = 0) : DichotomyLinearData A B C := by
  subst hC
  have hB : B ≠ 0 := by
    intro hB0; subst hB0; unfold disc at h; norm_num at h
  have hB1 : 1 ≤ |B| := Int.one_le_abs hB
  refine ⟨(B ^ 2 + |B| + |A| + 1).toNat, ?_⟩
  have hK : (((B ^ 2 + |B| + |A| + 1).toNat : ℕ) : ℤ) = B ^ 2 + |B| + |A| + 1 := by
    rw [Int.toNat_of_nonneg]; have := abs_nonneg A; have := abs_nonneg B; have := sq_nonneg B; omega
  intro l m q
  have hl := abs_nonneg l; have hm := abs_nonneg m; have hq := abs_nonneg q; have hA := abs_nonneg A
  have hBsq : (0 : ℤ) ≤ B ^ 2 := sq_nonneg B
  -- bound of a c with B c + m = 0
  have hzero_bound : ∀ c : ℕ, B * (c : ℤ) + m = 0 → (c : ℤ) ≤ |m| := by
    intro c hc
    have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
    have : |B| * (c : ℤ) = |m| := by
      rw [← abs_of_nonneg hc0, ← abs_mul, show B * (c : ℤ) = -m by linarith, abs_neg]
    nlinarith
  have hfb : ∀ c : ℕ, (c : ℤ) ≤ |m| → (c : ℤ) ≤ fbound (B ^ 2 + |B| + |A| + 1).toNat l m q := by
    intro c hc; unfold fbound; rw [hK]
    nlinarith [sq_nonneg (1 + |l| + |m|), mul_nonneg hBsq hq, mul_nonneg hBsq (sq_nonneg (1 + |l| + |m|)),
      mul_nonneg (abs_nonneg B) (sq_nonneg (1 + |l| + |m|)), mul_nonneg hA (sq_nonneg (1 + |l| + |m|)),
      mul_nonneg hBsq hq, mul_nonneg (abs_nonneg B) hq, mul_nonneg hA hq]
  by_cases hall : ∀ c ∈ fiberSet A B 0 l m q, B * (c : ℤ) + m = 0
  · right
    intro c hc
    exact hfb c (hzero_bound c (hall c hc))
  · push Not at hall
    obtain ⟨c₁, ⟨u₁, hu₁⟩, hne⟩ := hall
    simp only [fq] at hu₁
    set R := B ^ 2 * q - B * l * m + A * m ^ 2 with hR
    -- (B c₁ + m) * (B² u₁ + A B c₁ + B l - A m) = -R
    have hkey : (B * (c₁ : ℤ) + m) * (B ^ 2 * u₁ + A * B * c₁ + B * l - A * m) = -R := by
      rw [hR]; linear_combination B ^ 2 * hu₁
    by_cases hR0 : R = 0
    · left
      have hu₁' : B ^ 2 * u₁ = -(A * B * (c₁ : ℤ) + B * l - A * m) := by
        have h0 : (B * (c₁ : ℤ) + m) * (B ^ 2 * u₁ + A * B * c₁ + B * l - A * m) = 0 := by
          rw [hkey, hR0, neg_zero]
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact absurd h1 hne
        · linarith
      have hs : 1 ≤ (B ^ 2).toNat := by
        have : 1 ≤ B ^ 2 := by nlinarith [sq_abs B]
        omega
      refine linearFamily_nonempty A B 0 l m q c₁ (B ^ 2).toNat hs (fun t => u₁ - A * B * t) ?_
      intro t
      have hB2 : (((B ^ 2).toNat : ℕ) : ℤ) = B ^ 2 := Int.toNat_of_nonneg hBsq
      push_cast
      rw [hB2]
      simp only [fq]
      have hB2ne : B ^ 2 ≠ 0 := pow_ne_zero 2 hB
      apply mul_left_cancel₀ hB2ne
      rw [mul_zero]
      linear_combination (B * (c₁ : ℤ) + m + B ^ 2 * B * t) * hu₁' + hR0 + B ^ 2 * hu₁
        - B ^ 2 * hu₁
    · right
      intro c hc
      obtain ⟨u, hu⟩ := hc
      simp only [fq] at hu
      by_cases hz : B * (c : ℤ) + m = 0
      · exact hfb c (hzero_bound c hz)
      · have hdvd : (B * (c : ℤ) + m) ∣ R := by
          refine ⟨-(B ^ 2 * u + A * B * c + B * l - A * m), ?_⟩
          rw [hR]; linear_combination B ^ 2 * hu
        have hle : |B * (c : ℤ) + m| ≤ |R| :=
          Int.le_of_dvd (abs_pos.mpr hR0) ((abs_dvd_abs _ _).mpr hdvd)
        have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
        have h1 : |B| * (c : ℤ) ≤ |R| + |m| := by
          have : |B * (c : ℤ)| ≤ |B * c + m| + |m| := by
            calc |B * (c : ℤ)| = |(B * c + m) - m| := by ring_nf
              _ ≤ |B * (c : ℤ) + m| + |m| := abs_sub _ _
          rw [abs_mul, abs_of_nonneg hc0] at this
          linarith
        have h2 : (c : ℤ) ≤ |R| + |m| := by nlinarith [abs_nonneg R]
        have hRb : |R| ≤ B ^ 2 * |q| + |B| * |l| * |m| + |A| * |m| ^ 2 := by
          rw [hR]
          calc |B ^ 2 * q - B * l * m + A * m ^ 2|
              ≤ |B ^ 2 * q - B * l * m| + |A * m ^ 2| := abs_add_le _ _
            _ ≤ |B ^ 2 * q| + |B * l * m| + |A * m ^ 2| := by linarith [abs_sub (B ^ 2 * q) (B * l * m)]
            _ = B ^ 2 * |q| + |B| * |l| * |m| + |A| * |m| ^ 2 := by simp [abs_mul, sq_abs]
        unfold fbound; rw [hK]
        set S := (1 + |l| + |m|) ^ 2 with hS
        have hS0 : 0 ≤ S := sq_nonneg _
        have e1 : |l| * |m| ≤ S := by rw [hS]; nlinarith
        have e2 : |m| ^ 2 ≤ S := by rw [hS]; nlinarith
        have e3 : |m| ≤ S := by rw [hS]; nlinarith
        have f1 : B ^ 2 * |q| ≤ B ^ 2 * (S + |q|) := by nlinarith
        have f2 : |B| * |l| * |m| ≤ |B| * (S + |q|) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg B)
        have f3 : |A| * |m| ^ 2 ≤ |A| * (S + |q|) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
        have f4 : |m| ≤ 1 * (S + |q|) := by rw [one_mul]; linarith
        have hR2 : (c : ℤ) ≤ B ^ 2 * (S + |q|) + |B| * (S + |q|) + |A| * (S + |q|) + 1 * (S + |q|) := by
          linarith [h2, hRb, f1, f2, f3, f4]
        calc (c : ℤ) ≤ B ^ 2 * (S + |q|) + |B| * (S + |q|) + |A| * (S + |q|) + 1 * (S + |q|) := hR2
          _ = (B ^ 2 + |B| + |A| + 1) * (S + |q|) := by ring

/-! ### Branch D4 (disc > 0 a square, C ≠ 0) in data form -/

theorem dichotomy_square_C_ne_data (A B C : ℤ) (h : 0 < disc A B C) (hs : IsSquare (disc A B C)) (hC : C ≠ 0) :
    DichotomyLinearData A B C := by
  obtain ⟨r, hr⟩ := hs
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℤ, δ = |r| := ⟨_, rfl⟩
  have hδsq : δ ^ 2 = B ^ 2 - 4 * A * C := by rw [hδdef, sq_abs, sq, ← hr]; rfl
  have hδpos : 1 ≤ δ := by
    have : r ≠ 0 := by rintro rfl; simp at hr; rw [hr] at h; exact lt_irrefl _ h
    rw [hδdef]; exact Int.one_le_abs this
  have hC1 : 1 ≤ |C| := Int.one_le_abs hC
  have hl' := abs_nonneg B; have hC' := abs_nonneg C
  refine ⟨((2 * |B| + 4 * |C|) ^ 2 + 4 * disc A B C * (1 + 4 * |C|) + 2 * |B| + 4 * |C|).toNat, ?_⟩
  have hK : ((((2 * |B| + 4 * |C|) ^ 2 + 4 * disc A B C * (1 + 4 * |C|) + 2 * |B| + 4 * |C|).toNat : ℕ) : ℤ)
      = (2 * |B| + 4 * |C|) ^ 2 + 4 * disc A B C * (1 + 4 * |C|) + 2 * |B| + 4 * |C| := by
    rw [Int.toNat_of_nonneg]; have := sq_nonneg (2 * |B| + 4 * |C|); positivity
  intro l m q
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, β = 2 * B * m - 4 * C * l := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℤ, γ = m ^ 2 - 4 * C * q := ⟨_, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N' : ℤ, N' = β ^ 2 - 4 * δ ^ 2 * γ := ⟨_, rfl⟩
  have hl := abs_nonneg l; have hm := abs_nonneg m; have hq := abs_nonneg q
  -- shared bounds
  have hβb : |β| ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := by
    rw [hβ]
    calc |2 * B * m - 4 * C * l| ≤ |2 * B * m| + |4 * C * l| := abs_sub _ _
      _ = 2 * |B| * |m| + 4 * |C| * |l| := by simp [abs_mul]
      _ ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := by nlinarith [mul_nonneg hl' hl, mul_nonneg hC' hm]
  have hγb : |γ| ≤ |m| ^ 2 + 4 * |C| * |q| := by
    rw [hγ]
    calc |m ^ 2 - 4 * C * q| ≤ |m ^ 2| + |4 * C * q| := abs_sub _ _
      _ = |m| ^ 2 + 4 * |C| * |q| := by simp [abs_mul, sq_abs]
  by_cases hN0 : N' = 0
  · -- infinite (if nonempty)
    by_cases hne : ∃ c ∈ fiberSet A B C l m q, True
    · left
      obtain ⟨c₀, ⟨u₀, hu₀⟩, -⟩ := hne
      -- from the key identity: (2δ w₀)^2 = X₀^2 (N' = 0)
      have hkey : 4 * C * fq A B C l m q c₀ u₀
          = (2 * C * u₀ + B * c₀ + m) ^ 2 - (disc A B C * (c₀ : ℤ) ^ 2 + β * c₀ + γ) := by
        unfold fq disc; rw [hβ, hγ]; ring
      rw [hu₀, mul_zero] at hkey
      have hsq : (2 * δ * (2 * C * u₀ + B * c₀ + m)) ^ 2 = (2 * δ ^ 2 * c₀ + β) ^ 2 := by
        have hd : disc A B C = δ ^ 2 := by unfold disc; rw [hδsq]
        rw [hd] at hkey
        have : N' = 0 := hN0
        rw [hN'] at this
        nlinarith [hkey, this]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hY | hY
      · -- s = 1
        exact square_branch_data A B C l m q δ 1 c₀ u₀ (by norm_num) hδsq hδpos hC (by rw [hN', hβ, hγ] at hN0; exact hN0)
          (by rw [one_mul, ← hβ]; exact hY)
      · exact square_branch_data A B C l m q δ (-1) c₀ u₀ (by norm_num) hδsq hδpos hC (by rw [hN', hβ, hγ] at hN0; exact hN0)
          (by rw [neg_one_mul, ← hβ]; exact hY)
    · right; intro c hc; exact absurd ⟨c, hc, trivial⟩ hne
  · right
    intro c hc
    obtain ⟨u, hu⟩ := hc
    have hkey : 4 * C * fq A B C l m q c u
        = (2 * C * u + B * c + m) ^ 2 - (disc A B C * (c : ℤ) ^ 2 + β * c + γ) := by
      unfold fq disc; rw [hβ, hγ]; ring
    rw [hu, mul_zero] at hkey
    have hd : disc A B C = δ ^ 2 := by unfold disc; rw [hδsq]
    rw [hd] at hkey
    have hfac0 : ((2 * δ ^ 2 * (c : ℤ) + β) - 2 * δ * (2 * C * u + B * c + m))
        * ((2 * δ ^ 2 * (c : ℤ) + β) + 2 * δ * (2 * C * u + B * c + m)) = N' := by
      rw [hN']; linear_combination 4 * δ ^ 2 * hkey
    obtain ⟨X, hX⟩ : ∃ X : ℤ, X = 2 * δ ^ 2 * (c : ℤ) + β := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = 2 * δ * (2 * C * u + B * c + m) := ⟨_, rfl⟩
    have hfac : (X - Y) * (X + Y) = N' := by rw [hX, hY]; exact hfac0
    have hXY1 : X - Y ≠ 0 := by intro h0; apply hN0; rw [← hfac, h0, zero_mul]
    have hXY2 : X + Y ≠ 0 := by intro h0; apply hN0; rw [← hfac, h0, mul_zero]
    have hd1 : |X - Y| ≤ |N'| := Int.le_of_dvd (abs_pos.mpr hN0) ((abs_dvd_abs _ _).mpr ⟨X + Y, hfac.symm⟩)
    have hd2 : |X + Y| ≤ |N'| := Int.le_of_dvd (abs_pos.mpr hN0) ((abs_dvd_abs _ _).mpr ⟨X - Y, by rw [← hfac]; ring⟩)
    have hXle : |X| ≤ |N'| := by
      have : |2 * X| ≤ |X - Y| + |X + Y| := by
        calc |2 * X| = |(X - Y) + (X + Y)| := by ring_nf
          _ ≤ |X - Y| + |X + Y| := abs_add_le _ _
      rw [abs_mul, abs_two] at this; linarith
    have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
    have hcX : 2 * δ ^ 2 * (c : ℤ) ≤ |N'| + |β| := by
      have : 2 * δ ^ 2 * (c : ℤ) = X - β := by rw [hX]; ring
      rw [this]; linarith [le_abs_self (X - β), abs_sub X β, hXle]
    have hδ2 : (1 : ℤ) ≤ δ ^ 2 := one_le_pow₀ hδpos
    have hc1 : (c : ℤ) ≤ |N'| + |β| := by
      have : (c : ℤ) ≤ 2 * δ ^ 2 * c := le_mul_of_one_le_left hc0 (by linarith)
      linarith
    have hN'b : |N'| ≤ β ^ 2 + 4 * δ ^ 2 * |γ| := by
      rw [hN']
      calc |β ^ 2 - 4 * δ ^ 2 * γ| ≤ |β ^ 2| + |4 * δ ^ 2 * γ| := abs_sub _ _
        _ = β ^ 2 + 4 * δ ^ 2 * |γ| := by
          rw [abs_of_nonneg (sq_nonneg β), abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ 4 * δ ^ 2)]
    unfold fbound; rw [hK, hd]
    obtain ⟨S, hS⟩ : ∃ S : ℤ, S = (1 + |l| + |m|) ^ 2 := ⟨_, rfl⟩
    rw [← hS]
    have hS0 : 0 ≤ S := by rw [hS]; exact sq_nonneg _
    have hx0 : (1 : ℤ) ≤ 1 + |l| + |m| := by linarith
    have hx1 : 1 + |l| + |m| ≤ S := by rw [hS]; exact le_self_pow₀ hx0 (by norm_num)
    have hβ0 := abs_nonneg β
    have hb1 : β ^ 2 ≤ (2 * |B| + 4 * |C|) ^ 2 * S := by
      rw [← sq_abs β, hS, ← mul_pow]
      exact pow_le_pow_left₀ hβ0 hβb 2
    have hb2 : |β| ≤ (2 * |B| + 4 * |C|) * S := by
      calc |β| ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := hβb
        _ ≤ (2 * |B| + 4 * |C|) * S := mul_le_mul_of_nonneg_left hx1 (by positivity)
    have hm2 : |m| ^ 2 ≤ S := by rw [hS]; exact pow_le_pow_left₀ hm (by linarith) 2
    have hb3 : 4 * δ ^ 2 * |γ| ≤ 4 * δ ^ 2 * (1 + 4 * |C|) * (S + |q|) := by
      have h1 : |γ| ≤ (1 + 4 * |C|) * (S + |q|) := by
        have g1 : 4 * |C| * |q| ≤ 4 * |C| * (S + |q|) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have g2 : |m| ^ 2 ≤ 1 * (S + |q|) := by rw [one_mul]; linarith
        linarith [hγb]
      calc 4 * δ ^ 2 * |γ| ≤ 4 * δ ^ 2 * ((1 + 4 * |C|) * (S + |q|)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * δ ^ 2 * (1 + 4 * |C|) * (S + |q|) := by ring
    have hfin : (c : ℤ) ≤ (2 * |B| + 4 * |C|) ^ 2 * (S + |q|) + 4 * δ ^ 2 * (1 + 4 * |C|) * (S + |q|)
        + (2 * |B| + 4 * |C|) * (S + |q|) := by
      have hSq : S ≤ S + |q| := by linarith
      have e1 : (2 * |B| + 4 * |C|) ^ 2 * S ≤ (2 * |B| + 4 * |C|) ^ 2 * (S + |q|) :=
        mul_le_mul_of_nonneg_left hSq (sq_nonneg _)
      have e2 : (2 * |B| + 4 * |C|) * S ≤ (2 * |B| + 4 * |C|) * (S + |q|) :=
        mul_le_mul_of_nonneg_left hSq (by linarith)
      linarith only [hc1, hN'b, hb1, hb2, hb3, e1, e2]
    calc (c : ℤ) ≤ _ := hfin
      _ = ((2 * |B| + 4 * |C|) ^ 2 + 4 * δ ^ 2 * (1 + 4 * |C|) + 2 * |B| + 4 * |C|) * (S + |q|) := by ring
where
  /-- The infinite branch for a given sign s ∈ {1, −1}. -/
  square_branch_data (A B C l m q δ s : ℤ) (c₀ : ℕ) (u₀ : ℤ) (hs : s * s = 1) (hδsq : δ ^ 2 = B ^ 2 - 4 * A * C)
      (hδpos : 1 ≤ δ) (hC : C ≠ 0)
      (hN : (2 * B * m - 4 * C * l) ^ 2 - 4 * δ ^ 2 * (m ^ 2 - 4 * C * q) = 0)
      (hY : 2 * δ * (2 * C * u₀ + B * c₀ + m) = s * (2 * δ ^ 2 * c₀ + (2 * B * m - 4 * C * l))) :
      Nonempty (LinearFiberFamily A B C l m q) := by
    -- σ = sign of C, so that 2 σ C δ = 2 |C| δ ≥ 2
    obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, σ * C = |C| := by
      rcases lt_or_gt_of_ne hC with hneg | hpos
      · exact ⟨-1, by rw [abs_of_neg hneg]; ring⟩
      · exact ⟨1, by rw [abs_of_pos hpos]; ring⟩
    have hC1 : 1 ≤ |C| := Int.one_le_abs hC
    have hstep : 1 ≤ (2 * |C| * δ).toNat := by
      have : 1 ≤ 2 * |C| * δ := by nlinarith
      omega
    refine linearFamily_nonempty A B C l m q c₀ (2 * |C| * δ).toNat hstep
      (fun t => u₀ + σ * (s * δ ^ 2 - B * δ) * t) ?_
    intro t
    have hcast : (((2 * |C| * δ).toNat : ℕ) : ℤ) = 2 * σ * C * δ := by
      rw [Int.toNat_of_nonneg (by positivity), ← hσ]; ring
    push_cast
    rw [hcast]
    have hid := square_family_identity A B C l m q δ s σ c₀ u₀ t hs hδsq hN hY
    have hne : 4 * δ ^ 2 * (4 * C) ≠ 0 := by positivity
    have : 4 * δ ^ 2 * (4 * C) * fq A B C l m q (↑c₀ + 2 * σ * C * δ * ↑t) (u₀ + σ * (s * δ ^ 2 - B * δ) * ↑t) = 0 := by
      rw [mul_assoc]; exact hid
    exact (mul_eq_zero.mp this).resolve_left hne

/-! ### Each data form still implies the sealed leaf. -/

theorem dichotomy_degenerate_C_zero_of_data (A B C : ℤ) (h : disc A B C = 0) (hC : C = 0) :
    Dichotomy A B C :=
  dichotomy_of_dichotomyLinearData (dichotomy_degenerate_C_zero_data A B C h hC)

theorem dichotomy_square_C_zero_of_data (A B C : ℤ) (h : 0 < disc A B C) (hC : C = 0) :
    Dichotomy A B C :=
  dichotomy_of_dichotomyLinearData (dichotomy_square_C_zero_data A B C h hC)

theorem dichotomy_square_C_ne_of_data (A B C : ℤ) (h : 0 < disc A B C) (hs : IsSquare (disc A B C))
    (hC : C ≠ 0) : Dichotomy A B C :=
  dichotomy_of_dichotomyLinearData (dichotomy_square_C_ne_data A B C h hs hC)

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.linearFamily_nonempty
#print axioms DiophCompression.SemanticQuadratic.fiberSet_infinite_of_linearFamily
#print axioms DiophCompression.SemanticQuadratic.dichotomy_of_dichotomyLinearData
#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_zero_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_zero_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_ne_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_zero_of_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_zero_of_data
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_ne_of_data
