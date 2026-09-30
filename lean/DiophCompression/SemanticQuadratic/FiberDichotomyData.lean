/-
  DiophCompression/SemanticQuadratic/FiberDichotomyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (the one-witness aggregation) (s28, 2026-09-02, claude.ai direct).

  `fiber_dichotomy` dispatches the one-witness normal form to its leaves D1–D7 and returns `Dichotomy`,
  whose infinite side is bare `Set.Infinite`. Here the same ten-line dispatch is carried out at the DATA
  level: the leaves already converted in s28 (D1 bounded, D3/D4/D6 linear) are discharged, and the two
  still owed (D2 quadratic, D7 Pell — both have their families proved, only their dichotomy wrappers are
  not yet converted) appear as explicit hypotheses, so what remains is visible in the statement rather
  than hidden in prose. The data form implies the sealed one. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.FiberDichotomy
import DiophCompression.SemanticQuadratic.OneWitnessFamilyData

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- The one-witness dichotomy in data-carrying form. -/
def DichotomyOneWitnessData (A B C : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m q : ℤ, Nonempty (OneWitnessFamilyData A B C l m q) ∨
    ∀ c ∈ fiberSet A B C l m q, (c : ℤ) ≤ fbound K l m q

/-- The data form implies the sealed form: strengthening loses nothing. -/
theorem dichotomy_of_dichotomyOneWitnessData {A B C : ℤ} (h : DichotomyOneWitnessData A B C) :
    Dichotomy A B C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m q => ?_⟩
  rcases hK l m q with hF | hb
  · exact Or.inl (hF.elim fun F => fiberSet_infinite_of_oneWitnessFamilyData F)
  · exact Or.inr hb

/-- The linear leaves (D3, D4, D6) feed the aggregation through the `linear` constructor. -/
theorem dichotomyOneWitnessData_of_linear {A B C : ℤ} (h : DichotomyLinearData A B C) :
    DichotomyOneWitnessData A B C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m q => ?_⟩
  rcases hK l m q with hF | hb
  · exact Or.inl (hF.elim fun F => ⟨.linear F.c₀ F.s F.s_pos F.ut F.fam⟩)
  · exact Or.inr hb

/-! ### Leaf D1 (negative discriminant): always bounded, so the data form is the sealed proof verbatim -/

theorem dichotomy_definite_data (A B C : ℤ) (h : disc A B C < 0) : DichotomyOneWitnessData A B C := by
  refine ⟨(4 * |C| + 2 * |B| + 1).toNat, ?_⟩
  intro l m q
  right
  intro c hc
  obtain ⟨u, hu⟩ := hc
  have key := key_identity A B C l m q (c : ℤ) u
  rw [hu, mul_zero] at key
  set w := 2 * C * u + B * (c : ℤ) + m with hw
  set β := 2 * B * m - 4 * C * l with hβ
  set γ := m ^ 2 - 4 * C * q with hγ
  have hsq : 0 ≤ w ^ 2 := sq_nonneg w
  have hD : disc A B C ≤ -1 := by omega
  have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
  -- c^2 ≤ |β| c + |γ|
  have h1 : (c : ℤ) ^ 2 ≤ |β| * c + |γ| := by
    have hβc : β * c ≤ |β| * c := mul_le_mul_of_nonneg_right (le_abs_self β) hc0
    have hγ' : γ ≤ |γ| := le_abs_self γ
    nlinarith [hsq, hD, sq_nonneg (c : ℤ)]
  -- hence c ≤ |β| + |γ|
  have h2 : (c : ℤ) ≤ |β| + |γ| := by
    by_contra hcon
    push Not at hcon
    have hpos : (0 : ℤ) < c := by
      have := abs_nonneg β; have := abs_nonneg γ; omega
    nlinarith [abs_nonneg β, abs_nonneg γ]
  -- bound |β| + |γ| by fbound
  have hβb : |β| ≤ 2 * |B| * |m| + 4 * |C| * |l| := by
    rw [hβ]
    calc |2 * B * m - 4 * C * l| ≤ |2 * B * m| + |4 * C * l| := abs_sub _ _
      _ = 2 * |B| * |m| + 4 * |C| * |l| := by simp [abs_mul]
  have hγb : |γ| ≤ |m| ^ 2 + 4 * |C| * |q| := by
    rw [hγ]
    calc |m ^ 2 - 4 * C * q| ≤ |m ^ 2| + |4 * C * q| := abs_sub _ _
      _ = |m| ^ 2 + 4 * |C| * |q| := by simp [abs_mul, sq_abs]
  have hK : ((4 * |C| + 2 * |B| + 1).toNat : ℤ) = 4 * |C| + 2 * |B| + 1 := by
    rw [Int.toNat_of_nonneg]; have := abs_nonneg B; have := abs_nonneg C; omega
  unfold fbound
  rw [hK]
  have hl := abs_nonneg l; have hm := abs_nonneg m; have hq := abs_nonneg q
  have hB := abs_nonneg B; have hC := abs_nonneg C
  nlinarith [h2, hβb, hγb, mul_nonneg hB hm, mul_nonneg hC hl, mul_nonneg hC hq, mul_nonneg hl hm,
    mul_nonneg hB (mul_nonneg hl hm), mul_nonneg hC (mul_nonneg hl hm), sq_nonneg (|l| + |m|)]

/-! ### The dispatch, at data level -/

/-- 必須F step 3: the one-witness dispatch in data-carrying form. D1 and the linear leaves are
    discharged; D2 and D7 are the two leaf wrappers still owed (their families are already proved in
    `QuadraticFamilyData.lean` and `PellOrbitOfXPos.lean`). -/
theorem fiber_dichotomy_data (A B C : ℤ)
    (hD2 : disc A B C = 0 → C ≠ 0 → DichotomyOneWitnessData A B C)
    (hD7 : 0 < disc A B C → ¬ IsSquare (disc A B C) → DichotomyOneWitnessData A B C) :
    DichotomyOneWitnessData A B C := by
  rcases lt_trichotomy (disc A B C) 0 with hlt | heq | hgt
  · exact dichotomy_definite_data A B C hlt
  · by_cases hC : C = 0
    · exact dichotomyOneWitnessData_of_linear (dichotomy_degenerate_C_zero_data A B C heq hC)
    · exact hD2 heq hC
  · by_cases hC : C = 0
    · exact dichotomyOneWitnessData_of_linear (dichotomy_square_C_zero_data A B C hgt hC)
    · by_cases hs : IsSquare (disc A B C)
      · exact dichotomyOneWitnessData_of_linear (dichotomy_square_C_ne_data A B C hgt hs hC)
      · exact hD7 hgt hs

/-- The aggregated data form still implies the sealed `fiber_dichotomy`. -/
theorem fiber_dichotomy_of_data (A B C : ℤ)
    (hD2 : disc A B C = 0 → C ≠ 0 → DichotomyOneWitnessData A B C)
    (hD7 : 0 < disc A B C → ¬ IsSquare (disc A B C) → DichotomyOneWitnessData A B C) :
    Dichotomy A B C :=
  dichotomy_of_dichotomyOneWitnessData (fiber_dichotomy_data A B C hD2 hD7)

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.dichotomy_of_dichotomyOneWitnessData
#print axioms DiophCompression.SemanticQuadratic.dichotomyOneWitnessData_of_linear
#print axioms DiophCompression.SemanticQuadratic.dichotomy_definite_data
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_data
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_of_data
