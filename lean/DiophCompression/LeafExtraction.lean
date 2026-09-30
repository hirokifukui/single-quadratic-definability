/-
  DiophCompression/LeafExtraction.lean — APAL Structural Theory Gate 5, 必須D (s28, 2026-09-02, claude.ai direct).

  Leaf-level extraction: the packagers that turn the DATA each branch of the projection dichotomy actually
  produces into a structured certificate of the right kind (GATE4_F_BRANCH_INVENTORY, three families).
    * linear family  (B0, B1b′-D3/D4/D6)        → PolynomialProgressionRealization, deg 1
    * quadratic family (A2, B1b′-D2)            → PolynomialProgressionRealization, deg 2
    * periodic family (A3, B3, B1b)             → polynomialProgression_of_periodic_shift (s27, already kernel)
    * Pell unit orbit (A1, B1b′-D7)             → PellUnitOrbitRealization
    * moving-modulus step orbit (B1c, B2, B4)   → MovingModulusStepOrbit (s27/s28, already kernel)
  Each packager takes exactly the data the branch supplies and PROVES the output injectivity from the growth
  of the family — no `Classical.choice` fallback, no generic tag. No sorry; std-3.
-/
import DiophCompression.OutputNegation

namespace DiophCompression

open MvPolynomial MPUP Matrix

variable {n r : ℕ}

/-! ### Growth ⇒ injectivity beyond a threshold -/

/-- If an integer family strictly increases from `t₀` on, distinct indices `≥ t₀` give distinct values. -/
theorem injective_of_lt_succ_from (f : ℕ → ℤ) (t₀ : ℕ) (h : ∀ t, t₀ ≤ t → f t < f (t + 1)) :
    ∀ t t' : ℕ, t₀ ≤ t → t₀ ≤ t' → f t = f t' → t = t' := by
  have hg : StrictMono (fun k : ℕ => f (t₀ + k)) :=
    strictMono_nat_of_lt_succ (fun k => h (t₀ + k) (Nat.le_add_right _ _))
  intro t t' ht ht' heq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le ht'
  have := hg.injective (a₁ := d) (a₂ := d') heq
  omega

/-! ### The linear family (branches B0, D3, D4, D6) -/

/-- Output polynomial of a linear family `c₀ + s·t`. -/
noncomputable def linearFamilyPoly (c₀ s : ℤ) : Polynomial ℤ :=
  Polynomial.C s * Polynomial.X + Polynomial.C c₀

theorem linearFamilyPoly_eval (c₀ s : ℤ) (t : ℤ) : (linearFamilyPoly c₀ s).eval t = c₀ + s * t := by
  simp [linearFamilyPoly]; ring

/-- Packager for a linear family: base point `c₀`, nonzero step `s`, explicit witnesses. -/
noncomputable def extract_linear_family (P : Poly (n + 1) r) (a : Fin n → ℤ) (c₀ s : ℤ) (hs : s ≠ 0)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ t : ℕ, evalAtZZ P (Fin.snoc a (c₀ + s * t)) (w t) = 0) :
    PolynomialProgressionRealization P a where
  q := linearFamilyPoly c₀ s
  deg_le_two := by rw [linearFamilyPoly, Polynomial.natDegree_linear hs]; norm_num
  nonconst := by rw [linearFamilyPoly, Polynomial.natDegree_linear hs]; norm_num
  t₀ := 0
  witness := w
  mem := fun t _ => by rw [linearFamilyPoly_eval]; exact hmem t
  injective := fun t t' _ _ h => by
    rw [linearFamilyPoly_eval, linearFamilyPoly_eval] at h
    have : (t : ℤ) = (t' : ℤ) := by
      have := mul_left_cancel₀ hs (by linarith : s * (t : ℤ) = s * (t' : ℤ))
      exact this
    exact_mod_cast this

theorem extract_linear_family_q (P : Poly (n + 1) r) (a : Fin n → ℤ) (c₀ s : ℤ) (hs : s ≠ 0)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ t : ℕ, evalAtZZ P (Fin.snoc a (c₀ + s * t)) (w t) = 0) :
    (extract_linear_family P a c₀ s hs w hmem).q = linearFamilyPoly c₀ s ∧
      (extract_linear_family P a c₀ s hs w hmem).t₀ = 0 := ⟨rfl, rfl⟩

/-- Branch B0 (rank-zero quotient leaf): the remainder-zero family is a degree-1 progression. -/
noncomputable def extract_B0_polynomial (P : Poly (n + 1) r) (a : Fin n → ℤ) (c₀ s : ℤ) (hs : s ≠ 0)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ t : ℕ, evalAtZZ P (Fin.snoc a (c₀ + s * t)) (w t) = 0) :
    StructuredCertificate P a :=
  .polynomialProgression (extract_linear_family P a c₀ s hs w hmem)

/-- Branches D3, D4 (disc = 0 with C = 0; disc a positive square with C ≠ 0): family `c₀ + s·t`. -/
noncomputable def extract_B1_degenerate (P : Poly (n + 1) r) (a : Fin n → ℤ) (c₀ s : ℤ) (hs : s ≠ 0)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ t : ℕ, evalAtZZ P (Fin.snoc a (c₀ + s * t)) (w t) = 0) :
    StructuredCertificate P a :=
  .polynomialProgression (extract_linear_family P a c₀ s hs w hmem)

/-- Branch D6 (disc a positive square, C = 0): the step is `B²` with `B ≠ 0`. -/
noncomputable def extract_D6_linear (P : Poly (n + 1) r) (a : Fin n → ℤ) (c₀ B : ℤ) (hB : B ≠ 0)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ t : ℕ, evalAtZZ P (Fin.snoc a (c₀ + B ^ 2 * t)) (w t) = 0) :
    StructuredCertificate P a :=
  .polynomialProgression (extract_linear_family P a c₀ (B ^ 2) (pow_ne_zero 2 hB) w hmem)

/-! ### The quadratic family (branches A2, B1b′-D2) -/

/-- Output polynomial of a quadratic family `α t² + β t + γ`. -/
noncomputable def quadraticFamilyPoly (α β γ : ℤ) : Polynomial ℤ :=
  Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ

theorem quadraticFamilyPoly_eval (α β γ t : ℤ) :
    (quadraticFamilyPoly α β γ).eval t = α * t ^ 2 + β * t + γ := by
  simp [quadraticFamilyPoly]

/-- Packager for a quadratic family: leading coefficient nonzero, explicit witnesses, and strict growth
    from `t₀` on (which the branch supplies; injectivity is then PROVED, not assumed). -/
noncomputable def extract_quadratic_family (P : Poly (n + 1) r) (a : Fin n → ℤ) (α β γ : ℤ)
    (hα : α ≠ 0) (t₀ : ℕ) (w : ℕ → Fin r → ℤ)
    (hmem : ∀ t : ℕ, t₀ ≤ t → evalAtZZ P (Fin.snoc a (α * (t : ℤ) ^ 2 + β * t + γ)) (w t) = 0)
    (hgrow : ∀ t : ℕ, t₀ ≤ t →
      α * (t : ℤ) ^ 2 + β * t + γ < α * ((t : ℤ) + 1) ^ 2 + β * ((t : ℤ) + 1) + γ) :
    PolynomialProgressionRealization P a where
  q := quadraticFamilyPoly α β γ
  deg_le_two := by rw [quadraticFamilyPoly, Polynomial.natDegree_quadratic hα]
  nonconst := by rw [quadraticFamilyPoly, Polynomial.natDegree_quadratic hα]; norm_num
  t₀ := t₀
  witness := w
  mem := fun t ht => by rw [quadraticFamilyPoly_eval]; exact hmem t ht
  injective := by
    refine injective_of_lt_succ_from (fun t => (quadraticFamilyPoly α β γ).eval (t : ℤ)) t₀ ?_
    intro t ht
    simp only [quadraticFamilyPoly_eval, Nat.cast_add, Nat.cast_one]
    exact hgrow t ht

/-- Branch A2 (α = 0, β ≠ 0 in the full-rank block): the output is a degree-2 progression. -/
noncomputable def extract_A2_polynomial (P : Poly (n + 1) r) (a : Fin n → ℤ) (α β γ : ℤ)
    (hα : α ≠ 0) (t₀ : ℕ) (w : ℕ → Fin r → ℤ)
    (hmem : ∀ t : ℕ, t₀ ≤ t → evalAtZZ P (Fin.snoc a (α * (t : ℤ) ^ 2 + β * t + γ)) (w t) = 0)
    (hgrow : ∀ t : ℕ, t₀ ≤ t →
      α * (t : ℤ) ^ 2 + β * t + γ < α * ((t : ℤ) + 1) ^ 2 + β * ((t : ℤ) + 1) + γ) :
    StructuredCertificate P a :=
  .polynomialProgression (extract_quadratic_family P a α β γ hα t₀ w hmem hgrow)

/-- Branch B1b′-D2 (disc = 0, C ≠ 0): same shape as A2 through the one-witness normal form. -/
noncomputable def extract_D2_polynomial (P : Poly (n + 1) r) (a : Fin n → ℤ) (α β γ : ℤ)
    (hα : α ≠ 0) (t₀ : ℕ) (w : ℕ → Fin r → ℤ)
    (hmem : ∀ t : ℕ, t₀ ≤ t → evalAtZZ P (Fin.snoc a (α * (t : ℤ) ^ 2 + β * t + γ)) (w t) = 0)
    (hgrow : ∀ t : ℕ, t₀ ≤ t →
      α * (t : ℤ) ^ 2 + β * t + γ < α * ((t : ℤ) + 1) ^ 2 + β * ((t : ℤ) + 1) + γ) :
    StructuredCertificate P a :=
  .polynomialProgression (extract_quadratic_family P a α β γ hα t₀ w hmem hgrow)

/-! ### The periodic family (branches A3, B3, B1b) -/

/-- Branch A3 / B3 / B1b: a witnessed period `T > 0` gives a degree-1 progression certificate. This is the
    s27 lemma; the branch-named forms below fix which period each leaf supplies. -/
theorem extract_periodic (P : Poly (n + 1) r) (a : Fin n → ℤ) (T : ℕ) (hT : 0 < T) (c₀ : ℤ)
    (u₀ : Fin r → ℤ) (h₀ : evalAtZZ P (Fin.snoc a c₀) u₀ = 0)
    (shift : ℤ → (Fin r → ℤ) → (Fin r → ℤ))
    (hshift : ∀ (c : ℤ) (u : Fin r → ℤ), evalAtZZ P (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (c + T)) (shift c u) = 0) :
    ∃ cert : PolynomialProgressionRealization P a,
      cert.q = Polynomial.C c₀ + Polynomial.C (T : ℤ) * Polynomial.X ∧ cert.t₀ = 0 :=
  polynomialProgression_of_periodic_shift P a T hT c₀ u₀ h₀ shift hshift

/-- Branch A3 (α = β = 0 in the full-rank block): the period is `|N|` for the nonzero `N` of that branch. -/
theorem extract_A3_periodic (P : Poly (n + 1) r) (a : Fin n → ℤ) (N : ℤ) (hN : N ≠ 0) (c₀ : ℤ)
    (u₀ : Fin r → ℤ) (h₀ : evalAtZZ P (Fin.snoc a c₀) u₀ = 0)
    (shift : ℤ → (Fin r → ℤ) → (Fin r → ℤ))
    (hshift : ∀ (c : ℤ) (u : Fin r → ℤ), evalAtZZ P (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (c + (N.natAbs : ℤ))) (shift c u) = 0) :
    ∃ cert : PolynomialProgressionRealization P a,
      cert.q = Polynomial.C c₀ + Polynomial.C ((N.natAbs : ℤ)) * Polynomial.X ∧ cert.t₀ = 0 :=
  extract_periodic P a N.natAbs (Int.natAbs_pos.mpr hN) c₀ u₀ h₀ shift hshift

/-- Branch B3 (fixed modulus in the singular block) and branch B1b (uncoupled, `m₂ ≠ 0`): the period is the
    modulus of that branch. -/
theorem extract_B1_fixed_periodic (P : Poly (n + 1) r) (a : Fin n → ℤ) (M : ℤ) (hM : M ≠ 0) (c₀ : ℤ)
    (u₀ : Fin r → ℤ) (h₀ : evalAtZZ P (Fin.snoc a c₀) u₀ = 0)
    (shift : ℤ → (Fin r → ℤ) → (Fin r → ℤ))
    (hshift : ∀ (c : ℤ) (u : Fin r → ℤ), evalAtZZ P (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (c + (M.natAbs : ℤ))) (shift c u) = 0) :
    ∃ cert : PolynomialProgressionRealization P a,
      cert.q = Polynomial.C c₀ + Polynomial.C ((M.natAbs : ℤ)) * Polynomial.X ∧ cert.t₀ = 0 :=
  extract_periodic P a M.natAbs (Int.natAbs_pos.mpr hM) c₀ u₀ h₀ shift hshift

/-! ### The Pell unit orbit (branches A1, B1b′-D7) -/

/-- Positivity is preserved along the orbit of a fundamental unit with `x₀ > 1`, `y₀ > 0`. -/
theorem pellFamily_coords_pos (D x₀ y₀ : ℤ) (hD : 0 < D) (hx : 1 < x₀) (hy : 0 < y₀)
    (X Y : ℕ → ℤ) (hX : ∀ k, X (k + 1) = x₀ * X k + D * y₀ * Y k)
    (hY : ∀ k, Y (k + 1) = y₀ * X k + x₀ * Y k) (hX0 : 0 < X 0) (hY0 : 0 ≤ Y 0) :
    ∀ k, 0 < X k ∧ 0 ≤ Y k := by
  intro k
  induction k with
  | zero => exact ⟨hX0, hY0⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · rw [hX]; positivity
    · rw [hY]; positivity

/-- The orbit coordinates strictly increase. -/
theorem pellFamily_X_strictMono (D x₀ y₀ : ℤ) (hD : 0 < D) (hx : 1 < x₀) (hy : 0 < y₀)
    (X Y : ℕ → ℤ) (hX : ∀ k, X (k + 1) = x₀ * X k + D * y₀ * Y k)
    (hY : ∀ k, Y (k + 1) = y₀ * X k + x₀ * Y k) (hX0 : 0 < X 0) (hY0 : 0 ≤ Y 0) :
    StrictMono X := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  obtain ⟨h1, h2⟩ := pellFamily_coords_pos D x₀ y₀ hD hx hy X Y hX hY hX0 hY0 k
  have hDy : 0 ≤ D * y₀ * Y k := by positivity
  have : X k < x₀ * X k := by nlinarith
  rw [hX]; linarith

/-- Packager for the Pell kind: unit data, orbit recurrence, affine output with a denominator, witnesses,
    and strict growth of the output (from which injectivity is PROVED). -/
noncomputable def extract_pell_orbit (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (D x₀ y₀ N₀ : ℤ) (hD : 0 < D) (hDns : ¬ IsSquare D) (hunit : x₀ ^ 2 - D * y₀ ^ 2 = 1)
    (hy₀ : y₀ ≠ 0) (X Y : ℕ → ℤ) (hbase : X 0 ^ 2 - D * Y 0 ^ 2 = N₀)
    (hX : ∀ k, X (k + 1) = x₀ * X k + D * y₀ * Y k)
    (hY : ∀ k, Y (k + 1) = y₀ * X k + x₀ * Y k)
    (pc px py denom : ℤ) (hden : denom ≠ 0) (out : ℕ → ℤ)
    (hout : ∀ k, denom * out k = pc + px * X k + py * Y k)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ k, evalAtZZ P (Fin.snoc a (out k)) (w k) = 0)
    (hmono : StrictMono out) : PellUnitOrbitRealization P a where
  D := D
  D_pos := hD
  D_nonsquare := hDns
  x₀ := x₀
  y₀ := y₀
  unit := hunit
  y₀_ne := hy₀
  N₀ := N₀
  X := X
  Y := Y
  base_norm := hbase
  succ_X := hX
  succ_Y := hY
  pc := pc
  px := px
  py := py
  denom := denom
  denom_ne := hden
  output := out
  output_eq := hout
  witness := w
  mem := hmem
  injective := hmono.injective

/-- Branch A1 (full-rank block, signed non-square direction) — the Pell packaging. -/
noncomputable def extract_A1_pell (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (D x₀ y₀ N₀ : ℤ) (hD : 0 < D) (hDns : ¬ IsSquare D) (hunit : x₀ ^ 2 - D * y₀ ^ 2 = 1)
    (hy₀ : y₀ ≠ 0) (X Y : ℕ → ℤ) (hbase : X 0 ^ 2 - D * Y 0 ^ 2 = N₀)
    (hX : ∀ k, X (k + 1) = x₀ * X k + D * y₀ * Y k)
    (hY : ∀ k, Y (k + 1) = y₀ * X k + x₀ * Y k)
    (pc px py denom : ℤ) (hden : denom ≠ 0) (out : ℕ → ℤ)
    (hout : ∀ k, denom * out k = pc + px * X k + py * Y k)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ k, evalAtZZ P (Fin.snoc a (out k)) (w k) = 0)
    (hmono : StrictMono out) : StructuredCertificate P a :=
  .pellUnitOrbit (extract_pell_orbit P a D x₀ y₀ N₀ hD hDns hunit hy₀ X Y hbase hX hY
    pc px py denom hden out hout w hmem hmono)

/-- Branch B1b′-D7 (one-witness leaf, disc a positive non-square) — same packaging, `D = disc`. -/
noncomputable def extract_D7_pell (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (D x₀ y₀ N₀ : ℤ) (hD : 0 < D) (hDns : ¬ IsSquare D) (hunit : x₀ ^ 2 - D * y₀ ^ 2 = 1)
    (hy₀ : y₀ ≠ 0) (X Y : ℕ → ℤ) (hbase : X 0 ^ 2 - D * Y 0 ^ 2 = N₀)
    (hX : ∀ k, X (k + 1) = x₀ * X k + D * y₀ * Y k)
    (hY : ∀ k, Y (k + 1) = y₀ * X k + x₀ * Y k)
    (pc px py denom : ℤ) (hden : denom ≠ 0) (out : ℕ → ℤ)
    (hout : ∀ k, denom * out k = pc + px * X k + py * Y k)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ k, evalAtZZ P (Fin.snoc a (out k)) (w k) = 0)
    (hmono : StrictMono out) : StructuredCertificate P a :=
  .pellUnitOrbit (extract_pell_orbit P a D x₀ y₀ N₀ hD hDns hunit hy₀ X Y hbase hX hY
    pc px py denom hden out hout w hmem hmono)

/-! ### Kinds emitted, as kernel facts (necessary for the branch table to be checkable) -/

theorem extract_B0_polynomial_kind (P : Poly (n + 1) r) (a : Fin n → ℤ) (c₀ s : ℤ) (hs : s ≠ 0)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ t : ℕ, evalAtZZ P (Fin.snoc a (c₀ + s * t)) (w t) = 0) :
    (extract_B0_polynomial P a c₀ s hs w hmem).kind = StructuredKind.polynomialProgression := rfl

theorem extract_A2_polynomial_kind (P : Poly (n + 1) r) (a : Fin n → ℤ) (α β γ : ℤ)
    (hα : α ≠ 0) (t₀ : ℕ) (w : ℕ → Fin r → ℤ)
    (hmem : ∀ t : ℕ, t₀ ≤ t → evalAtZZ P (Fin.snoc a (α * (t : ℤ) ^ 2 + β * t + γ)) (w t) = 0)
    (hgrow : ∀ t : ℕ, t₀ ≤ t →
      α * (t : ℤ) ^ 2 + β * t + γ < α * ((t : ℤ) + 1) ^ 2 + β * ((t : ℤ) + 1) + γ) :
    (extract_A2_polynomial P a α β γ hα t₀ w hmem hgrow).kind
      = StructuredKind.polynomialProgression := rfl

theorem extract_A1_pell_kind (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (D x₀ y₀ N₀ : ℤ) (hD : 0 < D) (hDns : ¬ IsSquare D) (hunit : x₀ ^ 2 - D * y₀ ^ 2 = 1)
    (hy₀ : y₀ ≠ 0) (X Y : ℕ → ℤ) (hbase : X 0 ^ 2 - D * Y 0 ^ 2 = N₀)
    (hX : ∀ k, X (k + 1) = x₀ * X k + D * y₀ * Y k)
    (hY : ∀ k, Y (k + 1) = y₀ * X k + x₀ * Y k)
    (pc px py denom : ℤ) (hden : denom ≠ 0) (out : ℕ → ℤ)
    (hout : ∀ k, denom * out k = pc + px * X k + py * Y k)
    (w : ℕ → Fin r → ℤ) (hmem : ∀ k, evalAtZZ P (Fin.snoc a (out k)) (w k) = 0)
    (hmono : StrictMono out) :
    (extract_A1_pell P a D x₀ y₀ N₀ hD hDns hunit hy₀ X Y hbase hX hY pc px py denom hden out hout
      w hmem hmono).kind = StructuredKind.pellUnitOrbit := rfl

end DiophCompression

#print axioms DiophCompression.injective_of_lt_succ_from
#print axioms DiophCompression.linearFamilyPoly_eval
#print axioms DiophCompression.extract_linear_family_q
#print axioms DiophCompression.quadraticFamilyPoly_eval
#print axioms DiophCompression.extract_periodic
#print axioms DiophCompression.extract_A3_periodic
#print axioms DiophCompression.extract_B1_fixed_periodic
#print axioms DiophCompression.pellFamily_coords_pos
#print axioms DiophCompression.pellFamily_X_strictMono
#print axioms DiophCompression.extract_B0_polynomial_kind
#print axioms DiophCompression.extract_A2_polynomial_kind
#print axioms DiophCompression.extract_A1_pell_kind
