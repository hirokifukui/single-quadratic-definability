/-
  N4Control.lean — s52.  R41-D3: the rank-one control with a NON-CONSTANT residual and a
  slope that depends on the residue class.

      P(a,b) = (2b - a)(2b + 3a - 1) = 0 ,   r = 0, n = m = 1.

  Total and output-unique on all of Z; f(2t) = t and f(2t+1) = -3t - 1.  The quadratic part in
  b has leading coefficient 4 > 0 (rank one, positive definite on the z-block), the completed
  square has residual R(a) = (4a-1)^2/4, which is NOT constant, and no (M >= 1, s) satisfies
  f(a+M) = f(a) + s.  So "constant residual" and "common slope" do not travel from the
  four-square family to a general semidefinite branch.

  What this is NOT: a counterexample to the normal form.  The example SATISFIES the full-residue
  form with modulus 2 (`D3_fullVectorCosetNF`).  The doubled centre is non-integral at every
  input, so the "pick an input coset and reflect" shortcut is unavailable.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.AffineNormalForm
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.GraphVocabulary

namespace DiophCompression.ResearchUpgrade.N4Control

open Matrix DiophCompression.ResearchUpgrade

/-- **R41-D3.**  `P(a,b) = (2b − a)(2b + 3a − 1)`, expanded as an `IntQuad`:
`−3a² + 4ab + 4b² + a − 2b`.  No witnesses: `r = 0`. -/
def D3 : QuadraticGraphData 1 1 0 where
  P :=
    { c := 0
      l := fun v => match v with
        | Sum.inl _ => 1
        | Sum.inr (Sum.inl _) => -2
        | Sum.inr (Sum.inr _) => 0
      Q := fun p q => match p, q with
        | Sum.inl _, Sum.inl _ => -3
        | Sum.inl _, Sum.inr (Sum.inl _) => 4
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 4
        | _, _ => 0 }

theorem D3_eval (a b : Fin 1 → ℤ) (u : Fin 0 → ℤ) :
    D3.P.eval (pt a b u) = (2 * b 0 - a 0) * (2 * b 0 + 3 * a 0 - 1) := by
  simp [D3, IntQuad.eval, dotProduct, Matrix.mulVec, pt, Fintype.sum_sum_type,
    Fin.sum_univ_one]
  ring

theorem D3_sol_iff (a b : Fin 1 → ℤ) (u : Fin 0 → ℤ) :
    D3.Sol a b u ↔ (2 * b 0 = a 0 ∨ 2 * b 0 = 1 - 3 * a 0) := by
  show D3.P.eval (pt a b u) = 0 ↔ _
  rw [D3_eval, mul_eq_zero]
  constructor
  · rintro (h | h) <;> [left; right] <;> omega
  · rintro (h | h) <;> [left; right] <;> omega

theorem D3_graph_iff (a b : Fin 1 → ℤ) :
    D3.Graph a b ↔ (2 * b 0 = a 0 ∨ 2 * b 0 = 1 - 3 * a 0) :=
  ⟨fun ⟨u, hu⟩ => (D3_sol_iff a b u).mp hu,
   fun h => ⟨fun k => k.elim0, (D3_sol_iff a b _).mpr h⟩⟩

/-- The defined function: `f(2t) = t`, `f(2t+1) = −3t − 1`. -/
def f3 : (Fin 1 → ℤ) → (Fin 1 → ℤ) :=
  fun a _ => if a 0 % 2 = 0 then a 0 / 2 else -3 * ((a 0 - 1) / 2) - 1

theorem D3_defines : D3.Defines f3 := by
  intro a b
  rw [D3_graph_iff]
  constructor
  · rintro (h | h) <;> funext j <;>
      · have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        simp only [f3]
        omega
  · intro h
    have hb : b 0 = f3 a 0 := by rw [h]
    simp only [f3] at hb
    omega

theorem D3_total : D3.Total := fun a => ⟨f3 a, (D3_defines a (f3 a)).mpr rfl⟩

theorem D3_outputUnique : D3.OutputUnique := fun a b b' hb hb' => by
  rw [(D3_defines a b).mp hb, (D3_defines a b').mp hb']

theorem f3_even (t : ℤ) : f3 (fun _ => 2 * t) 0 = t := by simp only [f3]; omega
theorem f3_odd (t : ℤ) : f3 (fun _ => 2 * t + 1) 0 = -3 * t - 1 := by simp only [f3]; omega

/-- **No uniform translation covariance.**  There is no `M ≥ 1` and `s` with
`f(a + M) = f(a) + s` for every `a` — so the modulus cannot be collapsed to `1`. -/
theorem D3_no_uniform_translation :
    ¬ ∃ (M : ℤ) (s : ℤ), 1 ≤ M ∧
      ∀ a : Fin 1 → ℤ, f3 (fun j => a j + M) 0 = f3 a 0 + s := by
  rintro ⟨M, s, hM, h⟩
  have h0 := h (fun _ => 0)
  have h1 := h (fun _ => 1)
  simp only [f3] at h0 h1
  omega


/-! ### The completed square, and why the modulus cannot be `1` -/

/-- The exact completed square over ℚ: the residual is `R(a) = (4a − 1)²/4`. -/
theorem D3_completed_square (a b : ℚ) :
    4 * (b + (2 * a - 1) / 4) ^ 2 - (4 * a - 1) ^ 2 / 4
      = -3 * a ^ 2 + 4 * a * b + a + 4 * b ^ 2 - 2 * b := by
  ring

/-- `R` is NOT constant.  So "constant residual" and "common slope" cannot be carried over
from the four-square family to a general semidefinite branch. -/
theorem D3_residual_not_constant :
    ∃ a a' : ℚ, (4 * a - 1) ^ 2 / 4 ≠ (4 * a' - 1) ^ 2 / 4 :=
  ⟨0, 1, by norm_num⟩

/-- The doubled centre is non-integral at EVERY input, so no central reflection preserves the
integer lattice — the shortcut "choose the input coset and reflect" is unavailable. -/
theorem D3_double_centre_not_integral (a : ℤ) :
    ¬ ∃ z : ℤ, (z : ℚ) = -(2 * (a : ℚ) - 1) / 2 := by
  rintro ⟨z, hz⟩
  have h2 : ((2 * z : ℤ) : ℚ) = ((1 - 2 * a : ℤ) : ℚ) := by push_cast; push_cast at hz; linarith
  have : (2 * z : ℤ) = 1 - 2 * a := by exact_mod_cast h2
  omega

/-- The slope depends on the residue class mod 2: `+1` on the even class, `−3` on the odd one.
Together with `D3_no_uniform_translation` this is the content of the control. -/
theorem D3_slope_even (t : ℤ) :
    f3 (fun _ => 2 * t + 2) 0 - f3 (fun _ => 2 * t) 0 = 1 := by
  simp only [f3]; omega

theorem D3_slope_odd (t : ℤ) :
    f3 (fun _ => 2 * t + 3) 0 - f3 (fun _ => 2 * t + 1) 0 = -3 := by
  simp only [f3]; omega

/-- **The full-residue normal form with modulus 2.**  On each coset `ρ + 2ℤ` the function is a
rational polynomial of degree ≤ 2 — affine, in fact.  The example satisfies the normal form; it
is not a counterexample to it. -/
theorem D3_fullVectorCosetNF : FullVectorCosetNF f3 := by
  refine ⟨2, by norm_num, fun ρ => ?_⟩
  by_cases hp : ρ 0 % 2 = 0
  · refine ⟨fun _ => { c := ((ρ 0 / 2 : ℤ) : ℚ), l := fun _ => 1, Q := 0 }, fun t j => ?_⟩
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    have hf : f3 (ρ + ((2 : ℕ) : ℤ) • t) 0 = ρ 0 / 2 + t 0 := by
      simp only [f3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    rw [hf]
    simp [QuadForm.eval, castQ, dotProduct, Matrix.mulVec]
  · refine ⟨fun _ => { c := ((-3 * ((ρ 0 - 1) / 2) - 1 : ℤ) : ℚ), l := fun _ => -3, Q := 0 },
      fun t j => ?_⟩
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    have hf : f3 (ρ + ((2 : ℕ) : ℤ) • t) 0
        = (-3 * ((ρ 0 - 1) / 2) - 1) + (-3) * t 0 := by
      simp only [f3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    rw [hf]
    simp [QuadForm.eval, castQ, dotProduct, Matrix.mulVec]

end DiophCompression.ResearchUpgrade.N4Control
