import DiophCompression.SemanticQuadratic.FiberDefs
namespace DiophCompression.SemanticQuadratic

/-- Powers of a Pell unit (p + q√D): componentwise recursion. -/
def pellPow (D p q : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => (p * (pellPow D p q k).1 + D * q * (pellPow D p q k).2,
              p * (pellPow D p q k).2 + q * (pellPow D p q k).1)

theorem pellPow_norm (D p q : ℤ) (h : p ^ 2 - D * q ^ 2 = 1) (k : ℕ) :
    (pellPow D p q k).1 ^ 2 - D * (pellPow D p q k).2 ^ 2 = 1 := by
  induction k with
  | zero => simp [pellPow]
  | succ k ih => simp only [pellPow]; linear_combination ((pellPow D p q k).1 ^ 2 - D * (pellPow D p q k).2 ^ 2) * h + ih

theorem pellPow_add (D p q : ℤ) (i T : ℕ) :
    (pellPow D p q (i + T)).1 = (pellPow D p q i).1 * (pellPow D p q T).1 + D * (pellPow D p q i).2 * (pellPow D p q T).2 ∧
    (pellPow D p q (i + T)).2 = (pellPow D p q i).1 * (pellPow D p q T).2 + (pellPow D p q i).2 * (pellPow D p q T).1 := by
  induction T with
  | zero => simp [pellPow]
  | succ T ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [show i + (T + 1) = (i + T) + 1 by omega]
    simp only [pellPow]
    rw [h1, h2]
    constructor <;> ring

theorem pellPow_pos (D p q : ℤ) (hD : 0 < D) (hp : 1 ≤ p) (hq : 1 ≤ q) (k : ℕ) :
    1 ≤ (pellPow D p q k).1 ∧ 0 ≤ (pellPow D p q k).2 ∧ (k ≠ 0 → 1 ≤ (pellPow D p q k).2) := by
  induction k with
  | zero => simp [pellPow]
  | succ k ih =>
    obtain ⟨h1, h2, _⟩ := ih
    simp only [pellPow]
    refine ⟨?_, ?_, fun _ => ?_⟩
    · nlinarith [mul_nonneg (le_of_lt hD) (mul_nonneg (by linarith : (0:ℤ) ≤ q) h2)]
    · nlinarith
    · nlinarith

/-- Periodicity of the unit powers modulo M: some positive power is ≡ (1, 0). -/
theorem pellPow_periodic (D p q : ℤ) (h : p ^ 2 - D * q ^ 2 = 1) (M : ℕ) (hM : 0 < M) :
    ∃ T : ℕ, 0 < T ∧ (M : ℤ) ∣ (pellPow D p q T).1 - 1 ∧ (M : ℤ) ∣ (pellPow D p q T).2 := by
  haveI : NeZero M := ⟨by omega⟩
  let f : ℕ → ZMod M × ZMod M := fun k => (((pellPow D p q k).1 : ZMod M), ((pellPow D p q k).2 : ZMod M))
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  -- order i < j without loss of generality
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hf.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  refine ⟨j - i, by omega, ?_, ?_⟩
  all_goals
    have hfp : ((pellPow D p q i).1 : ZMod M) = (pellPow D p q j).1 := congrArg Prod.fst hf
    have hfq : ((pellPow D p q i).2 : ZMod M) = (pellPow D p q j).2 := congrArg Prod.snd hf
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hfp hfq
    obtain ⟨h1, h2⟩ := pellPow_add D p q i (j - i)
    rw [show i + (j - i) = j by omega] at h1 h2
    have hni := pellPow_norm D p q h i
    obtain ⟨a, ha⟩ := hfp
    obtain ⟨b, hb⟩ := hfq
  · -- p_T - 1 = p_i (p_j - p_i) - D q_i (q_j - q_i)
    refine ⟨(pellPow D p q i).1 * a - D * (pellPow D p q i).2 * b, ?_⟩
    linear_combination (pellPow D p q i).1 * ha - D * (pellPow D p q i).2 * hb
      - (pellPow D p q i).1 * h1 + D * (pellPow D p q i).2 * h2 + (1 - (pellPow D p q (j - i)).1) * hni
  · -- q_T = p_i (q_j - q_i) - q_i (p_j - p_i)
    refine ⟨(pellPow D p q i).1 * b - (pellPow D p q i).2 * a, ?_⟩
    linear_combination (pellPow D p q i).1 * hb - (pellPow D p q i).2 * ha
      - (pellPow D p q i).1 * h2 + (pellPow D p q i).2 * h1 - (pellPow D p q (j - i)).2 * hni

end DiophCompression.SemanticQuadratic
#print axioms DiophCompression.SemanticQuadratic.pellPow_periodic
#print axioms DiophCompression.SemanticQuadratic.pellPow_pos
