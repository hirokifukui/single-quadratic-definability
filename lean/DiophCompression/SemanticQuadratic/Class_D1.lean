import DiophCompression.SemanticQuadratic.FiberDefs
namespace DiophCompression.SemanticQuadratic
open MPUP

/-- Key identity. -/
theorem key_identity (A B C l m q c u : ℤ) :
    4 * C * fq A B C l m q c u
      = (2 * C * u + B * c + m) ^ 2 - (disc A B C * c ^ 2 + (2 * B * m - 4 * C * l) * c + (m ^ 2 - 4 * C * q)) := by
  unfold fq disc; ring

theorem dichotomy_definite (A B C : ℤ) (h : disc A B C < 0) : Dichotomy A B C := by
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

end DiophCompression.SemanticQuadratic
#print axioms DiophCompression.SemanticQuadratic.dichotomy_definite
