import DiophCompression.SemanticQuadratic.FiberDefs

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- The core algebraic identity: `4C·fq = w² − (Δ·c² + β·c + γ)`. -/
lemma key_id (A B C l m q c u : ℤ) :
    4 * C * (fq A B C l m q c u)
      = (2 * C * u + B * c + m) ^ 2
        - (disc A B C * c ^ 2 + (2 * B * m - 4 * C * l) * c + (m ^ 2 - 4 * C * q)) := by
  simp only [fq, disc]; ring

/-- Solution-preserving translation for the degenerate (`Δ = 0`) parabola: the quadratic-in-`t`
    family through a root `(c₀,u₀)` stays on the fiber for every integer `t`. -/
lemma mem_seq_a (A B C l m q c0 u0 t : ℤ) (hfq0 : fq A B C l m q c0 u0 = 0)
    (hdisc : disc A B C = 0) (hC : C ≠ 0) :
    fq A B C l m q
        (c0 + 4 * C * t * (2 * C * u0 + B * c0 + m)
          + 4 * C ^ 2 * (2 * B * m - 4 * C * l) * t ^ 2)
        (u0 + (2 * B * m - 4 * C * l) * t - 2 * B * t * (2 * C * u0 + B * c0 + m)
          - 2 * B * C * (2 * B * m - 4 * C * l) * t ^ 2) = 0 := by
  have h4 : (4 : ℤ) * C ≠ 0 := mul_ne_zero (by norm_num) hC
  have key : 4 * C * (fq A B C l m q
        (c0 + 4 * C * t * (2 * C * u0 + B * c0 + m)
          + 4 * C ^ 2 * (2 * B * m - 4 * C * l) * t ^ 2)
        (u0 + (2 * B * m - 4 * C * l) * t - 2 * B * t * (2 * C * u0 + B * c0 + m)
          - 2 * B * C * (2 * B * m - 4 * C * l) * t ^ 2)) = 0 := by
    simp only [fq, disc] at *
    linear_combination (4 * C) * hfq0
      + (c0 ^ 2 - (c0 + 4 * C * t * (2 * C * u0 + B * c0 + m)
          + 4 * C ^ 2 * (2 * B * m - 4 * C * l) * t ^ 2) ^ 2) * hdisc
  exact (mul_eq_zero.mp key).resolve_left h4

/-- Additive solution-preserving translation for the `β = 0` sub-case. -/
lemma mem_seq_b (A B C l m q c0 u0 t : ℤ) (hfq0 : fq A B C l m q c0 u0 = 0)
    (hdisc : disc A B C = 0) (hβ0 : 2 * B * m - 4 * C * l = 0) (hC : C ≠ 0) :
    fq A B C l m q (c0 + 2 * C * t) (u0 - B * t) = 0 := by
  have h4 : (4 : ℤ) * C ≠ 0 := mul_ne_zero (by norm_num) hC
  have key : 4 * C * (fq A B C l m q (c0 + 2 * C * t) (u0 - B * t)) = 0 := by
    simp only [fq, disc] at *
    linear_combination (4 * C) * hfq0
      + (c0 ^ 2 - (c0 + 2 * C * t) ^ 2) * hdisc + (-2 * C * t) * hβ0
  exact (mul_eq_zero.mp key).resolve_left h4

/-- Package: an injective `ℕ`-indexed family of fiber members forces the fiber set to be infinite. -/
lemma inf_of_family (A B C l m q : ℤ) (cf : ℕ → ℕ) (uf : ℕ → ℤ)
    (hmem : ∀ n, fq A B C l m q ((cf n : ℤ)) (uf n) = 0) (hmono : StrictMono cf) :
    (fiberSet A B C l m q).Infinite := by
  apply Set.infinite_of_injective_forall_mem hmono.injective
  intro n
  exact ⟨uf n, hmem n⟩

-- D2
theorem dichotomy_degenerate_C_ne (A B C : ℤ) (h : disc A B C = 0) (hC : C ≠ 0) :
    Dichotomy A B C := by
  refine ⟨4 * C.natAbs + 1, fun l m q => ?_⟩
  rcases lt_trichotomy (2 * B * m - 4 * C * l) 0 with hβneg | hβ0 | hβpos
  · -- β < 0 : RIGHT disjunct (bounded)
    right
    intro c hc
    obtain ⟨u, hu⟩ := hc
    -- from the identity: w² = β·c + γ
    have hsq : (2 * C * u + B * (c : ℤ) + m) ^ 2
        = (2 * B * m - 4 * C * l) * (c : ℤ) + (m ^ 2 - 4 * C * q) := by
      have key := key_id A B C l m q (c : ℤ) u
      rw [hu, h] at key
      linear_combination -key
    have hnn : 0 ≤ (2 * B * m - 4 * C * l) * (c : ℤ) + (m ^ 2 - 4 * C * q) := by
      rw [← hsq]; exact sq_nonneg _
    have hcnn : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
    have hβ1 : 2 * B * m - 4 * C * l ≤ -1 := by
      have := Int.add_one_le_iff.mpr hβneg; linarith
    have hcle : (c : ℤ) ≤ m ^ 2 - 4 * C * q := by
      nlinarith [hnn, hcnn, hβ1,
        mul_nonneg (by linarith [hβ1] : (0 : ℤ) ≤ -1 - (2 * B * m - 4 * C * l)) hcnn]
    -- bound m² − 4Cq by fbound
    have h1 : m ^ 2 ≤ (1 + |l| + |m|) ^ 2 := by
      nlinarith [sq_abs m, abs_nonneg l, abs_nonneg m, le_abs_self m]
    have h4 : -(4 * C * q) ≤ 4 * |C| * |q| := by
      have heq : |4 * C * q| = 4 * |C| * |q| := by
        rw [abs_mul, abs_mul]; norm_num
      calc -(4 * C * q) ≤ |4 * C * q| := neg_le_abs _
        _ = 4 * |C| * |q| := heq
    have h5 : (0 : ℤ) ≤ (1 + |l| + |m|) ^ 2 := sq_nonneg _
    have hCn : (0 : ℤ) ≤ |C| := abs_nonneg C
    have hqn : (0 : ℤ) ≤ |q| := abs_nonneg q
    simp only [fbound]
    have hK : ((4 * C.natAbs + 1 : ℕ) : ℤ) = 4 * |C| + 1 := by
      push_cast [Int.natCast_natAbs]; ring
    rw [hK]
    nlinarith [hcle, h1, h4, h5, hCn, hqn, mul_nonneg hCn h5, mul_nonneg hCn hqn]
  · -- β = 0 : LEFT (infinite) if nonempty, else RIGHT vacuously
    rcases Set.eq_empty_or_nonempty (fiberSet A B C l m q) with hemp | ⟨c0, hc0⟩
    · right; intro c hc; simp only [hemp, Set.mem_empty_iff_false] at hc
    · left
      obtain ⟨u0, hu0⟩ := hc0
      rcases lt_or_gt_of_ne hC with hCneg | hCpos
      · -- C < 0 : step downward in t
        have hstep : (0 : ℤ) < -(2 * C) := by linarith
        apply inf_of_family A B C l m q
          (fun n => c0 + (-(2 * C)).toNat * n)
          (fun n => u0 - B * (-(n : ℤ)))
        · intro n
          have hcast : ((c0 + (-(2 * C)).toNat * n : ℕ) : ℤ) = (c0 : ℤ) + 2 * C * (-(n : ℤ)) := by
            push_cast
            rw [Int.toNat_of_nonneg hstep.le]; ring
          rw [hcast]
          exact mem_seq_b A B C l m q (c0 : ℤ) u0 (-(n : ℤ)) hu0 h hβ0 hC
        · apply strictMono_nat_of_lt_succ
          intro n
          have hK1 : 1 ≤ (-(2 * C)).toNat := by
            rw [Nat.one_le_iff_ne_zero]; intro hz
            rw [Int.toNat_eq_zero] at hz; exact absurd hstep (not_lt_of_ge hz)
          nlinarith [hK1]
      · -- C > 0 : step upward in t
        have hstep : (0 : ℤ) < 2 * C := by linarith
        apply inf_of_family A B C l m q
          (fun n => c0 + (2 * C).toNat * n)
          (fun n => u0 - B * (n : ℤ))
        · intro n
          have hcast : ((c0 + (2 * C).toNat * n : ℕ) : ℤ) = (c0 : ℤ) + 2 * C * (n : ℤ) := by
            push_cast
            rw [Int.toNat_of_nonneg hstep.le]
          rw [hcast]
          exact mem_seq_b A B C l m q (c0 : ℤ) u0 (n : ℤ) hu0 h hβ0 hC
        · apply strictMono_nat_of_lt_succ
          intro n
          have hK1 : 1 ≤ (2 * C).toNat := by
            rw [Nat.one_le_iff_ne_zero]; intro hz
            rw [Int.toNat_eq_zero] at hz; exact absurd hstep (not_lt_of_ge hz)
          nlinarith [hK1]
  · -- β > 0 : LEFT (infinite) if nonempty, else RIGHT vacuously
    rcases Set.eq_empty_or_nonempty (fiberSet A B C l m q) with hemp | ⟨c0, hc0⟩
    · right; intro c hc; simp only [hemp, Set.mem_empty_iff_false] at hc
    · left
      obtain ⟨u0, hu0⟩ := hc0
      have hC2 : (0 : ℤ) < C ^ 2 := by
        rcases lt_or_gt_of_ne hC with hh | hh <;> nlinarith [hh]
      have hPpos : (0 : ℤ) < 4 * C ^ 2 * (2 * B * m - 4 * C * l) :=
        mul_pos (by nlinarith [hC2]) hβpos
      have hPnn : (0 : ℤ) ≤ 4 * C ^ 2 * (2 * B * m - 4 * C * l) := hPpos.le
      have hPn1 : 1 ≤ (4 * C ^ 2 * (2 * B * m - 4 * C * l)).toNat := by
        rw [Nat.one_le_iff_ne_zero]; intro hz
        rw [Int.toNat_eq_zero] at hz; exact absurd hPpos (not_lt_of_ge hz)
      rcases (lt_or_ge (4 * C * (2 * C * u0 + B * (c0 : ℤ) + m)) 0).symm with hasign | hasign
      · -- a := 4C·w₀ ≥ 0 : run t = n
        apply inf_of_family A B C l m q
          (fun n => c0 + (4 * C ^ 2 * (2 * B * m - 4 * C * l)).toNat * n ^ 2
            + (4 * C * (2 * C * u0 + B * (c0 : ℤ) + m)).toNat * n)
          (fun n => u0 + (2 * B * m - 4 * C * l) * (n : ℤ)
            - 2 * B * (n : ℤ) * (2 * C * u0 + B * (c0 : ℤ) + m)
            - 2 * B * C * (2 * B * m - 4 * C * l) * (n : ℤ) ^ 2)
        · intro n
          have hcast : ((c0 + (4 * C ^ 2 * (2 * B * m - 4 * C * l)).toNat * n ^ 2
                + (4 * C * (2 * C * u0 + B * (c0 : ℤ) + m)).toNat * n : ℕ) : ℤ)
              = (c0 : ℤ) + 4 * C * (n : ℤ) * (2 * C * u0 + B * (c0 : ℤ) + m)
                + 4 * C ^ 2 * (2 * B * m - 4 * C * l) * (n : ℤ) ^ 2 := by
            push_cast
            rw [Int.toNat_of_nonneg hPnn, Int.toNat_of_nonneg hasign]; ring
          rw [hcast]
          exact mem_seq_a A B C l m q (c0 : ℤ) u0 (n : ℤ) hu0 h hC
        · apply strictMono_nat_of_lt_succ
          intro n
          nlinarith [hPn1]
      · -- a := 4C·w₀ < 0 : run t = -n
        have hasign' : (0 : ℤ) ≤ -(4 * C * (2 * C * u0 + B * (c0 : ℤ) + m)) := by linarith
        apply inf_of_family A B C l m q
          (fun n => c0 + (4 * C ^ 2 * (2 * B * m - 4 * C * l)).toNat * n ^ 2
            + (-(4 * C * (2 * C * u0 + B * (c0 : ℤ) + m))).toNat * n)
          (fun n => u0 + (2 * B * m - 4 * C * l) * (-(n : ℤ))
            - 2 * B * (-(n : ℤ)) * (2 * C * u0 + B * (c0 : ℤ) + m)
            - 2 * B * C * (2 * B * m - 4 * C * l) * (-(n : ℤ)) ^ 2)
        · intro n
          have hcast : ((c0 + (4 * C ^ 2 * (2 * B * m - 4 * C * l)).toNat * n ^ 2
                + (-(4 * C * (2 * C * u0 + B * (c0 : ℤ) + m))).toNat * n : ℕ) : ℤ)
              = (c0 : ℤ) + 4 * C * (-(n : ℤ)) * (2 * C * u0 + B * (c0 : ℤ) + m)
                + 4 * C ^ 2 * (2 * B * m - 4 * C * l) * (-(n : ℤ)) ^ 2 := by
            push_cast
            rw [Int.toNat_of_nonneg hPnn, Int.toNat_of_nonneg hasign']; ring
          rw [hcast]
          exact mem_seq_a A B C l m q (c0 : ℤ) u0 (-(n : ℤ)) hu0 h hC
        · apply strictMono_nat_of_lt_succ
          intro n
          nlinarith [hPn1]

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_ne
