/-
  DiophCompression/SemanticQuadratic/DegenerateDichotomyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (leaf D2 wrapper) (s28, 2026-09-02, claude.ai direct).

  Branch D2 in data-carrying form, the last hypothesis of `fiber_dichotomy_data`. The bounded branch
  (β < 0) is the sealed argument verbatim. The two β = 0 branches are LINEAR families (the sealed proof
  uses the additive translation `mem_seq_b`), and the two β > 0 branches are the genuine QUADRATIC ones
  (`mem_seq_a`), with α = 4C²(2Bm − 4Cl), linear coefficient ±4C(2Cu₀ + Bc₀ + m), γ = c₀. Each
  `inf_of_family` call becomes the matching constructor of `OneWitnessFamilyData`; the cast lemmas the
  sealed proof already needed supply the `out` field. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.FiberDichotomyData
import DiophCompression.SemanticQuadratic.PellDichotomyData

namespace DiophCompression.SemanticQuadratic

open MPUP

theorem dichotomy_degenerate_C_ne_data (A B C : ℤ) (h : disc A B C = 0) (hC : C ≠ 0) :
    DichotomyOneWitnessData A B C := by
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
  · -- β = 0 : the family is LINEAR
    rcases Set.eq_empty_or_nonempty (fiberSet A B C l m q) with hemp | ⟨c0, hc0⟩
    · right; intro c hc; simp only [hemp, Set.mem_empty_iff_false] at hc
    · left
      obtain ⟨u0, hu0⟩ := hc0
      rcases lt_or_gt_of_ne hC with hCneg | hCpos
      · have hstep : (0 : ℤ) < -(2 * C) := by linarith
        have hK1 : 1 ≤ (-(2 * C)).toNat := by
          rw [Nat.one_le_iff_ne_zero]; intro hz
          rw [Int.toNat_eq_zero] at hz; exact absurd hstep (not_lt_of_ge hz)
        refine ⟨OneWitnessFamilyData.linear c0 ((-(2 * C)).toNat) hK1
          (fun n => u0 - B * (-(n : ℤ))) (fun n => ?_)⟩
        have hcast : ((c0 + (-(2 * C)).toNat * n : ℕ) : ℤ) = (c0 : ℤ) + 2 * C * (-(n : ℤ)) := by
          push_cast
          rw [Int.toNat_of_nonneg hstep.le]; ring
        rw [hcast]
        exact mem_seq_b A B C l m q (c0 : ℤ) u0 (-(n : ℤ)) hu0 h hβ0 hC
      · have hstep : (0 : ℤ) < 2 * C := by linarith
        have hK1 : 1 ≤ (2 * C).toNat := by
          rw [Nat.one_le_iff_ne_zero]; intro hz
          rw [Int.toNat_eq_zero] at hz; exact absurd hstep (not_lt_of_ge hz)
        refine ⟨OneWitnessFamilyData.linear c0 ((2 * C).toNat) hK1
          (fun n => u0 - B * (n : ℤ)) (fun n => ?_)⟩
        have hcast : ((c0 + (2 * C).toNat * n : ℕ) : ℤ) = (c0 : ℤ) + 2 * C * (n : ℤ) := by
          push_cast
          rw [Int.toNat_of_nonneg hstep.le]
        rw [hcast]
        exact mem_seq_b A B C l m q (c0 : ℤ) u0 (n : ℤ) hu0 h hβ0 hC
  · -- β > 0 : the family is QUADRATIC
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
      · refine ⟨OneWitnessFamilyData.quadratic (4 * C ^ 2 * (2 * B * m - 4 * C * l))
          (4 * C * (2 * C * u0 + B * (c0 : ℤ) + m)) (c0 : ℤ) hPpos.ne'
          (fun n => c0 + (4 * C ^ 2 * (2 * B * m - 4 * C * l)).toNat * n ^ 2
            + (4 * C * (2 * C * u0 + B * (c0 : ℤ) + m)).toNat * n)
          (fun n => u0 + (2 * B * m - 4 * C * l) * (n : ℤ)
            - 2 * B * (n : ℤ) * (2 * C * u0 + B * (c0 : ℤ) + m)
            - 2 * B * C * (2 * B * m - 4 * C * l) * (n : ℤ) ^ 2) ?_ ?_ ?_⟩
        · intro n
          push_cast
          rw [Int.toNat_of_nonneg hPnn, Int.toNat_of_nonneg hasign]; ring
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
      · have hasign' : (0 : ℤ) ≤ -(4 * C * (2 * C * u0 + B * (c0 : ℤ) + m)) := by linarith
        refine ⟨OneWitnessFamilyData.quadratic (4 * C ^ 2 * (2 * B * m - 4 * C * l))
          (-(4 * C * (2 * C * u0 + B * (c0 : ℤ) + m))) (c0 : ℤ) hPpos.ne'
          (fun n => c0 + (4 * C ^ 2 * (2 * B * m - 4 * C * l)).toNat * n ^ 2
            + (-(4 * C * (2 * C * u0 + B * (c0 : ℤ) + m))).toNat * n)
          (fun n => u0 + (2 * B * m - 4 * C * l) * (-(n : ℤ))
            - 2 * B * (-(n : ℤ)) * (2 * C * u0 + B * (c0 : ℤ) + m)
            - 2 * B * C * (2 * B * m - 4 * C * l) * (-(n : ℤ)) ^ 2) ?_ ?_ ?_⟩
        · intro n
          push_cast
          rw [Int.toNat_of_nonneg hPnn, Int.toNat_of_nonneg hasign']; ring
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

/-- 必須F step 3, MILESTONE: with D2 (here) and D7 (`dichotomy_pell_data`) both converted, the whole
    one-witness layer is UNCONDITIONAL in data-carrying form — every fibre of the one-witness normal form
    is either bounded by the sealed bound, or carries an explicit structured family. -/
theorem fiber_dichotomy_data_full (A B C : ℤ) : DichotomyOneWitnessData A B C :=
  fiber_dichotomy_data A B C (fun heq hCne => dichotomy_degenerate_C_ne_data A B C heq hCne)
    (fun hgt hns => dichotomy_pell_data A B C hgt hns)

/-- And it still implies the sealed `fiber_dichotomy`. -/
theorem fiber_dichotomy_of_data_full (A B C : ℤ) : Dichotomy A B C :=
  dichotomy_of_dichotomyOneWitnessData (fiber_dichotomy_data_full A B C)

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.dichotomy_degenerate_C_ne_data
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_data_full
#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy_of_data_full
