/-
  BoxCriterion.lean — s52.  R41-D2 (partial): total and output-unique for the four-square family
  is equivalent, INPUT BY INPUT, to a box condition.  This is a pointwise equivalence: the right-hand
  side still quantifies over every integer input.  It is not a finite decision criterion.

  The four witnesses are a slack variable and nothing else, so `Graph a b` holds iff
  `sum_j (k b_j - lin_j(a))^2 <= R a`.  Hence total and output-unique together say: at every
  input the box holds exactly one lattice point.  Each coordinate is pinned by
  `box_coord_bound`, so the box is finite; `R a < 0` empties it; and `graph_shift` shows that
  two inputs whose linear parts differ by a multiple of k, with equal residual, have boxes that
  are translates.  A criterion ranging over the reachable residues c + B rho only is NOT proved
  here: it needs the constancy of the residual, which this file does not use.  `defines_of_box_unique` reads the defined function off the singleton.

  Not claimed: a decision procedure for general SE2, any complexity bound, or a generalisation
  to arbitrary universal quadratic forms.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.FourSquareSlack

namespace DiophCompression.ResearchUpgrade.FourSquareSlack
namespace Family

variable {n m : ℕ} (F : Family n m)

/-- **R41-D2, the reduction.**  The four witnesses are exactly a slack variable: a point is on
the graph iff the finite box inequality holds.  `exists_four_squares` is what makes `≤` and
`∃ u` the same thing. -/
theorem graph_iff_box (a : Fin n → ℤ) (b : Fin m → ℤ) :
    F.Graph a b ↔ (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a := by
  constructor
  · rintro ⟨u, hu⟩
    have hu' : (∑ j, (F.k * b j - F.lin a j) ^ 2) + ∑ i, u i ^ 2 = F.R a := hu
    have : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · intro h
    obtain ⟨u, hu⟩ := exists_four_squares (N := F.R a - ∑ j, (F.k * b j - F.lin a j) ^ 2)
      (by linarith)
    exact ⟨u, by show _ + _ = _; linarith⟩

/-- `R a < 0` makes the box empty, so the family is not total there. -/
theorem not_graph_of_neg {a : Fin n → ℤ} (h : F.R a < 0) (b : Fin m → ℤ) : ¬ F.Graph a b := by
  rw [graph_iff_box]
  have : 0 ≤ ∑ j, (F.k * b j - F.lin a j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  omega

/-- **The pointwise box condition.**  Total and output-unique is exactly: at every input the box
contains exactly one lattice point.  The quantifier over all inputs remains. -/
theorem total_and_outputUnique_iff :
    (F.Total ∧ F.OutputUnique)
      ↔ ∀ a : Fin n → ℤ, ∃! b : Fin m → ℤ, (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a := by
  constructor
  · rintro ⟨hT, hU⟩ a
    obtain ⟨b, hb⟩ := hT a
    refine ⟨b, (F.graph_iff_box a b).mp hb, fun b' hb' => ?_⟩
    exact hU a b' b ((F.graph_iff_box a b').mpr hb') hb
  · intro h
    refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
    · obtain ⟨b, hb, -⟩ := h a
      exact ⟨b, (F.graph_iff_box a b).mpr hb⟩
    · obtain ⟨b₀, -, huniq⟩ := h a
      rw [huniq b ((F.graph_iff_box a b).mp hb), huniq b' ((F.graph_iff_box a b').mp hb')]

/-- Each coordinate of a box point is pinned: the box is finite, with an explicit bound. -/
theorem box_coord_bound {a : Fin n → ℤ} {b : Fin m → ℤ}
    (h : (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a) (j : Fin m) :
    (F.k * b j - F.lin a j) ^ 2 ≤ F.R a :=
  le_trans (Finset.single_le_sum (f := fun j => (F.k * b j - F.lin a j) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)) h

/-- **Only the residue matters.**  If two inputs have linear parts differing by a multiple of
`k` and the same residual, their boxes are translates of each other.  This is why the criterion
could range over reachable residues `c + Bρ` once the residual is known to be constant; that step
is not taken here. -/
theorem graph_shift {a a' : Fin n → ℤ} (d : Fin m → ℤ)
    (hlin : ∀ j, F.lin a' j = F.lin a j + F.k * d j) (hR : F.R a' = F.R a) (b : Fin m → ℤ) :
    F.Graph a' (b + d) ↔ F.Graph a b := by
  rw [graph_iff_box, graph_iff_box, hR]
  have : ∀ j, F.k * (b + d) j - F.lin a' j = F.k * b j - F.lin a j := by
    intro j; rw [hlin j]; simp [Pi.add_apply]; ring
  rw [Finset.sum_congr rfl fun j _ => by rw [this j]]

/-- From the singleton, the defined function is recovered on the nose. -/
theorem defines_of_box_unique
    (h : ∀ a : Fin n → ℤ, ∃! b : Fin m → ℤ, (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ F.R a)
    (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : ∀ a, (∑ j, (F.k * f a j - F.lin a j) ^ 2) ≤ F.R a) :
    ∀ a b, F.Graph a b ↔ b = f a := by
  intro a b
  obtain ⟨b₀, hb₀, huniq⟩ := h a
  rw [graph_iff_box]
  constructor
  · intro hb; rw [huniq b hb, ← huniq (f a) (hf a)]
  · rintro rfl; exact hf a

end Family

/-- The `k = 3` example through the criterion: `Ex` has `c = 0`, so the box is `(3b − a)² ≤ 1`. -/
theorem Ex_box (a b : Fin 1 → ℤ) :
    Ex.Graph a b ↔ (∑ j, (Ex.k * b j - Ex.lin a j) ^ 2) ≤ Ex.R a :=
  Ex.graph_iff_box a b

end DiophCompression.ResearchUpgrade.FourSquareSlack
