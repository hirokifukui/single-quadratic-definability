/-
  DiophCompression/NatGuardZ.lean — r05 必須D part 1 (session 5, 2026-08-26, claude.ai direct, no CC).
  (1) Non-negativity guard for ℤ-unknowns: natGuard4 x y z w = x²+y²+z²+w² is ≥ 0 and onto ℕ
      (Lagrange, mathlib `Nat.sum_four_squares`). GPT r04 proposed x²+y²+z²+z (three integers, needs
      Legendre's three-square theorem, not in mathlib) — ruled 2026-08-26: four squares, cost one more witness.
  (2) ℤ-unknowns → ℕ-unknowns: w = u − v. Every set represented with ℤ-unknowns is Diophantine over ℕ
      (`diophN_of_representsZ`). No resource claim (2r unknowns, same degree); used only to certify that the
      image B = e(A) is DiophN, which is the hypothesis form of UniversalPairZ (Spec.lean).
  Statements frozen 2026-08-26 (frozen statement file `NatGuardZ_GraphToUniversalityZ_STATEMENTS.lean`).
-/
import MPUP.Task1

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Four-square guard -/

def natGuard4 (x y z w : ℤ) : ℤ := x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2

theorem natGuard4_nonneg (x y z w : ℤ) : 0 ≤ natGuard4 x y z w := by
  unfold natGuard4; positivity

theorem natGuard4_surjective (c : ℕ) : ∃ x y z w : ℤ, natGuard4 x y z w = c := by
  obtain ⟨a, b, c', d, h⟩ := Nat.sum_four_squares c
  exact ⟨a, b, c', d, by unfold natGuard4; exact_mod_cast h⟩

/-! ### Splitting ℤ-unknowns into differences of ℕ-unknowns -/

/-- Variable map: parameters kept, unknown `j` ↦ `X (castAdd r j) − X (natAdd r j)`. -/
noncomputable def splitSub (n r : ℕ) : (Fin n ⊕ Fin r) → MvPolynomial (Fin n ⊕ Fin (r + r)) ℤ
  | Sum.inl i => X (Sum.inl i)
  | Sum.inr j => X (Sum.inr (Fin.castAdd r j)) - X (Sum.inr (Fin.natAdd r j))

noncomputable def splitUnknowns {n r : ℕ} (P : Poly n r) : Poly n (r + r) := aeval (splitSub n r) P

theorem evalAt_splitUnknowns {n r : ℕ} (P : Poly n r) (a : Fin n → ℕ) (z : Fin (r + r) → ℤ) :
    evalAt (splitUnknowns P) a z = evalAt P a (fun j => z (Fin.castAdd r j) - z (Fin.natAdd r j)) := by
  unfold evalAt splitUnknowns
  rw [map_aeval]
  have hcomp : (eval (Sum.elim (fun i => (a i : ℤ)) z)).comp
      (algebraMap ℤ (MvPolynomial (Fin n ⊕ Fin (r + r)) ℤ)) = RingHom.id ℤ := by
    rw [algebraMap_eq]
    ext x
    simp
  rw [hcomp]
  have : (eval₂Hom (RingHom.id ℤ) (fun v => (eval (Sum.elim (fun i => (a i : ℤ)) z)) (splitSub n r v))) P
      = eval (fun v => (eval (Sum.elim (fun i => (a i : ℤ)) z)) (splitSub n r v)) P := rfl
  rw [this]
  apply congrArg (fun ρ => eval ρ P)
  funext v
  cases v with
  | inl i => simp [splitSub]
  | inr j => simp [splitSub]

theorem representsN_splitUnknowns {n r : ℕ} (P : Poly n r) (S : Set (Fin n → ℕ))
    (h : RepresentsZ P S) : RepresentsN (splitUnknowns P) S := by
  intro a
  rw [h a]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨Fin.append (fun j => (w j).toNat) (fun j => (-w j).toNat), ?_⟩
    rw [evalAt_splitUnknowns]
    convert hw using 2
    funext j
    simp only [Fin.append_left, Fin.append_right]
    exact Int.toNat_sub_toNat_neg (w j)
  · rintro ⟨y, hy⟩
    rw [evalAt_splitUnknowns] at hy
    exact ⟨_, hy⟩

/-- ℤ-unknown representability implies ℕ-unknown Diophantine-ness (w = u − v; no resource claim). -/
theorem diophN_of_representsZ {n r : ℕ} (P : Poly n r) (S : Set (Fin n → ℕ)) (h : RepresentsZ P S) :
    DiophN S :=
  ⟨_, _, representsN_splitUnknowns P S h⟩

theorem diophN_of_diophZ {n : ℕ} {S : Set (Fin n → ℕ)} (h : DiophZ S) : DiophN S := by
  obtain ⟨r, P, hP⟩ := h
  exact diophN_of_representsZ P S hP

end DiophCompression

#print axioms DiophCompression.natGuard4_nonneg
#print axioms DiophCompression.natGuard4_surjective
#print axioms DiophCompression.representsN_splitUnknowns
#print axioms DiophCompression.diophN_of_representsZ
#print axioms DiophCompression.diophN_of_diophZ
