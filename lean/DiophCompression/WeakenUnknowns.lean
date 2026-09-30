/-
  DiophCompression/WeakenUnknowns.lean — r13 mandatory F leaf (session 13, 2026-08-28).
  The witness-padding trio, excised VERBATIM from GraphToUniversalityZ.lean so that
  Class_D9 (and hence the entire graph-headline closure) no longer pulls
  GraphToUniversalityZ -> {Sandwich, NatGuardZ}. Same namespace, same fully
  qualified names; import architecture only, no proof changes.
-/
import MPUP.Spec

namespace DiophCompression

open MvPolynomial MPUP

/-- Add `m` unknowns after the existing `r`; the polynomial ignores them. -/
noncomputable def weakenUnknowns {n r : ℕ} (m : ℕ) (P : Poly n r) : Poly n (r + m) :=
  rename (Sum.map id (Fin.castAdd m)) P

theorem evalAt_weakenUnknowns {n r m : ℕ} (P : Poly n r) (a : Fin n → ℕ) (z : Fin (r + m) → ℤ) :
    evalAt (weakenUnknowns m P) a z = evalAt P a (fun j => z (Fin.castAdd m j)) := by
  simp only [evalAt, weakenUnknowns, eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v; cases v <;> rfl

theorem totalDegree_weakenUnknowns_le {n r m : ℕ} (P : Poly n r) :
    (weakenUnknowns m P).totalDegree ≤ P.totalDegree :=
  totalDegree_rename_le _ _

end DiophCompression
