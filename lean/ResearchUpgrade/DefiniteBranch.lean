/-
  DefiniteBranch.lean — Gate-20 Packet 2, task T08 (with T09 already in place).

  The DEFINITE, NONDEGENERATE branch, closed end to end over ℤ:

      LatticeCoercive D c  →  D.Defines f  →  Function.Injective f  →  n ≤ m.

  The analytic input is isolated in ONE named hypothesis, `LatticeCoercive D c`
  (`1 ≤ c` and `c ‖z‖∞² ≤ Q(z)` for every integer `z`).  Everything else is proved:
  the linear part is bounded by `Λ(1+‖a‖)‖z‖`, the input part by `A(1+‖a‖)²`, the equation
  `Q(z) = −ℓ_a(z) − q(a)` then gives `c‖z‖² ≤ Λ(1+‖a‖)‖z‖ + A(1+‖a‖)²`, and the integer
  quadratic bound `le_of_sq_le` turns that into `‖z‖ ≤ (Λ+A+1)(1+‖a‖)` — LINEAR.  Since the
  output is a sub-tuple of `z`, `LinearGrowth f` follows, and T09 finishes.

  Note the honest shape of the coercivity hypothesis: `not_latticeCoercive_of_radical` proves that
  a nonzero radical vector makes it IMPOSSIBLE.  That is exactly why the reviewer's §2 quotients by
  the radical before reaching §3, and it is why T05 (radical annihilation) comes first.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.LinearGrowthDimension
import ResearchUpgrade.RadicalDrift

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- Triangle inequality, spelled locally so the proof does not depend on a mathlib name that
moves between versions. -/
private theorem abs_add' (x y : ℤ) : |x + y| ≤ |x| + |y| := by
  have h1 := le_abs_self x; have h2 := le_abs_self y
  have h3 := neg_abs_le x; have h4 := neg_abs_le y
  rcases abs_cases (x + y) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

/-- The integer quadratic bound: `c s² ≤ B s + C` with `1 ≤ c`, `C ≤ K²` forces `s ≤ B + K`.
One inequality, no square roots, no real numbers. -/
theorem le_of_sq_le {c s B Cc K : ℤ} (hc : 1 ≤ c) (hs : 0 ≤ s) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hKC : Cc ≤ K ^ 2) (h : c * s ^ 2 ≤ B * s + Cc) : s ≤ B + K := by
  by_contra hcon
  push_neg at hcon
  have h1 : K ≤ s := by linarith
  have h2 : K * K ≤ K * s := mul_le_mul_of_nonneg_left h1 hK
  have h3 : (B + K) * s < s * s := by nlinarith
  nlinarith

theorem supNorm_outProj_le {m r : ℕ} (z : OutWit m r → ℤ) : supNorm (outProj z) ≤ supNorm z := by
  refine Finset.sup_le (fun i _ => ?_)
  exact Finset.le_sup (f := fun k => (z k).natAbs) (Finset.mem_univ (Sum.inl i))

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- The analytic input, named: the output/witness form is bounded below by the sup-norm squared,
with a RATIONAL constant `c/N`.  The two-constant form is not cosmetic — see
`not_latticeCoercive_one_shear`: the positive-definite form `x² − 4xy + 5y²` satisfies NO bound
with `N = 1`, because `Q(2,1) = 1` while `‖(2,1)‖∞² = 4`.  A single integer constant would make
the hypothesis unsatisfiable for sheared forms. -/
def LatticeCoercive (c N : ℤ) : Prop :=
  1 ≤ c ∧ 1 ≤ N ∧ ∀ z : OutWit m r → ℤ, c * (supNorm z : ℤ) ^ 2 ≤ N * D.zQuad z

/-! ### Coefficient bounds (everything below is proved, not assumed) -/

def lc1 : ℤ := ∑ k, |D.P.l (Sum.inr k)|
def lc2 : ℤ := ∑ k, ∑ i, |D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i)|
def ac0 : ℤ := |D.P.c|
def ac1 : ℤ := ∑ i, |D.P.l (Sum.inl i)|
def ac2 : ℤ := ∑ i, ∑ j, |D.P.Q (Sum.inl i) (Sum.inl j)|

theorem lc1_nonneg : 0 ≤ D.lc1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem lc2_nonneg : 0 ≤ D.lc2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem ac0_nonneg : 0 ≤ D.ac0 := abs_nonneg _
theorem ac1_nonneg : 0 ≤ D.ac1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem ac2_nonneg : 0 ≤ D.ac2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem lin_coeff_sum_le (a : Fin n → ℤ) :
    (∑ k, |D.zLin a k|) ≤ (D.lc1 + D.lc2) * (1 + (supNorm a : ℤ)) := by
  have hN : (0 : ℤ) ≤ (supNorm a : ℤ) := Int.natCast_nonneg _
  have hstep : ∀ k : OutWit m r, |D.zLin a k|
      ≤ |D.P.l (Sum.inr k)|
        + (∑ i, |D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i)|)
          * (supNorm a : ℤ) := by
    intro k
    have hcomm : (∑ i, a i * (D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i)))
        = ∑ i, (D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i)) * a i := by
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    have hdot := abs_dot_le
      (fun i => D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i)) a
    calc |D.zLin a k| ≤ |D.P.l (Sum.inr k)|
            + |∑ i, a i * (D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i))| := by
          simpa [zLin] using abs_add' _ _
      _ ≤ _ := by rw [hcomm]; linarith [hdot]
  calc (∑ k, |D.zLin a k|)
      ≤ ∑ k, (|D.P.l (Sum.inr k)|
          + (∑ i, |D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i)|)
            * (supNorm a : ℤ)) := Finset.sum_le_sum fun k _ => hstep k
    _ = D.lc1 + D.lc2 * (supNorm a : ℤ) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]; rfl
    _ ≤ (D.lc1 + D.lc2) * (1 + (supNorm a : ℤ)) := by
          have h1 := D.lc1_nonneg; have h2 := D.lc2_nonneg; nlinarith

theorem zLinEval_abs_le (a : Fin n → ℤ) (z : OutWit m r → ℤ) :
    |D.zLinEval a z| ≤ (D.lc1 + D.lc2) * (1 + (supNorm a : ℤ)) * (supNorm z : ℤ) := by
  have h1 : |D.zLinEval a z| ≤ (∑ k, |D.zLin a k|) * (supNorm z : ℤ) :=
    abs_dot_le (fun k => D.zLin a k) z
  have h2 := D.lin_coeff_sum_le a
  have hz : (0 : ℤ) ≤ (supNorm z : ℤ) := Int.natCast_nonneg _
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hz)

theorem aPart_abs_le (a : Fin n → ℤ) :
    |D.aPart a| ≤ (D.ac0 + D.ac1 + D.ac2) * (1 + (supNorm a : ℤ)) ^ 2 := by
  have hN : (0 : ℤ) ≤ (supNorm a : ℤ) := Int.natCast_nonneg _
  have hlin : |∑ i, D.P.l (Sum.inl i) * a i| ≤ D.ac1 * (supNorm a : ℤ) :=
    abs_dot_le (fun i => D.P.l (Sum.inl i)) a
  have hquad : |∑ i, ∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j)|
      ≤ D.ac2 * (supNorm a : ℤ) ^ 2 := by
    calc |∑ i, ∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j)|
        ≤ ∑ i, |∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (∑ j, |D.P.Q (Sum.inl i) (Sum.inl j)|) * (supNorm a : ℤ) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hi : |a i| ≤ (supNorm a : ℤ) := abs_le_supNorm a i
          have hin : |∑ j, D.P.Q (Sum.inl i) (Sum.inl j) * a j|
              ≤ (∑ j, |D.P.Q (Sum.inl i) (Sum.inl j)|) * (supNorm a : ℤ) :=
            abs_dot_le (fun j => D.P.Q (Sum.inl i) (Sum.inl j)) a
          have hrw : (∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j))
              = a i * ∑ j, D.P.Q (Sum.inl i) (Sum.inl j) * a j := by
            rw [Finset.mul_sum]
          rw [hrw, abs_mul]
          have hs : (0 : ℤ) ≤ ∑ j, |D.P.Q (Sum.inl i) (Sum.inl j)| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          calc |a i| * |∑ j, D.P.Q (Sum.inl i) (Sum.inl j) * a j|
              ≤ (supNorm a : ℤ) * ((∑ j, |D.P.Q (Sum.inl i) (Sum.inl j)|) * (supNorm a : ℤ)) := by
                exact mul_le_mul hi hin (abs_nonneg _) hN
            _ = (∑ j, |D.P.Q (Sum.inl i) (Sum.inl j)|) * (supNorm a : ℤ) ^ 2 := by ring
      _ = D.ac2 * (supNorm a : ℤ) ^ 2 := by rw [← Finset.sum_mul]; rfl
  have h0 := D.ac0_nonneg; have h1 := D.ac1_nonneg; have h2 := D.ac2_nonneg
  have habs : |D.aPart a| ≤ D.ac0 + |∑ i, D.P.l (Sum.inl i) * a i|
      + |∑ i, ∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j)| := by
    have t1 := abs_add' (D.P.c + ∑ i, D.P.l (Sum.inl i) * a i)
      (∑ i, ∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j))
    have t2 := abs_add' D.P.c (∑ i, D.P.l (Sum.inl i) * a i)
    simp only [aPart, ac0]
    linarith
  nlinarith [habs, hlin, hquad]

/-! ### T08 — the definite branch -/

theorem supNorm_le_of_coercive {c N : ℤ} (hcoer : D.LatticeCoercive c N) {a : Fin n → ℤ}
    {z : OutWit m r → ℤ} (hz : D.SolZ a z) :
    (supNorm z : ℤ)
      ≤ (N * (D.lc1 + D.lc2) + N * (D.ac0 + D.ac1 + D.ac2) + 1) * (1 + (supNorm a : ℤ)) := by
  obtain ⟨hc1, hN1, hcQ⟩ := hcoer
  set Λ : ℤ := D.lc1 + D.lc2 with hΛ
  set A : ℤ := D.ac0 + D.ac1 + D.ac2 with hA
  have hΛ0 : 0 ≤ Λ := by have := D.lc1_nonneg; have := D.lc2_nonneg; omega
  have hA0 : 0 ≤ A := by
    have := D.ac0_nonneg; have := D.ac1_nonneg; have := D.ac2_nonneg; omega
  have hN : (0 : ℤ) ≤ (supNorm a : ℤ) := Int.natCast_nonneg _
  have hs : (0 : ℤ) ≤ (supNorm z : ℤ) := Int.natCast_nonneg _
  have heq : D.zQuad z + D.zLinEval a z + D.aPart a = 0 := by
    have := hz; unfold QuadraticGraphData.SolZ at this; rwa [D.evalZ] at this
  have hQ : D.zQuad z ≤ |D.zLinEval a z| + |D.aPart a| := by
    have h1 : D.zQuad z = -(D.zLinEval a z) - D.aPart a := by linarith
    have h2 := neg_abs_le (D.zLinEval a z)
    have h3 := neg_abs_le (D.aPart a)
    linarith
  have hmain : c * (supNorm z : ℤ) ^ 2
      ≤ (N * Λ * (1 + (supNorm a : ℤ))) * (supNorm z : ℤ)
        + N * A * (1 + (supNorm a : ℤ)) ^ 2 := by
    have hL := D.zLinEval_abs_le a z
    have hP := D.aPart_abs_le a
    have hz2 := hcQ z
    nlinarith [hQ, hL, hP, hz2, hN1, hs, hN]
  have hK : ((N * A + 1) * (1 + (supNorm a : ℤ))) ^ 2 ≥ N * A * (1 + (supNorm a : ℤ)) ^ 2 := by
    nlinarith
  have hNa : (0 : ℤ) ≤ 1 + (supNorm a : ℤ) := by linarith
  have hNpos : (0 : ℤ) ≤ N := by linarith
  have hNA : (0 : ℤ) ≤ N * A := mul_nonneg hNpos hA0
  have hB0 : (0 : ℤ) ≤ N * Λ * (1 + (supNorm a : ℤ)) :=
    mul_nonneg (mul_nonneg hNpos hΛ0) hNa
  have hK0 : (0 : ℤ) ≤ (N * A + 1) * (1 + (supNorm a : ℤ)) :=
    mul_nonneg (by linarith) hNa
  have := le_of_sq_le (c := c) (s := (supNorm z : ℤ)) (B := N * Λ * (1 + (supNorm a : ℤ)))
    (Cc := N * A * (1 + (supNorm a : ℤ)) ^ 2) (K := (N * A + 1) * (1 + (supNorm a : ℤ)))
    hc1 hs hB0 hK0 hK hmain
  nlinarith [this]

theorem linearGrowth_of_coercive {c N : ℤ} (hcoer : D.LatticeCoercive c N)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : LinearGrowth f := by
  have hN1 : 1 ≤ N := hcoer.2.1
  set Λ : ℤ := D.lc1 + D.lc2 with hΛ
  set A : ℤ := D.ac0 + D.ac1 + D.ac2 with hA
  have hΛ0 : 0 ≤ Λ := by have := D.lc1_nonneg; have := D.lc2_nonneg; omega
  have hA0 : 0 ≤ A := by
    have := D.ac0_nonneg; have := D.ac1_nonneg; have := D.ac2_nonneg; omega
  refine ⟨(N * Λ + N * A + 1).toNat, fun a => ?_⟩
  obtain ⟨u, hu⟩ : D.Graph a (f a) := (hf a (f a)).2 rfl
  have hz : D.SolZ a (Sum.elim (f a) u) := hu
  have hbound := D.supNorm_le_of_coercive hcoer hz
  have hproj : supNorm (f a) ≤ supNorm (Sum.elim (f a) u) := by
    have : outProj (Sum.elim (f a) u) = f a := rfl
    rw [← this]; exact supNorm_outProj_le _
  have hcast : ((N * Λ + N * A + 1).toNat : ℤ) = N * Λ + N * A + 1 :=
    Int.toNat_of_nonneg (by nlinarith)
  have h1 : (supNorm (f a) : ℤ) ≤ (N * Λ + N * A + 1) * (1 + (supNorm a : ℤ)) := by
    have : (supNorm (f a) : ℤ) ≤ (supNorm (Sum.elim (f a) u) : ℤ) := by exact_mod_cast hproj
    linarith
  have h2 : (supNorm (f a) : ℤ) ≤ (((N * Λ + N * A + 1).toNat * (1 + supNorm a) : ℕ) : ℤ) := by
    push_cast [hcast]; linarith
  exact_mod_cast h2

/-- **T08 + T09.**  In the coercive (definite, nondegenerate) branch, an injective SE₂-definable
total function forces `n ≤ m`. -/
theorem dim_le_of_coercive {c N : ℤ} (hcoer : D.LatticeCoercive c N)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) : n ≤ m :=
  dim_le_of_linearGrowth_injective (D.linearGrowth_of_coercive hcoer hf) hinj

/-! ### A machine-checkable certificate for the coercivity hypothesis

`LatticeCoercive` is the one analytic input of T08.  Rather than assume it, we make it
CERTIFIABLE: an SOS decomposition of `N·Q` together with a left inverse of the transforming
matrix.  Every positive-definite rational form admits such a certificate (Lagrange
diagonalisation, then clear denominators) — producing it for a concrete `D` is CAS work; the
implication certificate ⇒ coercivity is proved here in the kernel. -/

theorem supNorm_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (z : ι → ℤ) : supNorm z = 0 := by
  simp [supNorm]

theorem exists_supNorm_eq {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℤ) :
    ∃ i, (supNorm z : ℤ) = |z i| := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
      (fun i => (z i).natAbs)
  refine ⟨i, ?_⟩
  rw [supNorm, hi]
  first
    | exact (Int.abs_eq_natAbs _).symm
    | exact Int.natCast_natAbs _
    | simp

/-- The certificate.  `L` is the transforming matrix, `d` the positive weights, `M` a left
inverse of `L` up to the integer `N'`. -/
structure CoercivityCertificate {n m r : ℕ} (D : QuadraticGraphData n m r) where
  N : ℤ
  N' : ℤ
  L : OutWit m r → OutWit m r → ℤ
  d : OutWit m r → ℤ
  M : OutWit m r → OutWit m r → ℤ
  hN : 1 ≤ N
  hN' : 1 ≤ N'
  hd : ∀ i, 1 ≤ d i
  hsos : ∀ z, N * D.zQuad z = ∑ i, d i * (∑ j, L i j * z j) ^ 2
  hinv : ∀ (z : OutWit m r → ℤ) (j), N' * z j = ∑ i, M j i * (∑ k, L i k * z k)

namespace CoercivityCertificate

variable {n m r : ℕ} {D : QuadraticGraphData n m r} (cert : CoercivityCertificate D)

/-- `L z`. -/
def img (z : OutWit m r → ℤ) : OutWit m r → ℤ := fun i => ∑ j, cert.L i j * z j

/-- A crude bound on the entries of the left inverse. -/
def Bsum : ℤ := ∑ j, ∑ i, |cert.M j i|

theorem Bsum_nonneg : 0 ≤ cert.Bsum :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem row_le_Bsum (j : OutWit m r) : (∑ i, |cert.M j i|) ≤ cert.Bsum :=
  Finset.single_le_sum (f := fun j => ∑ i, |cert.M j i|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-- The SOS half: `‖Lz‖∞² ≤ N · Q(z)`. -/
theorem sos_lower (z : OutWit m r → ℤ) :
    (supNorm (cert.img z) : ℤ) ^ 2 ≤ cert.N * D.zQuad z := by
  rw [cert.hsos z]
  rcases isEmpty_or_nonempty (OutWit m r) with hemp | hne
  · rw [supNorm_of_isEmpty]
    simp
  · obtain ⟨i0, hi0⟩ := exists_supNorm_eq (cert.img z)
    have hterms : ∀ i ∈ (Finset.univ : Finset (OutWit m r)),
        0 ≤ cert.d i * (∑ j, cert.L i j * z j) ^ 2 := by
      intro i _
      exact mul_nonneg (by have := cert.hd i; linarith) (sq_nonneg _)
    have hsingle := Finset.single_le_sum
      (f := fun i => cert.d i * (∑ j, cert.L i j * z j) ^ 2) hterms (Finset.mem_univ i0)
    have hd0 : 1 ≤ cert.d i0 := cert.hd i0
    have hsq : (0 : ℤ) ≤ (∑ j, cert.L i0 j * z j) ^ 2 := sq_nonneg _
    have hlhs : (supNorm (cert.img z) : ℤ) ^ 2 = (∑ j, cert.L i0 j * z j) ^ 2 := by
      rw [hi0]; rw [sq_abs]; rfl
    rw [hlhs]
    nlinarith [hsingle, hd0, hsq]

/-- The inverse half: `N' ‖z‖∞ ≤ (B+1) ‖Lz‖∞`. -/
theorem inv_upper (z : OutWit m r → ℤ) :
    cert.N' * (supNorm z : ℤ) ≤ (cert.Bsum + 1) * (supNorm (cert.img z) : ℤ) := by
  have hw : (0 : ℤ) ≤ (supNorm (cert.img z) : ℤ) := Int.natCast_nonneg _
  rcases isEmpty_or_nonempty (OutWit m r) with hemp | hne
  · rw [supNorm_of_isEmpty z]
    have := cert.Bsum_nonneg
    simp
    nlinarith
  · obtain ⟨j0, hj0⟩ := exists_supNorm_eq z
    have hN'0 : (0 : ℤ) ≤ cert.N' := by have := cert.hN'; linarith
    have hdot : |∑ i, cert.M j0 i * (cert.img z) i|
        ≤ (∑ i, |cert.M j0 i|) * (supNorm (cert.img z) : ℤ) :=
      abs_dot_le (fun i => cert.M j0 i) (cert.img z)
    have heq : cert.N' * z j0 = ∑ i, cert.M j0 i * (cert.img z) i := cert.hinv z j0
    have habs : |cert.N' * z j0| ≤ (∑ i, |cert.M j0 i|) * (supNorm (cert.img z) : ℤ) := by
      rw [heq]; exact hdot
    have hsplit : |cert.N' * z j0| = cert.N' * |z j0| := by
      rw [abs_mul, abs_of_nonneg hN'0]
    have hrow := cert.row_le_Bsum j0
    rw [hj0]
    nlinarith [habs, hsplit, hrow, hw]

/-- **The certificate implies coercivity.** -/
theorem latticeCoercive :
    D.LatticeCoercive (cert.N' ^ 2) (cert.N * (cert.Bsum + 1) ^ 2) := by
  have hB := cert.Bsum_nonneg
  have hN := cert.hN
  have hN' := cert.hN'
  refine ⟨by nlinarith, by nlinarith, fun z => ?_⟩
  have h1 := cert.inv_upper z
  have h2 := cert.sos_lower z
  have hz : (0 : ℤ) ≤ (supNorm z : ℤ) := Int.natCast_nonneg _
  have hw : (0 : ℤ) ≤ (supNorm (cert.img z) : ℤ) := Int.natCast_nonneg _
  have hL : (0 : ℤ) ≤ cert.N' * (supNorm z : ℤ) := by nlinarith
  have hsq : (cert.N' * (supNorm z : ℤ)) ^ 2
      ≤ ((cert.Bsum + 1) * (supNorm (cert.img z) : ℤ)) ^ 2 := by
    have hR : (0 : ℤ) ≤ (cert.Bsum + 1) * (supNorm (cert.img z) : ℤ) := by nlinarith
    nlinarith [h1, hL, hR]
  nlinarith [hsq, h2, hB, hN]

end CoercivityCertificate

/-- **T08, certified form.**  A coercivity certificate plus injectivity gives `n ≤ m` with NO
remaining hypothesis about the form beyond the certificate itself. -/
theorem dim_le_of_certificate {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (cert : CoercivityCertificate D) (hf : D.Defines f) (hinj : Function.Injective f) : n ≤ m :=
  D.dim_le_of_coercive cert.latticeCoercive hf hinj



/-! ### Controls -/

/-- NEGATIVE control, and the reason the radical must be quotiented out first: a nonzero radical
vector makes coercivity IMPOSSIBLE at every `c`. -/
theorem not_latticeCoercive_of_radical {e : OutWit m r → ℤ} (he : D.InRadical e) (hne : e ≠ 0)
    (c N : ℤ) : ¬ D.LatticeCoercive c N := by
  rintro ⟨hc1, hN1, hcQ⟩
  have hQe : D.zQuad e = 0 := D.zQuad_of_radical he
  have h := hcQ e
  rw [hQe, mul_zero] at h
  have hs : supNorm e ≠ 0 := fun h0 => hne (supNorm_eq_zero h0)
  have hs1 : (1 : ℤ) ≤ (supNorm e : ℤ) := by
    have : 1 ≤ supNorm e := Nat.one_le_iff_ne_zero.2 hs
    exact_mod_cast this
  nlinarith

end QuadraticGraphData

/-- POSITIVE control: the hypothesis is satisfiable — with no outputs and no witnesses the form is
coercive with `c = 1` (both sides are 0).  A non-degenerate example is recorded as an owed control. -/
theorem latticeCoercive_trivial {n : ℕ} (D : QuadraticGraphData n 0 0) :
    D.LatticeCoercive 1 1 := by
  refine ⟨le_refl 1, le_refl 1, fun z => ?_⟩
  have hz : supNorm z = 0 := by
    simp [supNorm]
  simp [hz, QuadraticGraphData.zQuad]

end DiophCompression.ResearchUpgrade
