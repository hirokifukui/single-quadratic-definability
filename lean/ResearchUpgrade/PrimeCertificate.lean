/-
  PrimeCertificate.lean — Gate-20 Packet N1, the N1.1b interface.

  N1.1b in general ("`¬ IsSquare (−D·δ)` ⇒ a residue witness exists") is the classical statement
  that a non-square integer is a quadratic non-residue at some prime.  It is NOT in mathlib:
  LeanSearch on "integer which is a quadratic residue modulo every prime is a perfect square" and
  on "if an integer is not a square then there exists a prime for which it is a quadratic
  nonresidue" returns only the pointwise characterisations (`ZMod.nonsquare_iff_jacobiSym_eq_neg_one`,
  `quadraticChar_neg_one_iff_not_isSquare`), never the global existence statement.  (Recorded as
  "not found by these queries", not as "absent from mathlib".)  Proving it needs squarefree
  decomposition + CRT + reciprocity and stays an open leaf.

  What is proved here instead makes the leaf USABLE rather than blocking: **one explicitly
  exhibited prime is a complete certificate**.  If a single `p` coprime to the modulus carries
  `(−D/p) = −1` and `(δ/p) = +1`, then its residue class is a residue witness, and N1.1a turns it
  into infinitely many such primes.  So for every concrete pair `(D, δ)` the leaf is discharged by
  a one-line CAS search, and the general statement is only needed for a uniform theorem.

  * `stdModulus D δ = 4|D||δ|` — carries both Jacobi periods and is even.
  * `residueWitness_of_prime` / `residueWitness_of_prime_std` — prime certificate ⇒ residue witness.
    (Primality is not even used: coprimality to the modulus suffices.)
  * `discriminant_rigidity_of_primeCertificate` — the practical entry point to N2.2: one prime
    certificate kills total representability of `A T² + B T + C` by `x² + D y²`.
  * `residueWitness_one_minusThree_via_prime` — the hand-built witness of `DiscriminantRigidity`
    re-derived as an instance with `p = 7`, `stdModulus 1 (−3) = 12`, `7 % 12 = 7`.

  Claim tags: [P] (std-3).  Baseline read-only.
-/
import Lean.Parser.Command
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import ResearchUpgrade.DiscriminantRigidity
import ResearchUpgrade.SeparatingPrime

namespace DiophCompression.ResearchUpgrade

/-- The standard modulus for the pair `(D, δ)`: even, and divisible by both Jacobi periods
`4|D|` and `4|δ|`. -/
def stdModulus (D δ : ℤ) : ℕ := 4 * D.natAbs * δ.natAbs

/-- **A single prime is a complete certificate for N1.1b.**  Primality is not used; only
coprimality to the modulus. -/
theorem residueWitness_of_prime (D δ : ℤ) (M p : ℕ)
    (hM0 : 0 < M) (h2M : 2 ∣ M) (h4D : 4 * D.natAbs ∣ M) (h4δ : 4 * δ.natAbs ∣ M)
    (hcop : Nat.Coprime p M)
    (hjD : jacobiSym (-D) p = -1) (hjδ : jacobiSym δ p = 1) :
    ResidueWitness D δ M (p % M) := by
  have hgcd : Nat.gcd p M = 1 := hcop
  have hodd_p : Odd p := by
    rw [Nat.odd_iff]
    by_contra hev
    have h2p : 2 ∣ p := by omega
    have hdvd : (2 : ℕ) ∣ Nat.gcd p M := Nat.dvd_gcd h2p h2M
    rw [hgcd] at hdvd
    omega
  have hmod2 : p % M % 2 = p % 2 := Nat.mod_mod_of_dvd p h2M
  have hodd' : Odd (p % M) := by
    rw [Nat.odd_iff] at hodd_p ⊢
    omega
  have hcop' : Nat.Coprime (p % M) M := by
    show Nat.gcd (p % M) M = 1
    rw [← Nat.gcd_rec M p, Nat.gcd_comm M p]
    exact hgcd
  refine ⟨hM0, h2M, h4D, h4δ, hcop', ?_, ?_⟩
  · have hper : 4 * (-D).natAbs ∣ M := by rwa [Int.natAbs_neg]
    rw [jacobiSym.mod_right _ hodd', Nat.mod_mod_of_dvd p hper,
      ← jacobiSym.mod_right _ hodd_p]
    exact hjD
  · rw [jacobiSym.mod_right _ hodd', Nat.mod_mod_of_dvd p h4δ,
      ← jacobiSym.mod_right _ hodd_p]
    exact hjδ

/-- The same with the standard modulus `4|D||δ|`. -/
theorem residueWitness_of_prime_std (D δ : ℤ) (hD : D ≠ 0) (hδ : δ ≠ 0) (p : ℕ)
    (hcop : Nat.Coprime p (stdModulus D δ))
    (hjD : jacobiSym (-D) p = -1) (hjδ : jacobiSym δ p = 1) :
    ResidueWitness D δ (stdModulus D δ) (p % stdModulus D δ) := by
  have hDa : 0 < D.natAbs := by omega
  have hδa : 0 < δ.natAbs := by omega
  refine residueWitness_of_prime D δ (stdModulus D δ) p ?_ ?_ ?_ ?_ hcop hjD hjδ
  · simp only [stdModulus]; positivity
  · exact ⟨2 * D.natAbs * δ.natAbs, by simp only [stdModulus]; ring⟩
  · exact ⟨δ.natAbs, by simp only [stdModulus]⟩
  · exact ⟨D.natAbs, by simp only [stdModulus]; ring⟩

/-- **Practical entry point to N2.2.**  One prime certificate for `(D, B² − 4AC)` kills total
representability of `A T² + B T + C` by `x² + D y²` over ℚ. -/
theorem discriminant_rigidity_of_primeCertificate (D A B C : ℤ) (hA : A ≠ 0) (hD : D ≠ 0)
    (hδ : B ^ 2 - 4 * A * C ≠ 0) (p : ℕ)
    (hcop : Nat.Coprime p (stdModulus D (B ^ 2 - 4 * A * C)))
    (hjD : jacobiSym (-D) p = -1) (hjδ : jacobiSym (B ^ 2 - 4 * A * C) p = 1)
    (htotal : ∀ t : ℤ, ∃ r s : ℚ,
      ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (D : ℚ) * s ^ 2) : False :=
  discriminant_rigidity_of_residueWitness D A B C hA
    (stdModulus D (B ^ 2 - 4 * A * C)) (p % stdModulus D (B ^ 2 - 4 * A * C))
    (residueWitness_of_prime_std D (B ^ 2 - 4 * A * C) hD hδ p hcop hjD hjδ) htotal

/-! ### The hand-built witness, re-derived from the prime certificate `p = 7` -/

theorem stdModulus_one_minusThree : stdModulus 1 (-3) = 12 := by
  simp only [stdModulus]
  rfl

/-- `residueWitness_one_minusThree` as an instance of the general construction: the certificate is
the single prime `7`, and `7 % stdModulus 1 (−3) = 7 % 12 = 7`. -/
theorem residueWitness_one_minusThree_via_prime :
    ResidueWitness 1 (-3) (stdModulus 1 (-3)) (7 % stdModulus 1 (-3)) := by
  refine residueWitness_of_prime_std 1 (-3) (by norm_num) (by norm_num) 7 ?_ ?_ ?_
  · rw [stdModulus_one_minusThree]; decide
  · exact residueWitness_one_minusThree.2.2.2.2.2.1
  · exact residueWitness_one_minusThree.2.2.2.2.2.2

end DiophCompression.ResearchUpgrade
