/-
  IsotropicCoset.lean — s48.  Gate22 task **G22-T12**: from the rational section to an INTEGRAL
  coset, and hence to `WeakVectorCosetNF` — the second disjunct of the II-D summit.

  G22-T11 produced a section that solves the equation at every input, is anchored at an integer
  solution, and is of total degree ≤ 2 in the input.  It is rational.  What remains is the
  reviewer's §5.2: ONE modulus `M` clearing the denominators of the finitely many coefficients,
  after which the section takes INTEGER values on the whole coset `a₀ + M ℤⁿ`.

  Two applications of `exists_int_clear` do it — one at the index type `OutWit × Fin n` for the
  shifted linear coefficients, one at `OutWit × Fin n × Fin n` for the quadratic ones — and
  `M := d_A · d_B` serves both, because `M·Q ∈ ℤ` already gives `M²·Q ∈ ℤ`.  **`M` does not depend
  on the input** (reviewer's control 18), and the coset is a full lattice coset, so it contains
  `t` and `−t` alike (control 19).

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.CosetShift
import ResearchUpgrade.IsotropicSection
import ResearchUpgrade.RadicalBridge

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **G22-T12.**  A degree-≤2 rational section that is integral at `ρ` and solves the equation
everywhere puts `f` in the weak vector coset normal form.  The modulus is built here, once, from
the coefficients; it is independent of the input. -/
theorem weakVectorCosetNF_of_quadSection
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (sec : (Fin n → ℤ) → OutWit m r → ℚ)
    (q : OutWit m r → QuadForm n)
    (hq : ∀ (a : Fin n → ℤ) (k : OutWit m r), sec a k = (q k).eval (castQ a))
    {ρ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hanchor : sec ρ = toQ z₀)
    (hsolves : ∀ a : Fin n → ℤ,
      D.zQuadQ (sec a) + D.zLinQ a (sec a) + (D.aPart a : ℚ) = 0) :
    WeakVectorCosetNF f := by
  classical
  -- the two coefficient families
  set A : (OutWit m r × Fin n) → ℚ := fun x =>
    (q x.1).l x.2 + ∑ j, ((q x.1).Q j x.2 + (q x.1).Q x.2 j) * castQ ρ j with hA
  set B : (OutWit m r × Fin n × Fin n) → ℚ := fun x => (q x.1).Q x.2.1 x.2.2 with hB
  obtain ⟨wA, dA, hdA, hwA⟩ := exists_int_clear A
  obtain ⟨wB, dB, hdB, hwB⟩ := exists_int_clear B
  set M : ℕ := dA * dB with hM
  have hMpos : 0 < M := Nat.mul_pos hdA hdB
  have hMQ : ((M : ℕ) : ℚ) = (dA : ℚ) * (dB : ℚ) := by rw [hM]; push_cast; ring
  -- the integral coefficients
  set lz : OutWit m r → Fin n → ℤ := fun k i => (dB : ℤ) * wA (k, i) with hlz
  set Qz : OutWit m r → Matrix (Fin n) (Fin n) ℤ :=
    fun k i j => (M : ℤ) * (dA : ℤ) * wB (k, (i, j)) with hQz
  have hc : ∀ k, (q k).eval (castQ ρ) = ((z₀ k : ℤ) : ℚ) := by
    intro k
    rw [← hq ρ k, hanchor]
    rfl
  have hl : ∀ (k : OutWit m r) (i : Fin n),
      ((q k).shift ρ (M : ℤ)).l i = ((lz k i : ℤ) : ℚ) := by
    intro k i
    have h1 := hwA (k, i)
    simp only [hA] at h1
    simp only [QuadForm.shift, hlz]
    push_cast
    rw [hMQ, h1]
    ring
  have hQ : ∀ (k : OutWit m r) (i j : Fin n),
      ((q k).shift ρ (M : ℤ)).Q i j = ((Qz k i j : ℤ) : ℚ) := by
    intro k i j
    have h1 := hwB (k, (i, j))
    simp only [hB] at h1
    simp only [QuadForm.shift, hQz]
    push_cast
    rw [hMQ, h1]
    ring
  -- the integer section on the coset
  set zint : (Fin n → ℤ) → OutWit m r → ℤ := fun t k =>
    z₀ k + (∑ i, lz k i * t i) + ∑ i, ∑ j, t i * (Qz k i j * t j) with hzint
  have hmatch : ∀ (t : Fin n → ℤ) (k : OutWit m r),
      ((zint t k : ℤ) : ℚ) = (q k).eval (castQ (ρ + (M : ℤ) • t)) := by
    intro t k
    rw [QuadForm.eval_shift_int (q k) ρ (M : ℤ) (hc k) (hl k) (hQ k) t]
  have hsol : ∀ t : Fin n → ℤ, D.SolZ (ρ + (M : ℤ) • t) (zint t) := by
    intro t
    have hsec : toQ (zint t) = sec (ρ + (M : ℤ) • t) := by
      funext k
      rw [hq (ρ + (M : ℤ) • t) k]
      exact hmatch t k
    have hQ0 := hsolves (ρ + (M : ℤ) • t)
    rw [← hsec, D.zQuadQ_toQ, D.zLinQ_toQ] at hQ0
    have hint : D.zQuad (zint t) + D.zLinEval (ρ + (M : ℤ) • t) (zint t)
        + D.aPart (ρ + (M : ℤ) • t) = 0 := by exact_mod_cast hQ0
    unfold QuadraticGraphData.SolZ
    rw [D.evalZ]
    exact hint
  exact weakVectorCosetNF_of_rational_section hf hMpos q zint
    (fun t k => hmatch t k) hsol

/-- **The isotropic branch of II-D.**  An affine centre family, an integer solution whose
off-centre part is seen by an isotropic direction, and `Defines f` ⇒ `f` has a weak vector coset
normal form; with injectivity, `n ≤ m`. -/
theorem weakVectorCosetNF_of_isotropic
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a))
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz₀ : D.SolZ a₀ z₀)
    {e : OutWit m r → ℚ} (he : D.zQuadQ e = 0)
    (hb : D.zPolarQ (toQ z₀ - centreFamily c₀ cs a₀) e ≠ 0) :
    WeakVectorCosetNF f := by
  classical
  set v₀ : OutWit m r → ℚ := toQ z₀ - centreFamily c₀ cs a₀ with hv₀
  have hquad : ∀ k : OutWit m r,
      IsQuadCoef (fun a : Fin n → ℤ => D.isoSection c₀ cs e v₀ a k) :=
    fun k => D.isQuadCoef_isoSection c₀ cs e v₀ k
  choose q hq using hquad
  exact D.weakVectorCosetNF_of_quadSection hf (D.isoSection c₀ cs e v₀) q
    (fun a k => hq k a) (D.isoSection_anchor hcen hz₀)
    (fun a => D.isoSection_solves he hb hcen a)

theorem dim_le_of_isotropic
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a))
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz₀ : D.SolZ a₀ z₀)
    {e : OutWit m r → ℚ} (he : D.zQuadQ e = 0)
    (hb : D.zPolarQ (toQ z₀ - centreFamily c₀ cs a₀) e ≠ 0) :
    n ≤ m := by
  by_contra hcon
  have h1 : m < n := by omega
  exact not_injective_of_weakVectorCosetNF h1 f
    (D.weakVectorCosetNF_of_isotropic hf hcen hz₀ he hb) hinj

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
