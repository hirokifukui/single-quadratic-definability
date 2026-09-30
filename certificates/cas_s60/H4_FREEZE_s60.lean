import ResearchUpgrade
/-
  H4_FREEZE_s60.lean — GATE30 (GPT R48) Packet B: short consequences of the R48 classification.
  B1 zero-witness scalar iff (no TCER), B2 unique-witness presentation (TCER, forward only), B3/B4 floor(a/3) needs exactly
  one witness in this fixed format (no TCER).
  DRAFT under Dr. Fukui's ruling of 2026-09-28 13:00 ("すべてOK", R-D); each statement truth-checked (comment above it)
  before freezing.  Intended home: `ResearchUpgrade/WitnessCount.lean`.
-/
namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial

/- TRUTH CHECK.  The sealed predicate is `∃ r, ∃ P : Poly (n + m) r, deg ≤ 2 ∧ RepresentsZZ P (graphVecZZ f)`; this fixes r. -/
/-- `f` is defined by one equation of total degree ≤ 2 with exactly `r` integer witnesses (sealed definition, `r` fixed). -/
def SingleQuadraticWithWitnessesZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (r : ℕ) : Prop :=
  ∃ P : MPUP.Poly (n + m) r, P.totalDegree ≤ 2 ∧ DiophCompression.RepresentsZZ P (DiophCompression.graphVecZZ f)

/- TRUTH CHECK.  Unfolding: both sides are `∃ r P, …`. -/
theorem singleQuadratic_iff_exists_witnesses {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ ∃ r, SingleQuadraticWithWitnessesZZ f r := by
  sorry

/- TRUTH CHECK.  Same construction as `graphData_of_singleQuadraticDefinable`, which keeps the witness count r. -/
theorem graphData_of_witnesses {n m r : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : SingleQuadraticWithWitnessesZZ f r) : ∃ D : QuadraticGraphData n m r, D.Defines f := by
  sorry

/- TRUTH CHECK.  In `scalar_commonSlope_or_rn_of_TCER` TCER is used only when the polar rank exceeds one; the Q ≡ 0 branch
   and the rank-one branch (witness-radical compiler) are TCER-free.  Here the rank-≥2 branch is excluded by hypothesis. -/
theorem scalar_rn_of_polarRank_le_one :
    ∀ (n r : ℕ) (D : QuadraticGraphData n 1 r) (f : (Fin n → ℤ) → (Fin 1 → ℤ)), D.Defines f → D.polarRank ≤ 1 →
      ∃ (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ),
        ∀ (x : Fin n → ℤ) (y : ℤ), Rn a β d E φ g x y ↔ y = scalarOut f x := by
  sorry

/- TRUTH CHECK.  (⇒) r = 0: the unknowns are the one output, so polarRank ≤ m + r = 1 (`polarRank_le`); previous theorem, then
   `rn_classify`.  No TCER.  (⇐) `zeroWitness_of_globalQuadratic`/`_parityAffine` give a polynomial over Fin (n+1) ⊕ Fin 0 =
   the variables of `Poly (n + 1) 0`.  C is NOT on the right: a common slope need not be zero-witness (floor(a/3), below). -/
/-- **B1.**  A scalar function is defined by one quadratic equation WITHOUT witnesses iff it is a global rational quadratic or
parity-affine.  Unconditional. -/
theorem zeroWitness_iff {n : ℕ} (f : (Fin n → ℤ) → (Fin 1 → ℤ)) :
    SingleQuadraticWithWitnessesZZ f 0 ↔ GlobalQuadratic (scalarOut f) ∨ ParityAffineNF (scalarOut f) := by
  sorry

/- TRUTH CHECK.  Witness uniqueness at EVERY point v (not only on the graph); no existence is required off the graph. -/
/-- A presentation with unique witnesses. -/
def UniqueWitnessSingleQuadraticZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ r, ∃ P : MPUP.Poly (n + m) r, P.totalDegree ≤ 2 ∧ DiophCompression.RepresentsZZ P (DiophCompression.graphVecZZ f) ∧
    ∀ (v : Fin (n + m) → ℤ) (y y' : Fin r → ℤ),
      DiophCompression.evalAtZZ P v y = 0 → DiophCompression.evalAtZZ P v y' = 0 → y = y'

/- TRUTH CHECK.  Existence: (f a, u) with u from RepresentsZZ.  Uniqueness: a solution (b, u) puts pairVec a b in the graph,
   so b = f a; then the witnesses agree by the uniqueness clause. -/
/-- For a unique-witness presentation, each input has exactly one solution (output, witnesses). -/
theorem existsUnique_of_uniqueWitness {n m r : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (P : MPUP.Poly (n + m) r)
    (hrep : DiophCompression.RepresentsZZ P (DiophCompression.graphVecZZ f))
    (hu : ∀ (v : Fin (n + m) → ℤ) (y y' : Fin r → ℤ),
      DiophCompression.evalAtZZ P v y = 0 → DiophCompression.evalAtZZ P v y' = 0 → y = y')
    (a : Fin n → ℤ) :
    ∃! p : (Fin m → ℤ) × (Fin r → ℤ), DiophCompression.evalAtZZ P (pairVec a p.1) p.2 = 0 := by
  sorry

/- TRUTH CHECK.  `commonSlope_posDef_presentation`: graph iff and (u, e) unique for every (a, b); rename the witness type
   Fin n ⊕ (Fin n → Fin M) to Fin (n + M^n) as in `singleQuadratic_of_commonSlope_witnesses`; every v is pairVec of its halves. -/
theorem uniqueWitness_of_commonSlope {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : CommonSlopeIntNF f) :
    UniqueWitnessSingleQuadraticZZ f := by
  sorry

/- TRUTH CHECK.  Fin 0 → ℤ has one element. -/
theorem uniqueWitness_of_zeroWitness {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : SingleQuadraticWithWitnessesZZ f 0) :
    UniqueWitnessSingleQuadraticZZ f := by
  sorry

/- TRUTH CHECK.  (⇐) forget uniqueness.  (⇒) m ≠ 1: common slope (`singleQuadratic_iff_commonSlope_of_TCER_of_ne_one`);
   m = 1: C, Q or H (`sealed_scalarFamilies_of_TCER`); C by the encoder, Q/H by B1 (⇐) and the zero-witness case.
   TCER only in (⇒).  Not a claim that every presentation has unique witnesses. -/
/-- **B2.**  TCER ⇒ every SE₂ function has a single quadratic presentation with unique witnesses (all n, m). -/
theorem singleQuadratic_iff_uniqueWitness_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ UniqueWitnessSingleQuadraticZZ f := by
  sorry

/- TRUTH CHECK.  Int division by 3 is Euclidean (= floor for the positive divisor 3), also for negative a. -/
/-- `a ↦ ⌊a/3⌋`. -/
def floorThird : (Fin 1 → ℤ) → (Fin 1 → ℤ) := fun a _ => a 0 / 3

/- TRUTH CHECK.  Variables: inl 0 = a (Fin.castAdd 1 0), inl 1 = b (Fin.natAdd 1 0), inr 0 = u.  (3b − a + 1)² + u² − 1. -/
/-- The one-witness equation for `floorThird`. -/
noncomputable def floorThirdPoly : MPUP.Poly (1 + 1) 1 :=
  (C 3 * X (Sum.inl 1) - X (Sum.inl 0) + 1) ^ 2 + X (Sum.inr 0) ^ 2 - 1

/- TRUTH CHECK (leg 1 M6, leg 2 M6).  P = 0 ⇒ (3b−a+1)² ≤ 1 ⇒ a − 2 ≤ 3b ≤ a ⇒ b = a/3.  Conversely a = 3q + r: u = 1 if r = 1,
   else 0.  Degree 2. -/
/-- **B3.**  `floorThird` is defined with one witness.  Unconditional. -/
theorem floorThird_oneWitness : SingleQuadraticWithWitnessesZZ floorThird 1 := by
  sorry

/- TRUTH CHECK.  a = 1, b = 0: (0 − 1 + 1)² + u² − 1 = u² − 1 = 0 at u = ±1.  Output unique, witness not unique. -/
/-- Control: in this presentation the witness is not unique (a ≡ 1 mod 3). -/
theorem floorThirdPoly_two_witnesses :
    DiophCompression.evalAtZZ floorThirdPoly (pairVec (fun _ => 1) (fun _ => 0)) (fun _ => 1) = 0 ∧
    DiophCompression.evalAtZZ floorThirdPoly (pairVec (fun _ => 1) (fun _ => 0)) (fun _ => -1) = 0 := by
  sorry

/- TRUTH CHECK (leg 1 M7/M8, leg 2 M7/M8).  By B1 the function would be Q or H.  Q: values 0,0,0,1 at 0,1,2,3 contradict a
   quadratic.  H (n = 1, p₀ odd): pick x ∈ {0,1} with p₀x + c even; then x + 6 too, and 2(F(x+6) − F(x)) = 6p₀ = 4. -/
/-- **B4.**  `floorThird` has no zero-witness single quadratic presentation.  Unconditional. -/
theorem floorThird_not_zeroWitness : ¬ SingleQuadraticWithWitnessesZZ floorThird 0 := by
  sorry

/- TRUTH CHECK.  B3 and B4; the minimum is over this fixed format (one equation, degree ≤ 2, integer witnesses). -/
/-- **B3 + B4.**  In the single-quadratic format `floorThird` needs exactly one witness. -/
theorem floorThird_min_witnesses :
    SingleQuadraticWithWitnessesZZ floorThird 1 ∧ ¬ SingleQuadraticWithWitnessesZZ floorThird 0 := by
  sorry

end DiophCompression.ResearchUpgrade
