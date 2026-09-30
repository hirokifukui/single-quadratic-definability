import ResearchUpgrade
import DiophCompression.QuadraticPPSeparation
import DiophCompression.AtomicDegreeRank
import DiophCompression.Folding
import DiophCompression.OneSorted
import DiophCompression.OneSortedPPCoding
import DiophCompression.OneSortedFragments
import DiophCompression.OneSortedPPFolding
import DiophCompression.APALLogicCore
import DiophCompression.FiniteFiberGrowth
import DiophCompression.PolynomialGraphs
import DiophCompression.SkolemReduction
import DiophCompression.FiniteFiberCardinality
import DiophCompression.FragmentLattice
import DiophCompression.MultivariatePolynomialGraphs
import DiophCompression.IntPrimrec
import DiophCompression.ComputabilityFragments
import DiophCompression.ComputableFunctions
import DiophCompression.HaltingTransport
import DiophCompression.UnaryDiagonal
import DiophCompression.QuadraticCodes
import DiophCompression.GlobalQuadraticCode
import DiophCompression.EffectiveDiagonal
import DiophCompression.DPRMTransport
import DiophCompression.InfiniteFiberCertificate
import DiophCompression.StructuredCertificates
import DiophCompression.OutputNegation
import DiophCompression.LeafExtraction
import DiophCompression.SummitTarget
import DiophCompression.BranchExhaustion
import DiophCompression.GSInputCompiler
import DiophCompression.SummitReduction
import DiophCompression.SemanticQuadratic.LeafDataD3D6
import DiophCompression.PeriodicProgressionCore
import DiophCompression.StructuredFamilyCore
import DiophCompression.PellOrbitCore
import DiophCompression.SemanticQuadratic.PellFiberOrbit
import DiophCompression.SemanticQuadratic.PellOrbitOfXPos
import DiophCompression.SemanticQuadraticTwoWitness.RankOneCoupledData
import DiophCompression.SemanticQuadratic.QuadraticFamilyData
import DiophCompression.SemanticQuadratic.OneWitnessFamilyData
import DiophCompression.SemanticQuadratic.FiberDichotomyData
import DiophCompression.SemanticQuadratic.PellDichotomyData
import DiophCompression.SemanticQuadratic.DegenerateDichotomyData
import DiophCompression.SemanticQuadraticTwoWitness.RankOneUncoupledData
import DiophCompression.SemanticQuadraticTwoWitness.RankOneNormalData
import DiophCompression.SemanticQuadraticMatrix.FullRankAssemblyData
import DiophCompression.SemanticQuadraticSingular.SingularDataCore
import DiophCompression.SemanticQuadraticGeneral.TopDichotomyData
import DiophCompression.SemanticQuadraticMatrix.QuadraticFamilyA2
import DiophCompression.PeriodicProgressionData
import DiophCompression.ArityZeroFragments
import DiophCompression.FunctionPhaseByArity
import DiophCompression.FunctionPhaseByArityNN
import DiophCompression.RelationPhaseAllPositiveArityClassical
import DiophCompression.APALStructuralTheoryCore
import DiophCompression.SummitClosure
import DiophCompression.GSCompilerComputable
import DiophCompression.SummitInstances
import MPUP.Quantitative
import MPUP.WeightedBound
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.SemanticQuadraticSingular.QuadraticUniversalityCorollaries
import DiophCompression.SemanticQuadraticSingular.CorollariesAllR
import DiophCompression.QuadraticUniversalityConditional

/-!
  scripts/PaperClaimTypeReport.lean — Gate 13 A04 (s39, 2026-09-06): the Lean TYPE FINGERPRINT of every root.

  For every `#print axioms` root of scripts/FinalAxiomReport.lean, and for every extra declaration listed in
  scripts/paper_claim_extra_roots.txt (the `def`s that paper Definitions cite), this script prints one TSV row:
      fully_qualified_name  <TAB>  kind  <TAB>  n_binders  <TAB>  normalized_pretty_type  <TAB>  axioms
  where normalized_pretty_type is the elaborated type pretty-printed with `Meta.ppExpr` at unbounded width, runs of
  whitespace collapsed to one space.  The SHA-256 of that string is computed downstream by tools/paper_claim_types.py
  (Lean core has no SHA-256); the string itself ships, so the hash is reproducible from this file alone.
  Planted controls: two theorems whose types differ only in an implicit degree (4 vs d) MUST print different
  normalized types; a theorem and its exact alias MUST print the same.  The script aborts on CONTROL_FAIL.
  Summary lines: TYPE_ROWS=, TYPE_CONTROLS=, TYPE_MISSING= (names in the lists that the environment lacks).
-/

open Lean Meta

namespace PaperClaimTypeReport

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- collapse runs of whitespace to one space and strip the ends (char fold; String API-version independent) -/
def collapse (s : String) : String :=
  let (out, _) := s.foldl (fun (acc : String × Bool) c =>
    if isWs c then (acc.1, true)
    else ((if acc.2 && !acc.1.isEmpty then acc.1.push ' ' else acc.1).push c, false)) ("", false)
  out

def ppType (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let fmt ← withOptions (fun o => (o.setBool `pp.fullNames true)) (ppExpr ci.type)
  return collapse (fmt.pretty (width := 100000))

def kindOf (n : Name) : MetaM String := do
  match (← getEnv).find? n with
  | some (.thmInfo _) => pure "theorem"
  | some (.defnInfo _) => pure "def"
  | some (.axiomInfo _) => pure "axiom"
  | some (.opaqueInfo _) => pure "opaque"
  | some _ => pure "other"
  | none => pure "MISSING"

def nBinders (n : Name) : MetaM Nat := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => pure xs.size

def row (n : Name) : MetaM (Option String) := do
  if !(← getEnv).contains n then return none
  let k ← kindOf n
  let b ← nBinders n
  let t ← ppType n
  let ax ← collectAxioms n
  return some s!"{n}\t{k}\t{b}\t{t}\t{",".intercalate (ax.toList.map toString)}"

/-! ### Planted controls -/
theorem control_fixed_degree {k : ℕ} {A : Set (Fin k → ℤ)} (h : DiophCompression.WithinSingleEquationZZ 4 A) :
    REPred fun a => a ∈ A := DiophCompression.singleEquation_relation_re h
theorem control_generic_degree {d k : ℕ} {A : Set (Fin k → ℤ)} (h : DiophCompression.WithinSingleEquationZZ d A) :
    REPred fun a => a ∈ A := DiophCompression.singleEquation_relation_re h
theorem control_alias {k : ℕ} {A : Set (Fin k → ℤ)} (h : DiophCompression.WithinSingleEquationZZ 4 A) :
    REPred fun a => a ∈ A := DiophCompression.singleQuartic_relation_re h

/-! ### Planted type-level mutation controls (Gate-13 §20, s39).  Each `def … : Prop` is the MUTATED
statement of a registered root; its pretty-printed VALUE must differ from the root's pretty-printed TYPE.
One exact copy must print the same.  These are the three §20 mutations that cannot be planted without a
Lean rebuild (implicit hypothesis dropped, external hypothesis moved to the conclusion, iff weakened). -/
def mut_iff_weakened : Prop :=
  DiophCompression.UniformQuadraticSolvabilityOnCodes → DiophCompression.UniformQuadraticSolvabilityDecidableZZ
def mut_hypothesis_dropped : Prop :=
  ∀ {n m : ℕ} (f : (Fin n → ℤ) → Fin m → ℤ), DiophCompression.SingleQuadraticDefinableFunctionZZ f → n ≤ 2 * m
def mut_hypothesis_to_conclusion : Prop :=
  ∀ (k : ℕ), DiophCompression.SingleEqFragmentZZ 2 k ⊆ DiophCompression.RecFragmentZZ k ∨
    ¬ DiophCompression.QuadraticSolvabilityDecidableZZ
def exact_iff : Prop :=
  DiophCompression.UniformQuadraticSolvabilityOnCodes ↔ DiophCompression.UniformQuadraticSolvabilityDecidableZZ

def ppValue (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  match ci.value? with
  | some v =>
    let fmt ← withOptions (fun o => (o.setBool `pp.fullNames true)) (ppExpr v)
    return collapse (fmt.pretty (width := 100000))
  | none => throwError s!"{n} has no value"

def mutControls : List (Name × Name × Bool × String) :=
  [(`PaperClaimTypeReport.mut_iff_weakened, `DiophCompression.uniformCodeGS_iff, false, "iff weakened to an implication"),
   (`PaperClaimTypeReport.mut_hypothesis_dropped, `DiophCompression.singleQuadratic_injective_dimension_bound, false, "Function.Injective hypothesis dropped"),
   (`PaperClaimTypeReport.mut_hypothesis_to_conclusion, `DiophCompression.singleEqFragmentZZ_two_subset_recFragmentZZ, false, "external hypothesis moved to the conclusion"),
   (`PaperClaimTypeReport.exact_iff, `DiophCompression.uniformCodeGS_iff, true, "exact copy prints the same")]

def readNames (path : String) (prefix_ : String) : IO (List Name) := do
  if !(← System.FilePath.pathExists path) then return []
  let s ← IO.FS.readFile path
  return (s.splitOn "\n").filterMap fun l =>
    let l := collapse l
    if l.isEmpty || l.startsWith "--" || l.startsWith "#" && prefix_ != "#print axioms " then none
    else if prefix_.isEmpty then some l.toName
    else if l.startsWith prefix_ then some (collapse (l.drop prefix_.length).toString).toName else none

def main : MetaM Unit := do
  -- controls
  let a ← ppType `PaperClaimTypeReport.control_fixed_degree
  let b ← ppType `PaperClaimTypeReport.control_generic_degree
  let c ← ppType `PaperClaimTypeReport.control_alias
  let d ← ppType `DiophCompression.singleQuartic_relation_re
  let e ← ppType `DiophCompression.singleEquation_relation_re
  let mut okc := 0
  if a != b then okc := okc + 1 else IO.println s!"CONTROL_FAIL\tfixed vs generic degree printed equal\t{a}"
  if a == c then okc := okc + 1 else IO.println s!"CONTROL_FAIL\talias printed differently\t{a}\t{c}"
  if d != e then okc := okc + 1 else IO.println s!"CONTROL_FAIL\tsingleQuartic vs singleEquation printed equal"
  if a == d then okc := okc + 1 else IO.println s!"CONTROL_FAIL\tcontrol_fixed_degree vs singleQuartic_relation_re differ\t{a}\t{d}"
  IO.println s!"TYPE_CONTROLS={okc}/4"
  if okc != 4 then throwError "CONTROL_FAIL"
  let mut okm := 0
  for (mutN, rootN, wantEq, desc) in mutControls do
    let v ← ppValue mutN
    let t ← ppType rootN
    if (v == t) == wantEq then okm := okm + 1
    else IO.println s!"MUT_CONTROL_FAIL\t{desc}\t{v}\t{t}"
  IO.println s!"TYPE_MUT_CONTROLS={okm}/{mutControls.length}"
  if okm != mutControls.length then throwError "MUT_CONTROL_FAIL"
  let rs ← readNames "scripts/FinalAxiomReport.lean" "#print axioms "
  let extra ← readNames "scripts/paper_claim_extra_roots.txt" ""
  IO.println "fully_qualified_name\tkind\tn_binders\tnormalized_pretty_type\taxioms"
  let mut n := 0; let mut missing : List Name := []
  for x in rs ++ extra do
    match ← row x with
    | some r => IO.println r; n := n + 1
    | none => missing := missing ++ [x]
  IO.println s!"TYPE_ROWS={n}"
  IO.println s!"TYPE_MISSING={missing.length}{if missing.isEmpty then "" else "\t" ++ ",".intercalate (missing.map toString)}"

end PaperClaimTypeReport

#eval PaperClaimTypeReport.main
