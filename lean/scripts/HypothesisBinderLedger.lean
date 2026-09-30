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
import MPUP.Quantitative
-- s34: FinalAxiomReport gained the WeightedBound roots; this ledger reads that file's root
-- list but has its own import set, so registering there without importing here made every new root
-- an unknown constant.  The two mechanisms must move together.
import MPUP.WeightedBound
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.SemanticQuadraticSingular.QuadraticUniversalityCorollaries
import DiophCompression.SemanticQuadraticSingular.CorollariesAllR
import DiophCompression.QuadraticUniversalityConditional
import DiophCompression.SummitClosure
import DiophCompression.GSCompilerComputable
import DiophCompression.SummitInstances
-- s50: r40's THIRD library.  scripts/PaperClaimTypeReport.lean imports it and takes its extra roots
-- from scripts/paper_claim_extra_roots.txt; this ledger must import it too, or every ResearchUpgrade
-- root read from that file is an unknown constant.  Second occurrence of the s34 lesson above.
import ResearchUpgrade

/-!
  scripts/HypothesisBinderLedger.lean — Gate 4 必須C (s27, 2026-09-01): the BINDER-LEVEL trust-boundary ledger.
  For every `#print axioms` root of scripts/FinalAxiomReport.lean, the theorem TYPE is analysed with the Lean Meta API
  (`forallTelescope`): every leading binder is classified explicit / implicit / strict-implicit / instance, and its type is
  searched for the registered external Props — directly (`Expr.getUsedConstants`) and through definitional wrapping
  (transitive unfolding of `def`s in the DiophCompression/MPUP namespaces). Occurrences in the CONCLUSION are reported
  separately and do NOT make a root conditional. The axiom footprint of each root is collected by `collectAxioms`.
  Planted controls (positive and negative) run first; the script aborts with CONTROL_FAIL if any expectation is missed.
  Output (stdout): TSV with header, then summary lines `BINDER_ROOTS=`, `BINDER_UNCONDITIONAL=`, `EXPLICIT_<Prop>=`,
  `IMPLICIT_ANY=`, `WRAPPED_ANY=`, `CONCLUSION_ONLY=`, `NONSTD_AXIOMS=`, `UNKNOWN_EXTERNAL_BINDERS=` (a Prop-typed binder
  whose head constant is in our namespaces but not in the registry — the unknown-external-Prop gate).
  Run: `lake env lean scripts/HypothesisBinderLedger.lean > certificates/hypothesis_binder_ledger_<tag>.tsv`.
  The Python occurrence ledger (scripts/conservative_hypothesis_occurrence_ledger.py) remains as the conservative check.
-/

open Lean Meta

namespace HypothesisBinderLedger

/-- The external-Prop registry (the trust boundary of the paper and its derived forms). -/
def registry : List Name :=
  [`DiophCompression.GlobalQuadraticSolvabilityDecidable,
   `DiophCompression.UniformQuadraticSolvabilityOnCodes,
   `DiophCompression.UniformQuadraticSolvabilityDecidableZZ,
   `DiophCompression.QuadraticSolvabilityDecidableZZ,
   `DiophCompression.DPRM_NN,
   `DiophCompression.DPRM_ZZ,
   `DiophCompression.PellClassFiniteness,
   -- r13-era conditional forms (QuadraticUniversalityConditional.lean), found by the unknown-external gate in s27:
   `DiophCompression.QuadraticSolvabilityDecidableZ,
   `DiophCompression.QuadraticSolvabilityDecidableN,
   `DiophCompression.HardDiophantineSetExists,
   -- s59 (GATE29 #129): the analytic input of Appendix A, an explicit hypothesis, never an axiom.
   `DiophCompression.ResearchUpgrade.TCERBridge.TernaryCosetEventualRepresentation]

def registryShort (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

def inOurNamespaces (n : Name) : Bool :=
  (`DiophCompression).isPrefixOf n || (`MPUP).isPrefixOf n || (`HypothesisBinderLedger).isPrefixOf n

/-- Transitive constant closure through `def` values, restricted to our namespaces (bounded). -/
partial def closure (env : Environment) (start : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := start.toList
  let mut fuel := 20000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      if inOurNamespaces c then
        match env.find? c with
        | some (.defnInfo d) => todo := d.value.getUsedConstants.toList ++ d.type.getUsedConstants.toList ++ todo
        | some ci => todo := ci.type.getUsedConstants.toList ++ todo
        | none => pure ()
  return seen

def registryIn (s : NameSet) : List Name := registry.filter s.contains

structure Row where
  name : Name
  explicitDirect : List Name := []
  implicitDirect : List Name := []   -- implicit + strict implicit
  instDirect : List Name := []
  wrapped : List Name := []          -- externals reached only through definitional unfolding of a binder type
  unknownExternal : List Name := []  -- Prop-typed binders with an unregistered head constant in our namespaces
  conclusion : List Name := []       -- direct or wrapped occurrences in the conclusion
  axioms : List Name := []

def isPropType (t : Expr) : MetaM Bool := do
  let s ← inferType t
  return s.isProp

def analyze (n : Name) : MetaM Row := do
  let env ← getEnv
  let ci ← getConstInfo n
  let ax ← collectAxioms n
  forallTelescope ci.type fun xs concl => do
    let mut r : Row := { name := n, axioms := ax.toList }
    for x in xs do
      let d ← x.fvarId!.getDecl
      let t := d.type
      let direct := registryIn (NameSet.ofList t.getUsedConstants.toList)
      let cl := closure env t.getUsedConstants
      let wrappedOnly := (registryIn cl).filter (fun c => !direct.contains c)
      r := { r with wrapped := r.wrapped ++ wrappedOnly }
      match d.binderInfo with
      | .default => r := { r with explicitDirect := r.explicitDirect ++ direct }
      | .instImplicit => r := { r with instDirect := r.instDirect ++ direct }
      | _ => r := { r with implicitDirect := r.implicitDirect ++ direct }
      -- unknown-external gate: a Prop binder headed by an unregistered constant of ours, with no registered external inside
      -- (closed Props only: a binder type with free variables is a predicate on earlier binders, not a hypothesis about the world)
      if (← isPropType t) && !t.hasFVar then
        match t.getAppFn with
        | .const h _ =>
          if inOurNamespaces h && !registry.contains h && direct.isEmpty && wrappedOnly.isEmpty then
            -- only flag if the head is a `def`/`abbrev` Prop (a hypothesis-like predicate), not a theorem/structure projection
            match env.find? h with
            | some (.defnInfo _) => r := { r with unknownExternal := r.unknownExternal ++ [h] }
            | _ => pure ()
        | _ => pure ()
    let cdirect := registryIn (NameSet.ofList concl.getUsedConstants.toList)
    let ccl := registryIn (closure env concl.getUsedConstants)
    r := { r with conclusion := (cdirect ++ ccl.filter (fun c => !cdirect.contains c)) }
    return r

def std3 : List Name := [`propext, `Classical.choice, `Quot.sound]

def Row.conditional (r : Row) : Bool :=
  !(r.explicitDirect.isEmpty && r.implicitDirect.isEmpty && r.instDirect.isEmpty && r.wrapped.isEmpty)

def fmt (l : List Name) : String := if l.isEmpty then "-" else String.intercalate "," (l.map registryShort)

def Row.tsv (r : Row) : String :=
  s!"{r.name}\t{fmt r.explicitDirect}\t{fmt r.implicitDirect}\t{fmt r.instDirect}\t{fmt r.wrapped}\t{fmt r.unknownExternal}\t{fmt r.conclusion}\t{if r.conditional then "CONDITIONAL" else "UNCONDITIONAL"}\t{String.intercalate "," (r.axioms.map toString)}"

/-! ### Planted controls -/
def wrappedExternal : Prop := DiophCompression.DPRM_ZZ ∧ True
def unregisteredPredicate : Prop := ∀ n : ℕ, n = n
theorem control_explicit (h : DiophCompression.DPRM_NN) : True := trivial
theorem control_implicit {h : DiophCompression.DPRM_ZZ} : True := trivial
theorem control_wrapped (h : wrappedExternal) : True := trivial
theorem control_conclusion_only : True ∨ DiophCompression.DPRM_ZZ := Or.inl trivial
theorem control_iff : DiophCompression.DPRM_ZZ ↔ DiophCompression.DPRM_ZZ := Iff.rfl
theorem control_unknown (h : unregisteredPredicate) : True := trivial
theorem control_clean : True := trivial

def controls : List (Name × (Row → Bool) × String) :=
  [(`HypothesisBinderLedger.control_explicit, fun r => r.explicitDirect == [`DiophCompression.DPRM_NN] && r.conditional, "explicit DPRM_NN → conditional"),
   (`HypothesisBinderLedger.control_implicit, fun r => r.implicitDirect == [`DiophCompression.DPRM_ZZ] && r.explicitDirect.isEmpty && r.conditional, "implicit DPRM_ZZ → conditional"),
   (`HypothesisBinderLedger.control_wrapped, fun r => r.wrapped == [`DiophCompression.DPRM_ZZ] && r.explicitDirect.isEmpty && r.conditional, "wrapped DPRM_ZZ → conditional (via unfolding)"),
   (`HypothesisBinderLedger.control_conclusion_only, fun r => r.conclusion == [`DiophCompression.DPRM_ZZ] && !r.conditional, "conclusion-only → unconditional"),
   (`HypothesisBinderLedger.control_iff, fun r => r.conclusion == [`DiophCompression.DPRM_ZZ] && !r.conditional, "iff both sides → unconditional"),
   (`HypothesisBinderLedger.control_unknown, fun r => r.unknownExternal == [`HypothesisBinderLedger.unregisteredPredicate] && !r.conditional, "unregistered Prop binder → flagged"),
   (`HypothesisBinderLedger.control_clean, fun r => !r.conditional && r.conclusion.isEmpty && r.unknownExternal.isEmpty, "clean → unconditional")]

def roots : IO (List Name) := do
  let s <- IO.FS.readFile "scripts/FinalAxiomReport.lean"
  let ls := s.splitOn "\n"
  let base := ls.filterMap fun l =>
    if l.startsWith "#print axioms " then some ((l.drop "#print axioms ".length).trim.toName) else none
  -- s50: ONE root source for the two mechanisms.  The r40 paper-claim roots of the third library live in
  -- scripts/paper_claim_extra_roots.txt, which scripts/PaperClaimTypeReport.lean already consumes; reading
  -- it here makes it impossible for a root to enter the type report while silently missing from this
  -- binder ledger (which would print n/a in the external_binders column of a THEOREM).
  let e <- IO.FS.readFile "scripts/paper_claim_extra_roots.txt"
  let extra := (e.splitOn "\n").filterMap fun l =>
    let x := l.trim
    if x.isEmpty || x.startsWith "--" then none else some x.toName
  return base ++ extra.filter (fun n => !base.contains n)

def main : MetaM Unit := do
  -- controls first
  let mut okc := 0
  for (n, chk, desc) in controls do
    let r ← analyze n
    if chk r then okc := okc + 1
    else IO.println s!"CONTROL_FAIL\t{n}\t{desc}\t{r.tsv}"
  IO.println s!"CONTROLS={okc}/{controls.length}"
  if okc != controls.length then throwError "CONTROL_FAIL"
  let rs ← roots
  IO.println "root\texplicit\timplicit\tinstance\twrapped\tunknown_external\tconclusion\tstatus\taxioms"
  let mut nUncond := 0; let mut nImpl := 0; let mut nWrap := 0; let mut nConclOnly := 0; let mut nNonStd := 0; let mut nUnknown := 0
  let mut perExplicit : List (Name × Nat) := registry.map (·, 0)
  for n in rs do
    let r ← analyze n
    IO.println r.tsv
    if !r.conditional then nUncond := nUncond + 1
    if !r.conditional && !r.conclusion.isEmpty then nConclOnly := nConclOnly + 1
    if !r.implicitDirect.isEmpty then nImpl := nImpl + 1
    if !r.wrapped.isEmpty then nWrap := nWrap + 1
    if !r.unknownExternal.isEmpty then nUnknown := nUnknown + 1
    if r.axioms.any (fun a => !std3.contains a) then nNonStd := nNonStd + 1
    perExplicit := perExplicit.map fun (p, c) => (p, if r.explicitDirect.contains p then c + 1 else c)
  IO.println s!"BINDER_ROOTS={rs.length}"
  IO.println s!"BINDER_UNCONDITIONAL={nUncond}"
  for (p, c) in perExplicit do IO.println s!"EXPLICIT_{registryShort p}={c}"
  IO.println s!"IMPLICIT_ANY={nImpl}"
  IO.println s!"WRAPPED_ANY={nWrap}"
  IO.println s!"CONCLUSION_ONLY={nConclOnly}"
  IO.println s!"UNKNOWN_EXTERNAL_BINDERS={nUnknown}"
  IO.println s!"NONSTD_AXIOMS={nNonStd}"

end HypothesisBinderLedger

#eval HypothesisBinderLedger.main
