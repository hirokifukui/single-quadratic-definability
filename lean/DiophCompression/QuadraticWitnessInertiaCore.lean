import DiophCompression.SemanticQuadraticSingular.SingularAssembly

/-! # Quadratic Witness Inertia — minimal root (GPT r11 mandatory C)

Building this module (`lake build DiophCompression.QuadraticWitnessInertiaCore`)
compiles exactly the import closure needed for the three all-r theorems:

* `quadraticProjectionDichotomyZ_all : ∀ r, QuadraticProjectionDichotomyZ r`
* `quadraticWitnessInertiaZ : ∀ r, graphCapacityZ r 2 = 2`
* `graphAchievableZ_degree_two_iff : ∀ r n, GraphAchievableZ n r 2 ↔ n ≤ 2`

and nothing else from the package. Closure facts (recount 2026-08-29, s15):
* static import closure = 64 local modules (61 under `DiophCompression/` + 3 under `MPUP/`:
  `Spec` (frozen statement layer), `Obstruction`, `Task1`), about 11,000 lines;
* `TreeCoding` and `UnifiedLower` are NOT in the closure (chain lower bounds moved to
  `CapacityChainLower.lean`; the lower bound G_ℤ(r,2) ≥ 2 in `ProjectionDichotomy.lean` now comes from
  the zero-witness pairing polynomial and witness monotonicity);
* the universality corollaries (`SemanticQuadraticSingular/QuadraticUniversalityCorollaries.lean`)
  and the conditional universality layer are not in the closure, while the graph→universality
  counting foundations the capacity machinery uses (`BoundaryCases`, `Sandwich`,
  `GraphToUniversalityN`, `NatGuardZ`) remain inside it;
* kernel-level (constant-dependency) closure of the three theorems = 50 local modules; the
  remaining imported modules are reached only through `import` edges.
The closure is documented in `manuscript/DEPENDENCY_CLOSURE_ALL_R.md`. -/

namespace DiophCompression
export SemanticQuadraticSingular
  (quadraticProjectionDichotomyZ_all quadraticWitnessInertiaZ
   graphAchievableZ_degree_two_iff)
end DiophCompression
