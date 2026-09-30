# DEPENDENCY_CLOSURE_ALL_R — the root of Quadratic Witness Inertia and its two closures

Root module: `DiophCompression/QuadraticWitnessInertiaCore.lean`
(`lake build DiophCompression.QuadraticWitnessInertiaCore`).
Exports exactly three theorems:

- `quadraticProjectionDichotomyZ_all : ∀ r, QuadraticProjectionDichotomyZ r`
- `quadraticWitnessInertiaZ : ∀ r, graphCapacityZ r 2 = 2`
- `graphAchievableZ_degree_two_iff : ∀ r n, GraphAchievableZ n r 2 ↔ n ≤ 2`

Two closures are reported, each with its script, its exact module list, and
its output log in the package. They answer different questions and both
numbers are quoted.

## Static import closure: 64 local modules, 11,020 lines

Definition: follow every `import DiophCompression.*` / `import MPUP.*` line
transitively from the root module (root included). This is the set of local
modules that `lake build DiophCompression.QuadraticWitnessInertiaCore`
compiles. Script: `scripts/static_closure.py`; log:
`certificates/static_closure.log` (anchors `STATIC_CLOSURE_MODULES=64 DC=61
MPUP=3`, `STATIC_CLOSURE_LOC=11020`, module list on the `SMOD` lines). Lines
are counted as the sum over modules of `len(text.splitlines())`, comments
and blank lines included.

## Kernel constant-dependency closure: 50 local modules

Definition: starting from the three exported constants, walk
`Expr.getUsedConstants` over the TYPE and the VALUE of every reached
constant (opaque bodies followed), and record the local module of each
reached constant. This is the set of local modules whose declarations the
kernel proofs of the three theorems actually reference. Script:
`scripts/kernel_closure.lean` (`lake env lean`); log:
`certificates/kernel_closure.log` (anchors `KERNEL_CLOSURE_MODULES=50 DC=48
MPUP=2`, list on the `KMOD` lines). The static closure contains the kernel
closure (`KERNEL_SUBSET_STATIC=YES`); the 14 static-only modules are
reached through `import` edges alone and are listed on the `STATIC_ONLY`
lines of the static log (they are: the root module itself, which only
re-exports; two r = 1 modules; `SemanticQuadraticSingular/DefsSingular`; nine
r = 2 modules of `SemanticQuadraticTwoWitness/`; and `MPUP/Task1`).

## By layer

| layer | static modules | kernel modules | LoC |
|---|---:|---:|---:|
| `DiophCompression/` (root level) | 14 | 13 | 1,823 |
| `DiophCompression/SemanticQuadratic/` | 11 | 9 | 1,250 |
| `DiophCompression/SemanticQuadraticGeneral/` | 3 | 3 | 486 |
| `DiophCompression/SemanticQuadraticMatrix/` | 5 | 5 | 1,509 |
| `DiophCompression/SemanticQuadraticSingular/` | 10 | 9 | 2,382 |
| `DiophCompression/SemanticQuadraticThreeWitness/` | 1 | 1 | 205 |
| `DiophCompression/SemanticQuadraticTwoWitness/` | 17 | 8 | 2,243 |
| `MPUP/` | 3 | 2 | 1,122 |
| **total** | **64** | **50** | **11,020** |

(Row counts are computed from the module lists in the two logs; the table
sums to the quoted totals.)

## Absences asserted by both scripts

`DiophCompression.TreeCoding`, `DiophCompression.UnifiedLower`,
`DiophCompression.QuadraticUniversalityConditional` and
`DiophCompression.UniversalSpectrumLower` are in neither closure; both
scripts print `..._ABSENT <module>=YES` for each and exit nonzero
otherwise. The universality corollaries
(`SemanticQuadraticSingular/QuadraticUniversalityCorollaries.lean`) and the
conditional universality layer are outside the root's closure; the
sixteen-theorem export of the release adds exactly those two files.

## Disclosed non-minimalities

1. **MPUP layer**: `MPUP.Spec` is the base definition module (imported by
   `DiophCompression/Definitions.lean`); `MPUP.Obstruction` carries the
   counting obstruction used by the capacity machinery. Both are in the
   kernel closure; `MPUP.Task1` is static-only.
2. **Static-only r = 2 modules**: the r = 2 rank leaves and the sign
   normalisation are imported by the general-r assembly but not referenced
   by the exported proofs; dropping them from the static closure would
   require re-routing imports, and nothing in the paper depends on doing so.

## Negative controls

`scripts/static_closure.py --negative-control` traverses from a scratch root
that imports `TreeCoding` and must report it present
(`NEGATIVE_CONTROL_TREECODING_DETECTED=YES`). The kernel script aborts with
`ROOT_MISSING` if any of the three exported constants is absent from the
environment.
