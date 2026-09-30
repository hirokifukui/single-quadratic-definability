import DiophCompression.QuadraticWitnessInertiaCore
/-! kernel_closure.lean (s16; formalizes the s15 draft). Kernel-level constant-dependency
closure of the three exported all-r theorems: walks `getUsedConstants` over TYPE and
VALUE (allowOpaque := true, so opaque bodies are followed) from the roots, then maps
each reached constant to its module; reports the local (DiophCompression./MPUP.)
modules, sorted, with grep-able anchors. Companion: scripts/static_closure.py
(import-graph closure). -/
open Lean

partial def collect (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | c :: rest, acc =>
    if acc.contains c then collect env rest acc else
    match env.checked.get.find? c with
    | none => collect env rest acc
    | some ci =>
      let used := (ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]).toList
      collect env (used ++ rest) (acc.insert c)

#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let roots := [``DiophCompression.SemanticQuadraticSingular.quadraticProjectionDichotomyZ_all,
                ``DiophCompression.SemanticQuadraticSingular.quadraticWitnessInertiaZ,
                ``DiophCompression.SemanticQuadraticSingular.graphAchievableZ_degree_two_iff]
  for r in roots do
    if (env.find? r).isNone then throwError "ROOT_MISSING {r}"
  let s := collect env roots {}
  let mut mods : NameSet := {}
  let mut nLocalConsts := 0
  for c in s.toList do
    if let some idx := env.getModuleIdxFor? c then
      let m := env.header.moduleNames[idx.toNat]!
      if (`DiophCompression).isPrefixOf m || (`MPUP).isPrefixOf m then
        mods := mods.insert m; nLocalConsts := nLocalConsts + 1
  let ml := (mods.toList.map toString).toArray.qsort (· < ·)
  let dc := ml.filter (·.startsWith "DiophCompression.")
  let mp := ml.filter (·.startsWith "MPUP.")
  logInfo m!"KERNEL_CLOSURE_ROOTS={roots.length}"
  logInfo m!"KERNEL_CLOSURE_CONSTANTS_TOTAL={s.size}"
  logInfo m!"KERNEL_CLOSURE_CONSTANTS_LOCAL={nLocalConsts}"
  logInfo m!"KERNEL_CLOSURE_MODULES={ml.size} DC={dc.size} MPUP={mp.size}"
  for m in ml do logInfo m!"KMOD {m}"
  let forbidden := ["DiophCompression.TreeCoding", "DiophCompression.UnifiedLower",
                    "DiophCompression.QuadraticUniversalityConditional", "DiophCompression.UniversalSpectrumLower"]
  for f in forbidden do
    logInfo m!"KERNEL_ABSENT {f}={if ml.contains f then "NO" else "YES"}"
