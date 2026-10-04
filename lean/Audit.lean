import SparseSGD
import Lean.Util.CollectAxioms

/-! Audit every exported project theorem, including its transitive dependencies. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut constants : Nat := 0
  for (name, info) in env.constants.toList do
    let project := match env.getModuleIdxFor? name with
      | some idx => (`SparseSGD).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => (`SparseSGD).isPrefixOf name
    if project then
      constants := constants + 1
      if info.isTheorem then count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unauthorized axiom {ax} in {name}"
  logInfo m!"Audited {constants} SparseSGD declarations ({count} theorems); only standard Lean axioms."
