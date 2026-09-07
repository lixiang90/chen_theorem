import ChenTheorem
import Lean.Util.CollectAxioms

/- Audit every project declaration imported by the public entry point, including
private supporting declarations and locally included third-party proofs.
Run: lake env lean AuditAll.lean -/
run_cmd do
  let env ← Lean.getEnv
  let modules := env.header.moduleNames.filter ((`ChenTheorem).isPrefixOf ·)
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut failed : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`ChenTheorem).isPrefixOf env.header.moduleNames[idx]! then
        checked := checked + 1
        let axioms ← Lean.collectAxioms name
        let extra := axioms.filter fun ax => !allowed.contains ax
        unless extra.isEmpty do
          failed := failed + 1
          Lean.logError m!"FAIL {name}: unproved inputs {extra}"
  if checked == 0 then
    Lean.logError "FAIL: no project declarations were audited"
  else if failed == 0 then
    Lean.logInfo m!"PASS: all {checked} declarations across {modules.size} project modules use only standard axioms"
  else
    Lean.logError m!"FAIL: {failed} of {checked} project declarations have unproved inputs"
