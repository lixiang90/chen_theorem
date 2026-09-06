import ChenTheorem
import Lean.Util.CollectAxioms

/- Completion gate. A successful build alone does not establish completion.
Run: lake env lean Audit.lean
This command must fail until all remaining mathematical inputs are proved. -/
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``Chen.LinearSieve.sum_divisors_multSum,
      ``Chen.LinearSieve.sum_le_siftedSum_of_lowerMoebius,
      ``Chen.LinearSieve.mainSum_sub_errSum_le_siftedSum,
      ``Chen.LinearSieve.errSum_le_sum_of_level,
      ``Chen.LinearSieve.exists_rosser_sieve_weights,
      ``Chen.LinearSieve.rosser_sieve_bounds_of_remainders,
      ``Chen.chen_theorem, ``Chen.chen_twin,
      ``Chen.chenCount_lower, ``Chen.chenCountShift_lower,
      ``Chen.BombieriVinogradov.bombieriVinogradov] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax => !allowed.contains ax
    if extra.isEmpty then
      Lean.logInfo m!"PASS {name}: {axioms}"
    else
      Lean.logError m!"FAIL {name}: unproved inputs {extra}"
