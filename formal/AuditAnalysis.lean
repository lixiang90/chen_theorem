import ChenTheorem.Analysis.PrimeNumberTheorem
import ChenTheorem.Analysis.PNT.PerronFormula
import ChenTheorem.Analysis.PNT.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime
import ChenTheorem.Analysis.MertensProduct
import Lean.Util.CollectAxioms

/- Kernel-level regression check for the locally included analytic inputs.
Run: lake env lean AuditAnalysis.lean -/
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``MediumPNT, ``Chen.chebyshevPsi_isEquivalent,
      ``RS_prime.mertens_second_theorem,
      ``Perron.formulaLtOne, ``Perron.formulaGtOne,
      ``Mertens.prod_one_minus_div_prime_eq, ``Mertens.E₃.bound'',
      ``Chen.primeEulerProduct_mul_log_tendsto] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax => !allowed.contains ax
    if extra.isEmpty then
      Lean.logInfo m!"PASS {name}: {axioms}"
    else
      Lean.logError m!"FAIL {name}: unproved inputs {extra}"
