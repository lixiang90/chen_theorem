import ChenTheorem.Lemma6.LFunctionDiskLogDerivative
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
      ``Chen.primeEulerProduct_mul_log_tendsto,
      ``Chen.differentiableAt_of_cexp,
      ``Chen.exists_normalized_analyticLog_on_ball,
      ``Chen.deriv_analyticLog_eq_logDeriv,
      ``Chen.norm_analyticLog_le_on_inner_ball,
      ``Chen.norm_logDeriv_le_of_nonvanishing_ball,
      ``Chen.tsum_nat_rpow_neg_le,
      ``Chen.norm_LSeries_le_of_unit_bound,
      ``Chen.norm_LFunction_euler_upper,
      ``Chen.norm_LFunction_euler_lower,
      ``Chen.norm_LFunction_logDeriv_le_of_nonvanishing_ball] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax => !allowed.contains ax
    if extra.isEmpty then
      Lean.logInfo m!"PASS {name}: {axioms}"
    else
      Lean.logError m!"FAIL {name}: unproved inputs {extra}"
