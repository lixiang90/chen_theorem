import ChenTheorem.Lemma6.ZeroFreeRegionAssembly
import ChenTheorem.Analysis.CompactZeroFreeStrip
import ChenTheorem.Lemma6.DirichletLogDerivativePositivity
import ChenTheorem.Lemma6.CompactDirichletFamily
import ChenTheorem.Lemma6.LFunctionZeroCount
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
      ``Chen.norm_LFunction_logDeriv_le_of_nonvanishing_ball,
      ``Chen.conductor_height_log_le,
      ``Chen.primitiveZeroFreeWidthAt_height_comparison,
      ``Chen.zeroFreeDiskCenter_re,
      ``Chen.zeroFreeDiskCenter_im,
      ``Chen.zeroFreeDisk_subset_region,
      ``Chen.half_width_point_mem_threeQuarterDisk,
      ``Chen.norm_LFunction_logDeriv_le_of_mixed_region,
      ``Chen.conductor_height_log_ge_threeQuarters,
      ``Chen.primitiveZeroFreeWidthAt_le_quarter,
      ``Chen.inv_primitiveZeroFreeWidthAt_le_scale,
      ``Chen.zeroFreeDiskCenter_norm_add_radius_le,
      ``Chen.zeroFreeDisk_log_growth_le_scale,
      ``Chen.norm_LFunction_logDeriv_le_scale_sq,
      ``Chen.primitiveZeroFreeRegionDataAt_of_nonvanishing,
      ``Chen.primitiveZeroFreeRegionData_of_dataAt,
      ``Chen.primitiveZeroFreeRegion_of_nonvanishing,
      ``Chen.exists_compact_zeroFree_strip,
      ``Chen.exists_uniform_compact_zeroFree_strip,
      ``Chen.exists_LFunction_compact_zeroFree_strip,
      ``Chen.norm_dirichletPhase,
      ``Chen.dirichletPhase_twice,
      ``Chen.real_part_trigonometric_polynomial_nonneg,
      ``Chen.vonMangoldt_twist_term_phase,
      ``Chen.vonMangoldt_term_real,
      ``Chen.vonMangoldt_three_four_one_term_nonneg,
      ``Chen.vonMangoldt_three_four_one_series_nonneg,
      ``Chen.LSeries_twist_vonMangoldt_eq_LFunction,
      ``Chen.Dirichlet_logDeriv_three_four_one_nonneg,
      ``Chen.exists_LFunction_common_compact_strip,
      ``Chen.exists_LFunction_bounded_conductor_strip,
      ``Chen.exists_mixed_region_of_nonvanishing_outside_compact,
      ``Chen.LFunction_zero_count_le] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax => !allowed.contains ax
    if extra.isEmpty then
      Lean.logInfo m!"PASS {name}: {axioms}"
    else
      Lean.logError m!"FAIL {name}: unproved inputs {extra}"
