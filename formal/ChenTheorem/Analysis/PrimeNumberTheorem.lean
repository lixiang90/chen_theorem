import ChenTheorem.Analysis.PNT.MediumPNT
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open Filter Real Asymptotics

namespace Chen

/-- The ordinary PNT follows from the locally included quantitative PNT.
This avoids importing the separate Wiener--Ikehara development. -/
theorem chebyshevPsi_isEquivalent :
    Chebyshev.psi ~[atTop] (fun x : ℝ => x) := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  have hdecay : Tendsto
      (fun x : ℝ => exp (-c * log x ^ ((1 : ℝ) / 10))) atTop (nhds 0) :=
    tendsto_exp_atBot.comp
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        tendsto_log_atTop).const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  have hsmall :
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10))) =o[atTop]
        (fun x : ℝ => x) := by
    simpa using (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO
      ((isLittleO_one_iff ℝ).mpr hdecay)
  exact (hpnt.trans_isLittleO hsmall).isEquivalent

end Chen
