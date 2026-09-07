import Submission.ChenTheorem.Analysis.ZetaRegularPart
import Submission.ChenTheorem.Analysis.PoleTaylorCoefficients

set_option autoImplicit true
open scoped Topology

namespace Chen

theorem backwardTaylorCoeff_regularizedZetaMul {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (n : ℕ) :
    backwardTaylorCoeff (regularizedZetaMul g) 2 n =
      backwardTaylorCoeff (fun s => riemannZeta s * g s) 2 n - g 1 := by
  have he : regularizedZetaMul g =ᶠ[𝓝 (2 : ℂ)]
      (fun s => riemannZeta s * g s - g 1 / (s - 1)) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (2 : ℂ) ≠ 1)] with s hs
    exact regularizedZetaMul_eq hs
  have hF : AnalyticAt ℂ (fun s => riemannZeta s * g s) 2 :=
    (analyticOn_riemannZeta 2 (by norm_num)).mul (hg.analyticAt 2)
  have hP : AnalyticAt ℂ (fun s : ℂ => g 1 / (s - 1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  have hc : backwardTaylorCoeff (regularizedZetaMul g) 2 n =
      backwardTaylorCoeff (fun s => riemannZeta s * g s - g 1 / (s - 1)) 2 n := by
    unfold backwardTaylorCoeff
    rw [he.iteratedDeriv_eq]
  rw [hc, backwardTaylorCoeff_sub n hF.contDiffAt hP.contDiffAt, backwardTaylorCoeff_pole]

theorem hasSum_regularizedZetaMul_backwardTaylor {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (z : ℂ) :
    HasSum (fun n : ℕ => (backwardTaylorCoeff (fun s => riemannZeta s * g s) 2 n - g 1) * z ^ n)
      (regularizedZetaMul g (2 - z)) := by
  have h := hasSum_backwardTaylorCoeff
    (differentiable_regularizedZetaMul hg).differentiableOn
    (c := (2 : ℂ)) (R := ‖z‖ + 1) (by linarith : ‖z‖ < ‖z‖ + 1)
  simpa only [backwardTaylorCoeff_regularizedZetaMul hg] using h

end Chen
