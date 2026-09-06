import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Set Metric Filter
open scoped Topology

namespace Chen

/-- A continuous lift through the complex exponential is holomorphic whenever
its exponential is holomorphic. The local logarithm is taken near one. -/
theorem differentiableAt_of_cexp (g : ℂ → ℂ) (z : ℂ)
    (hc : ContinuousAt g z) (hd : DifferentiableAt ℂ (fun w => Complex.exp (g w)) z) :
    DifferentiableAt ℂ g z := by
  have hsub : ContinuousAt (fun w => (g w - g z).im) z := by fun_prop
  have hnear : ∀ᶠ w in 𝓝 z, -(Real.pi) < (g w - g z).im ∧ (g w - g z).im < Real.pi := by
    simpa only [sub_self, Complex.zero_im] using hsub.eventually
      (Ioo_mem_nhds (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos))
  have he : DifferentiableAt ℂ (fun w => Complex.exp (g w - g z)) z := by
    simpa only [Complex.exp_sub] using hd.div_const (Complex.exp (g z))
  have hl : DifferentiableAt ℂ (fun w => Complex.log (Complex.exp (g w - g z)) + g z) z :=
    (he.clog (by simp [Complex.slitPlane])).add_const _
  apply hl.congr_of_eventuallyEq
  filter_upwards [hnear] with w hw
  rw [Complex.log_exp hw.1 hw.2.le]
  exact (sub_add_cancel _ _).symm

/-- A holomorphic nonvanishing function on a disk admits a holomorphic
logarithm of its ratio to the center value, normalized to vanish at the center. -/
theorem exists_normalized_analyticLog_on_ball (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ g c = 0 ∧
      ∀ z ∈ ball c R, Complex.exp (g z) = f z / f c := by
  have hc : c ∈ ball c R := mem_ball_self hR
  haveI : ContractibleSpace (ball c R) := (convex_ball c R).contractibleSpace ⟨c, hc⟩
  have hsimply : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hgc, hge⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimply isOpen_ball
    ((hf.div_const (f c)).continuousOn) (by
      rintro ⟨z, hz, he⟩
      exact div_ne_zero (hne z hz) (hne c hc) he)
  change ∀ z ∈ ball c R, Complex.exp (g z) = f z / f c at hge
  have hgd : DifferentiableOn ℂ g (ball c R) := by
    intro z hz
    have heq : (fun w => Complex.exp (g w)) =ᶠ[𝓝 z] (fun w => f w / f c) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hge w hw
    exact (differentiableAt_of_cexp g z
      (hgc.continuousAt (isOpen_ball.mem_nhds hz))
      (((hf z hz).differentiableAt (isOpen_ball.mem_nhds hz)).div_const (f c) |>.congr_of_eventuallyEq heq)).differentiableWithinAt
  refine ⟨fun z => g z - g c, hgd.sub_const _, sub_self _, ?_⟩
  intro z hz
  rw [Complex.exp_sub, hge z hz, hge c hc, div_self (hne c hc), div_one]

/-- The derivative of a normalized logarithm is the logarithmic derivative
of the original function on its domain. -/
theorem deriv_analyticLog_eq_logDeriv {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (c : ℂ) (hc : f c ≠ 0) (he : ∀ z ∈ U, Complex.exp (g z) = f z / f c)
    (z : ℂ) (hz : z ∈ U) : deriv g z = deriv f z / f z := by
  have hgf := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hff := (hf z hz).differentiableAt (hU.mem_nhds hz)
  have heq : (fun w => Complex.exp (g w)) =ᶠ[𝓝 z] (fun w => f w / f c) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, he⟩
  have hd := heq.deriv_eq
  rw [hgf.hasDerivAt.cexp.deriv, (hff.hasDerivAt.div_const (f c)).deriv, he z hz] at hd
  have hz0 : f z ≠ 0 := by
    intro hzero
    have := he z hz
    rw [hzero, zero_div] at this
    exact Complex.exp_ne_zero (g z) this
  field_simp [hc, hz0] at hd ⊢
  linear_combination hd

end Chen
