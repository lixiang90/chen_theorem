import Mathlib.Analysis.Complex.Hadamard

set_option autoImplicit true

open Complex.HadamardThreeLines

namespace Chen

/-- The three-circle estimate, obtained from mathlib's three-lines theorem by
composing an entire function with the complex exponential. -/
theorem norm_le_three_circle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c z : ℂ} {r R A B : ℝ} (hr : 0 < r) (hrR : r < R)
    (hA : ∀ w, ‖w - c‖ ≤ r → ‖f w‖ ≤ A)
    (hB : ∀ w, ‖w - c‖ ≤ R → ‖f w‖ ≤ B)
    (hzr : r ≤ ‖z - c‖) (hzR : ‖z - c‖ ≤ R) :
    ‖f z‖ ≤ A ^ (1 - (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) *
      B ^ ((Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) := by
  have hR : 0 < R := hr.trans hrR
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp (hr.trans_le hzr)
  have hlr : Real.log r < Real.log R := Real.log_lt_log hr hrR
  let F : ℂ → ℂ := fun w => f (c + Complex.exp w)
  have hF : Differentiable ℂ F := hf.comp (Complex.differentiable_exp.const_add c)
  have he (w : ℂ) : ‖c + Complex.exp w - c‖ = Real.exp w.re := by
    rw [add_sub_cancel_left, Complex.norm_exp]
  have hFR (w : ℂ) (hw : w ∈ verticalClosedStrip (Real.log r) (Real.log R)) : ‖F w‖ ≤ B := by
    apply hB
    rw [he]
    exact (Real.exp_le_exp.mpr hw.2).trans_eq (Real.exp_log hR)
  have hbounded : BddAbove ((norm ∘ F) '' verticalClosedStrip (Real.log r) (Real.log R)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hFR w hw
  have hleft : ∀ w ∈ Complex.re ⁻¹' {Real.log r}, ‖F w‖ ≤ A := by
    intro w hw
    apply hA
    rw [he, show w.re = Real.log r from hw, Real.exp_log hr]
  have hright : ∀ w ∈ Complex.re ⁻¹' {Real.log R}, ‖F w‖ ≤ B := by
    intro w hw
    apply hB
    rw [he, show w.re = Real.log R from hw, Real.exp_log hR]
  have hz : Complex.log (z - c) ∈ verticalClosedStrip (Real.log r) (Real.log R) := by
    change Real.log r ≤ (Complex.log (z - c)).re ∧ (Complex.log (z - c)).re ≤ Real.log R
    rw [Complex.log_re]
    exact ⟨Real.log_le_log hr hzr, Real.log_le_log (hr.trans_le hzr) hzR⟩
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlr hz hF.diffContOnCl hbounded hleft hright
  simpa only [F, Complex.exp_log hz0, add_sub_cancel, Complex.log_re] using h

end Chen
