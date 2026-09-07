import Submission.ChenTheorem.Lemma9.LinearSieve.InitialInflationBudget
import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousTerminalLoss

set_option autoImplicit true
namespace Chen.LinearSieve

theorem initial_density_loss_le_error (d δ D s r g : ℝ)
    (hD : 1 < D) (hs : 1 < s) (hs3 : s ≤ 3) (hr : 0 ≤ r) (hg : 0 ≤ g) :
    (linearSieveInitialConstant * r + (1 + r) * g) / s ≤
      ((Real.log D) ^ δ * (r + (1 + r) * g / linearSieveInitialConstant)) *
        inflatedAuxiliaryError d δ D s upperAuxiliaryError := by
  have hA : 0 < linearSieveInitialConstant := by linarith [linearSieveInitialConstant_ge_three]
  have hc : 0 ≤ r + (1 + r) * g / linearSieveInitialConstant := by positivity
  have h := rpow_mul_inflatedAuxiliaryError_ge d δ D s upperAuxiliaryError hD
    (by linarith) (upperAuxiliaryError_nonneg s hs)
  rw [upperAuxiliaryError_initial s hs hs3] at h
  have hm := mul_le_mul_of_nonneg_left h hc
  convert! hm using 1
  · field_simp
  · ring

/-- The strict cube-step contraction absorbs both small multiplicative
losses and one additive error budget. -/
theorem initial_transfer_absorption (α σ r : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hσ : 1 ≤ σ) (hr : 0 ≤ r) (hrx : r ≤ α / (512 * σ)) :
    α / (512 * σ) + (1 - α / (64 * σ)) * (1 + r) * (1 + α / (512 * σ)) ≤ 1 := by
  have hσ0 : 0 < σ := by linarith
  let x := α / (512 * σ)
  have hx : 0 ≤ x := div_nonneg hα (by positivity)
  have he : α / (64 * σ) = 8 * x := by dsimp [x]; field_simp; ring
  have hρ : 0 ≤ 1 - α / (64 * σ) := by
    have h := (div_le_one (by positivity : 0 < 64 * σ)).mpr (show α ≤ 64 * σ by linarith)
    linarith
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (_root_.add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hrx) hρ) (show 0 ≤ 1 + x by linarith)
  change (1 - α / (64 * σ)) * (1 + r) * (1 + x) ≤
    (1 - α / (64 * σ)) * (1 + x) * (1 + x) at hm
  rw [he] at hm ⊢
  change x + (1 - 8 * x) * (1 + r) * (1 + x) ≤ 1
  have hx3 := mul_nonneg hx (sq_nonneg x)
  nlinarith [sq_nonneg x]

end Chen.LinearSieve
