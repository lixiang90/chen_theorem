import Submission.ChenTheorem.Lemma6.NonprincipalSmallPower
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit true

namespace Chen

theorem exists_nonprincipal_deriv_small_power_disk {ε : ℝ} (hε : 0 < ε) :
    ∃ r D : ℝ, 0 < r ∧ 0 < D ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 →
        ∀ s : ℂ, ‖s - 1‖ ≤ r →
          ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ D * (q : ℝ) ^ ε := by
  obtain ⟨r, K, hr, hK, h⟩ := exists_nonprincipal_small_power_disk hε
  refine ⟨r / 2, K / (r / 2), by positivity, by positivity, ?_⟩
  intro q inst χ hq hχ s hs
  have hbound (w : ℂ) (hw : w ∈ Metric.sphere s (r / 2)) :
      ‖DirichletCharacter.LFunction χ w‖ ≤ K * (q : ℝ) ^ ε := by
    have hwN : ‖w - s‖ = r / 2 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have hN := norm_add_le (w - s) (s - 1)
    rw [sub_add_sub_cancel, hwN] at hN
    exact h q χ hq hχ w (by linarith)
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r / 2)
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl hbound
  apply hd.trans_eq
  ring

/-- A zero near one bounds the value at one by its distance to one, with only
an arbitrarily small power of the conductor as loss. -/
theorem exists_nonprincipal_one_bound_of_real_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ r D : ℝ, 0 < r ∧ 0 < D ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 →
        ∀ β : ℝ, 1 - r ≤ β → β ≤ 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          ‖DirichletCharacter.LFunction χ 1‖ ≤ D * (q : ℝ) ^ ε * (1 - β) := by
  obtain ⟨r, D, hr, hD, hd⟩ := exists_nonprincipal_deriv_small_power_disk hε
  refine ⟨r, D, hr, hD, ?_⟩
  intro q inst χ hq hχ β hβ hβ' hz
  have hmem : (β : ℂ) ∈ Metric.closedBall (1 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : β - 1 ≤ 0)]
    linarith
  have hmem1 : (1 : ℂ) ∈ Metric.closedBall (1 : ℂ) r := Metric.mem_closedBall_self hr.le
  have h := (convex_closedBall (1 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (DirichletCharacter.differentiable_LFunction hχ) s)
    (fun s hs => hd q χ hq hχ s (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs))
    hmem hmem1
  rw [hz, sub_zero, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_of_nonneg (sub_nonneg.mpr hβ')] at h
  exact h

end Chen
