import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliarySumDecay

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

theorem exp_neg_third_le_linear (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (-u / 3) ≤ 1 - u / 4 := by
  rw [show -u / 3 = -(u / 3) by ring, Real.exp_neg, ← one_div,
    div_le_iff₀ (Real.exp_pos (u / 3))]
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u / 3))
    (show 0 ≤ 1 - u / 4 by linarith)
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]

theorem integral_unit_linear_decay (s : ℝ) :
    (∫ t in (s - 1)..s, 1 - (t - (s - 1)) / 4) = 7 / 8 := by
  have hd : ∀ t ∈ uIcc (s - 1) s,
      HasDerivAt (fun t => t - (t - (s - 1)) ^ 2 / 8)
        (1 - (t - (s - 1)) / 4) t := by
    intro t _
    apply ((hasDerivAt_id t).sub
      ((((hasDerivAt_id t).sub_const (s - 1)).pow 2).div_const 8)).congr_deriv
    dsimp
    ring
  have hc : Continuous (fun t : ℝ => 1 - (t - (s - 1)) / 4) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  ring

theorem auxiliaryErrorSum_shift_pairing_decay_bound (s : ℝ) (hs : 5 ≤ s) :
    s * auxiliaryAdjoint s * auxiliaryErrorSum s ≤
      (7 / 8) * auxiliaryAdjoint (s + 1) * auxiliaryErrorSum (s - 1) := by
  rw [auxiliaryErrorSum_pairing_zero s (by linarith)]
  have hab : s - 1 ≤ s := by linarith
  have hq : Continuous (fun t : ℝ => auxiliaryAdjoint (t + 1)) := by
    unfold auxiliaryAdjoint
    fun_prop
  have hc := hq.continuousOn.mul (continuousOn_auxiliaryErrorSum.mono
    (show Icc (s - 1) s ⊆ Ioi 1 from by
      intro t ht; change 1 < t; linarith [ht.1]))
  have hg : Continuous (fun t : ℝ =>
      (auxiliaryAdjoint (s + 1) * auxiliaryErrorSum (s - 1)) *
        (1 - (t - (s - 1)) / 4)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (hc.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable (a := s - 1) (b := s))
    (show ∀ t ∈ Icc (s - 1) s,
      auxiliaryAdjoint (t + 1) * auxiliaryErrorSum t ≤
        (auxiliaryAdjoint (s + 1) * auxiliaryErrorSum (s - 1)) *
          (1 - (t - (s - 1)) / 4) from by
      intro t ht
      have he := auxiliaryErrorSum_exponential_comparison (s - 1) t (by linarith) ht.1
      have hl := mul_le_mul_of_nonneg_right
        (exp_neg_third_le_linear (t - (s - 1)) (by linarith [ht.1])
          (by linarith [ht.2])) (auxiliaryErrorSum_pos (s - 1) (by linarith)).le
      have hqle := monotoneOn_auxiliaryAdjoint
        (show t + 1 ∈ Ici 2 by change 2 ≤ t + 1; linarith [ht.1])
        (show s + 1 ∈ Ici 2 by change 2 ≤ s + 1; linarith)
        (by linarith [ht.2])
      have hm := _root_.mul_le_mul hqle (he.trans hl)
        (auxiliaryErrorSum_pos t (by linarith [ht.1])).le
        (auxiliaryAdjoint_pos (s + 1) (by linarith)).le
      convert! hm using 1
      ring)
  rw [intervalIntegral.integral_const_mul, integral_unit_linear_decay] at hi
  convert! hi using 1
  ring

/-- The elementary shift estimate can be strengthened using its own
exponential decay on the preceding unit interval. -/
theorem auxiliaryErrorSum_shift_ge_self (s : ℝ) (hs : 16 ≤ s) :
    s * auxiliaryErrorSum s ≤ auxiliaryErrorSum (s - 1) := by
  have h := auxiliaryErrorSum_shift_pairing_decay_bound s (by linarith)
  have hq : (7 / 8) * auxiliaryAdjoint (s + 1) ≤ auxiliaryAdjoint s := by
    dsimp [auxiliaryAdjoint]
    nlinarith [sq_nonneg (s - 16)]
  have hm := mul_le_mul_of_nonneg_right hq
    (auxiliaryErrorSum_pos (s - 1) (by linarith)).le
  have hp := auxiliaryAdjoint_pos s (by linarith)
  nlinarith

theorem hasDerivAt_exp_sq_mul_auxiliaryErrorSum (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun t => Real.exp t * (t ^ 2 * auxiliaryErrorSum t))
      (Real.exp s * s * (s * auxiliaryErrorSum s - auxiliaryErrorSum (s - 1))) s := by
  apply ((Real.hasDerivAt_exp s).mul
    (hasDerivAt_sq_mul_auxiliaryErrorSum s hs)).congr_deriv
  ring

theorem antitoneOn_exp_sq_mul_auxiliaryErrorSum :
    AntitoneOn (fun s => Real.exp s * (s ^ 2 * auxiliaryErrorSum s)) (Ici 16) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 16)
  · apply ContinuousOn.mul (by fun_prop)
    exact (continuousOn_id.pow 2).mul (continuousOn_auxiliaryErrorSum.mono
      (by intro s hs; change 1 < s; linarith [show 16 ≤ s from hs]))
  · intro s hs
    rw [interior_Ici] at hs
    exact (hasDerivAt_exp_sq_mul_auxiliaryErrorSum s
      (by linarith [show 16 < s from hs])).hasDerivWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le (by linarith [show 16 < s from hs]))
      (sub_nonpos.mpr (auxiliaryErrorSum_shift_ge_self s (le_of_lt hs)))

theorem auxiliaryErrorSum_exponential_bound (s : ℝ) (hs : 16 ≤ s) :
    auxiliaryErrorSum s ≤ (Real.exp 16 * auxiliaryErrorSum 16) * Real.exp (-s) := by
  have h := antitoneOn_exp_sq_mul_auxiliaryErrorSum (by simp) hs hs
  have hsq : (16 : ℝ) ^ 2 ≤ s ^ 2 := by nlinarith
  have hn := (auxiliaryErrorSum_pos s (by linarith)).le
  have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hn)
    (Real.exp_pos s).le
  have hcancel : Real.exp s * auxiliaryErrorSum s ≤ Real.exp 16 * auxiliaryErrorSum 16 := by
    dsimp only at h
    nlinarith
  rw [mul_comm (Real.exp s), ← le_div_iff₀ (Real.exp_pos s)] at hcancel
  simpa only [Real.exp_neg, div_eq_mul_inv] using hcancel

/-- Both actual auxiliary errors satisfy the exponential boundary condition
used for the delay equation. No decay hypothesis is assumed. -/
theorem auxiliaryErrors_exponential_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 16 ≤ s →
      upperAuxiliaryError s ≤ C * Real.exp (-s) ∧
      lowerAuxiliaryError s ≤ C * Real.exp (-s) := by
  refine ⟨Real.exp 16 * auxiliaryErrorSum 16,
    mul_pos (Real.exp_pos _) (auxiliaryErrorSum_pos _ (by norm_num)), ?_⟩
  intro s hs
  have h := auxiliaryErrorSum_exponential_bound s hs
  have hu := (upperAuxiliaryError_pos s (by linarith)).le
  have hl := (lowerAuxiliaryError_pos s (by linarith)).le
  dsimp [auxiliaryErrorSum] at h ⊢
  constructor <;> linarith

end Chen.LinearSieve
