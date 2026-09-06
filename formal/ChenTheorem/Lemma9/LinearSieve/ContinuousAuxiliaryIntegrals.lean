import ChenTheorem.Lemma9.LinearSieve.ContinuousAuxiliary

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_sq_mul_upperAuxiliaryError_zero :
    Tendsto (fun s => s ^ 2 * upperAuxiliaryError s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [eventually_ge_atTop (a + 1)] with s hs
    linarith
  have h := ((tendsto_mul_lowerContinuousError_zero.comp hshift).add
    (tendsto_lowerContinuousError_zero.comp hshift)).add tendsto_mul_upperContinuousError_zero
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (3 : ℝ)] with s hs
  dsimp [upperAuxiliaryError]
  rw [max_eq_left (by linarith : 2 ≤ s - 1)]
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

theorem tendsto_sq_mul_lowerAuxiliaryError_zero :
    Tendsto (fun s => s ^ 2 * lowerAuxiliaryError s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [eventually_ge_atTop (a + 1)] with s hs
    linarith
  have h := ((tendsto_mul_upperContinuousError_zero.comp hshift).add
    (tendsto_upperContinuousError_zero.comp hshift)).add tendsto_mul_lowerContinuousError_zero
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
  dsimp [lowerAuxiliaryError]
  rw [if_neg (by linarith : ¬s ≤ 2)]
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

theorem integral_mul_shift_lowerAuxiliaryError (s b : ℝ) (hs : 3 ≤ s) (hsb : s ≤ b) :
    (∫ t in s..b, t * lowerAuxiliaryError (t - 1)) =
      s ^ 2 * upperAuxiliaryError s - b ^ 2 * upperAuxiliaryError b := by
  have hc : ContinuousOn (fun t => t * lowerAuxiliaryError (t - 1)) (Icc s b) :=
    continuousOn_id.mul (continuousOn_lowerAuxiliaryError.comp
      (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 0 < t - 1; linarith [ht.1]))
  have hi : IntervalIntegrable (fun t => t * lowerAuxiliaryError (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb] using hc
  have hf : ContinuousOn (fun t => t ^ 2 * upperAuxiliaryError t) (Icc s b) :=
    (continuousOn_id.pow 2).mul (continuousOn_upperAuxiliaryError.mono
      (fun t ht => by change 1 < t; linarith [ht.1]))
  have hd : ∀ t ∈ Ioo s b, HasDerivAt (fun t => t ^ 2 * upperAuxiliaryError t)
      (-(t * lowerAuxiliaryError (t - 1))) t := by
    intro t ht
    simpa only [neg_mul] using hasDerivAt_sq_mul_upperAuxiliaryError t (by linarith [ht.1])
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsb hf hd hi.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem integral_mul_shift_upperAuxiliaryError (s b : ℝ) (hs : 2 ≤ s) (hsb : s ≤ b) :
    (∫ t in s..b, t * upperAuxiliaryError (t - 1)) =
      s ^ 2 * lowerAuxiliaryError s - b ^ 2 * lowerAuxiliaryError b := by
  -- At `s = 2` the upper auxiliary formula has only a right limit at one.
  -- Its initial formula supplies a continuous extension for the integrand.
  let H : ℝ → ℝ := fun t => if t ≤ 3 then
    linearSieveInitialConstant / (t - 1) ^ 2 else upperAuxiliaryError (t - 1)
  have hH : ∀ t ∈ Ioc s b, H t = upperAuxiliaryError (t - 1) := by
    intro t ht
    dsimp [H]
    split_ifs with ht3
    · exact (upperAuxiliaryError_initial (t - 1) (by linarith [ht.1]) (by linarith)).symm
    · rfl
  have hcH : ContinuousOn H (Icc s b) := by
    apply ContinuousOn.if
    · intro t ht
      have heq : t = 3 := by
        have hm := ht.2
        change t ∈ frontier (Iic (3 : ℝ)) at hm
        simpa only [frontier_Iic, mem_singleton_iff] using hm
      subst t
      simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
        (upperAuxiliaryError_initial 2 (by norm_num) (by norm_num)).symm
    · apply continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      intro t ht
      apply pow_ne_zero 2
      change t - 1 ≠ 0
      linarith [ht.1.1]
    · apply continuousOn_upperAuxiliaryError.comp (continuousOn_id.sub continuousOn_const)
      intro t ht
      have ht3 : 3 ≤ t := by
        have hm := ht.2
        simp only [not_le] at hm
        change t ∈ closure (Ioi (3 : ℝ)) at hm
        simpa only [closure_Ioi, mem_Ici] using hm
      change 1 < t - 1
      linarith
  have hi : IntervalIntegrable (fun t => t * H t) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb, Pi.mul_def, id_eq] using continuousOn_id.mul hcH
  have hf : ContinuousOn (fun t => t ^ 2 * lowerAuxiliaryError t) (Icc s b) :=
    (continuousOn_id.pow 2).mul (continuousOn_lowerAuxiliaryError.mono
      (fun t ht => by change 0 < t; linarith [ht.1]))
  have hd : ∀ t ∈ Ioo s b, HasDerivAt (fun t => t ^ 2 * lowerAuxiliaryError t)
      (-(t * H t)) t := by
    intro t ht
    rw [hH t ⟨ht.1, ht.2.le⟩]
    simpa only [neg_mul] using hasDerivAt_sq_mul_lowerAuxiliaryError t (by linarith [ht.1])
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsb hf hd hi.neg
  rw [intervalIntegral.integral_neg] at h
  have heq : (∫ t in s..b, t * H t) = ∫ t in s..b, t * upperAuxiliaryError (t - 1) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hsb]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hH t ht]
  rw [heq] at h
  linarith

theorem tendsto_integral_mul_shift_lowerAuxiliaryError (s : ℝ) (hs : 3 ≤ s) :
    Tendsto (fun b => ∫ t in s..b, t * lowerAuxiliaryError (t - 1)) atTop
      (𝓝 (s ^ 2 * upperAuxiliaryError s)) := by
  have hc : Tendsto (fun _ : ℝ => s ^ 2 * upperAuxiliaryError s) atTop
      (𝓝 (s ^ 2 * upperAuxiliaryError s)) := tendsto_const_nhds
  have h := hc.sub tendsto_sq_mul_upperAuxiliaryError_zero
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop s] with b hb
  exact (integral_mul_shift_lowerAuxiliaryError s b hs hb).symm

theorem tendsto_integral_mul_shift_upperAuxiliaryError (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun b => ∫ t in s..b, t * upperAuxiliaryError (t - 1)) atTop
      (𝓝 (s ^ 2 * lowerAuxiliaryError s)) := by
  have hc : Tendsto (fun _ : ℝ => s ^ 2 * lowerAuxiliaryError s) atTop
      (𝓝 (s ^ 2 * lowerAuxiliaryError s)) := tendsto_const_nhds
  have h := hc.sub tendsto_sq_mul_lowerAuxiliaryError_zero
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop s] with b hb
  exact (integral_mul_shift_upperAuxiliaryError s b hs hb).symm

theorem parameter_integral_mul_shift_lowerAuxiliaryError_le (s b : ℝ)
    (hs : 3 ≤ s) (hsb : s ≤ b) :
    (1 / s ^ 2) * (∫ t in s..b, t * lowerAuxiliaryError (t - 1)) ≤
      upperAuxiliaryError s := by
  rw [integral_mul_shift_lowerAuxiliaryError s b hs hsb,
    one_div, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < s))]
  have hn := mul_nonneg (sq_nonneg b) (upperAuxiliaryError_nonneg b (by linarith))
  nlinarith

theorem parameter_integral_mul_shift_upperAuxiliaryError_le (s b : ℝ)
    (hs : 2 ≤ s) (hsb : s ≤ b) :
    (1 / s ^ 2) * (∫ t in s..b, t * upperAuxiliaryError (t - 1)) ≤
      lowerAuxiliaryError s := by
  rw [integral_mul_shift_upperAuxiliaryError s b hs hsb,
    one_div, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < s))]
  have hn := mul_nonneg (sq_nonneg b) (lowerAuxiliaryError_nonneg b (by linarith))
  nlinarith

end Chen.LinearSieve
