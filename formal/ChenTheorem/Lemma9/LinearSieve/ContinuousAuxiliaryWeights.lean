import ChenTheorem.Lemma9.LinearSieve.ContinuousAuxiliaryIntegrals

open Set MeasureTheory

namespace Chen.LinearSieve

/-- The factor created by a child level's logarithmic error, including
the child's sieve parameter. -/
noncomputable def childAuxiliaryWeight (δ t : ℝ) : ℝ :=
  (t / (t - 1)) ^ δ * (t - 1)

theorem childAuxiliaryWeight_nonneg (δ t : ℝ) (ht : 1 < t) :
    0 ≤ childAuxiliaryWeight δ t := by
  exact mul_nonneg (Real.rpow_nonneg (by positivity) δ) (by linarith)

theorem childAuxiliaryWeight_le (δ t : ℝ) (hδ : δ ≤ 1) (ht : 1 < t) :
    childAuxiliaryWeight δ t ≤ t := by
  have ht1 : 0 < t - 1 := by linarith
  have hb : 1 ≤ t / (t - 1) := (le_div_iff₀ ht1).2 (by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hb hδ
  rw [Real.rpow_one] at hp
  calc
    childAuxiliaryWeight δ t ≤ (t / (t - 1)) * (t - 1) :=
      mul_le_mul_of_nonneg_right hp ht1.le
    _ = t := div_mul_cancel₀ t ht1.ne'

theorem continuousOn_childAuxiliaryWeight (δ : ℝ) :
    ContinuousOn (childAuxiliaryWeight δ) (Ioi 1) := by
  intro t ht
  change 1 < t at ht
  have ht1 : t - 1 ≠ 0 := by linarith
  have hratio : t / (t - 1) ≠ 0 := div_ne_zero (by linarith) ht1
  have hc : ContinuousAt (childAuxiliaryWeight δ) t := by
    unfold childAuxiliaryWeight
    exact (((continuousAt_id.div (continuousAt_id.sub continuousAt_const) ht1).rpow_const
      (Or.inl hratio)).mul (continuousAt_id.sub continuousAt_const))
  exact hc.continuousWithinAt

theorem childAuxiliaryWeight_eq_complement_power (δ t : ℝ) (ht : 1 < t) :
    childAuxiliaryWeight δ t = ((t - 1) / t) ^ (1 - δ) * t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have hr : 0 < (t - 1) / t := div_pos ht1 ht0
  rw [Real.rpow_sub hr, Real.rpow_one]
  have hinv : t / (t - 1) = ((t - 1) / t)⁻¹ := by field_simp
  rw [childAuxiliaryWeight, hinv, Real.inv_rpow hr.le]
  field_simp

theorem integral_childAuxiliaryWeight_lower_le (δ s b : ℝ)
    (hδ : δ ≤ 1) (hs : 3 ≤ s) (hsb : s ≤ b) :
    (∫ t in s..b, childAuxiliaryWeight δ t * lowerAuxiliaryError (t - 1)) ≤
      s ^ 2 * upperAuxiliaryError s - b ^ 2 * upperAuxiliaryError b := by
  have hl : ContinuousOn (fun t => lowerAuxiliaryError (t - 1)) (Icc s b) :=
    continuousOn_lowerAuxiliaryError.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 0 < t - 1; linarith [ht.1])
  have hw := (continuousOn_childAuxiliaryWeight δ).mono
    (show Icc s b ⊆ Ioi 1 from fun t ht => by change 1 < t; linarith [ht.1])
  have hi : IntervalIntegrable (fun t => childAuxiliaryWeight δ t *
      lowerAuxiliaryError (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb, Pi.mul_def] using hw.mul hl
  have hj : IntervalIntegrable (fun t => t * lowerAuxiliaryError (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb, Pi.mul_def, id_eq] using continuousOn_id.mul hl
  rw [← integral_mul_shift_lowerAuxiliaryError s b hs hsb]
  exact intervalIntegral.integral_mono_on hsb hi hj (fun t ht =>
    mul_le_mul_of_nonneg_right (childAuxiliaryWeight_le δ t hδ (by linarith [ht.1]))
      (lowerAuxiliaryError_nonneg (t - 1) (by linarith [ht.1])))

theorem integral_childAuxiliaryWeight_upper_le (δ s b : ℝ)
    (hδ : δ ≤ 1) (hs : 2 < s) (hsb : s ≤ b) :
    (∫ t in s..b, childAuxiliaryWeight δ t * upperAuxiliaryError (t - 1)) ≤
      s ^ 2 * lowerAuxiliaryError s - b ^ 2 * lowerAuxiliaryError b := by
  have hu : ContinuousOn (fun t => upperAuxiliaryError (t - 1)) (Icc s b) :=
    continuousOn_upperAuxiliaryError.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 1 < t - 1; linarith [ht.1])
  have hw := (continuousOn_childAuxiliaryWeight δ).mono
    (show Icc s b ⊆ Ioi 1 from fun t ht => by change 1 < t; linarith [ht.1])
  have hi : IntervalIntegrable (fun t => childAuxiliaryWeight δ t *
      upperAuxiliaryError (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb, Pi.mul_def] using hw.mul hu
  have hj : IntervalIntegrable (fun t => t * upperAuxiliaryError (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb, Pi.mul_def, id_eq] using continuousOn_id.mul hu
  rw [← integral_mul_shift_upperAuxiliaryError s b hs.le hsb]
  exact intervalIntegral.integral_mono_on hsb hi hj (fun t ht =>
    mul_le_mul_of_nonneg_right (childAuxiliaryWeight_le δ t hδ (by linarith [ht.1]))
      (upperAuxiliaryError_nonneg (t - 1) (by linarith [ht.1])))

theorem parameter_integral_childAuxiliaryWeight_lower_le (δ s b : ℝ)
    (hδ : δ ≤ 1) (hs : 3 ≤ s) (hsb : s ≤ b) :
    (1 / s) * (∫ t in s..b, childAuxiliaryWeight δ t * lowerAuxiliaryError (t - 1)) ≤
      s * upperAuxiliaryError s := by
  have h := integral_childAuxiliaryWeight_lower_le δ s b hδ hs hsb
  have hn := mul_nonneg (sq_nonneg b) (upperAuxiliaryError_nonneg b (by linarith))
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by linarith : 0 < s)]
  nlinarith

theorem parameter_integral_childAuxiliaryWeight_upper_le (δ s b : ℝ)
    (hδ : δ ≤ 1) (hs : 2 < s) (hsb : s ≤ b) :
    (1 / s) * (∫ t in s..b, childAuxiliaryWeight δ t * upperAuxiliaryError (t - 1)) ≤
      s * lowerAuxiliaryError s := by
  have h := integral_childAuxiliaryWeight_upper_le δ s b hδ hs hsb
  have hn := mul_nonneg (sq_nonneg b) (lowerAuxiliaryError_nonneg b (by linarith))
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by linarith : 0 < s)]
  nlinarith

theorem mul_childAuxiliaryWeight_shift_eq (δ t : ℝ) (H : ℝ → ℝ) (ht : 1 < t) :
    t * (childAuxiliaryWeight δ t * H (t - 1)) =
      (t / (t - 1)) ^ (δ + 1) * ((t - 1) ^ 2 * H (t - 1)) := by
  have ht1 : 0 < t - 1 := by linarith
  have hr : 0 < t / (t - 1) := div_pos (by linarith) ht1
  rw [Real.rpow_add hr, Real.rpow_one, childAuxiliaryWeight]
  field_simp

/-- Weighted shape is preserved by the child logarithmic factor. This
is the scaling condition needed by the dimension-one Buchstab bound. -/
theorem antitoneOn_mul_childAuxiliaryWeight_shift (δ a : ℝ) (H : ℝ → ℝ)
    (hδ : -1 ≤ δ) (ha : 0 ≤ a)
    (hH : ∀ t ∈ Ioi a, 0 ≤ H t)
    (hanti : AntitoneOn (fun t => t ^ 2 * H t) (Ioi a)) :
    AntitoneOn (fun t => t * (childAuxiliaryWeight δ t * H (t - 1))) (Ioi (a + 1)) := by
  intro s hs t ht hst
  change a + 1 < s at hs
  change a + 1 < t at ht
  have hs1 : 0 < s - 1 := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have hr : t / (t - 1) ≤ s / (s - 1) := by
    apply (div_le_div_iff₀ ht1 hs1).2
    nlinarith
  have hp := Real.rpow_le_rpow (div_nonneg (by linarith) ht1.le) hr
    (by linarith : 0 ≤ δ + 1)
  have hm := hanti (show s - 1 ∈ Ioi a by change a < s - 1; linarith)
    (show t - 1 ∈ Ioi a by change a < t - 1; linarith) (sub_le_sub_right hst 1)
  dsimp only at hm ⊢
  rw [mul_childAuxiliaryWeight_shift_eq δ s H (by linarith),
    mul_childAuxiliaryWeight_shift_eq δ t H (by linarith)]
  exact _root_.mul_le_mul hp hm
    (mul_nonneg (sq_nonneg _) (hH _ (by change a < t - 1; linarith)))
    (Real.rpow_nonneg (div_nonneg (by linarith) hs1.le) _)

theorem antitoneOn_mul_childAuxiliaryWeight_upper (δ : ℝ) (hδ : -1 ≤ δ) :
    AntitoneOn (fun t => t * (childAuxiliaryWeight δ t * upperAuxiliaryError (t - 1)))
      (Ioi 2) := by
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    antitoneOn_mul_childAuxiliaryWeight_shift δ 1 upperAuxiliaryError hδ (by norm_num)
      (fun t ht => upperAuxiliaryError_nonneg t ht) antitoneOn_sq_mul_upperAuxiliaryError

theorem antitoneOn_mul_childAuxiliaryWeight_lower (δ : ℝ) (hδ : -1 ≤ δ) :
    AntitoneOn (fun t => t * (childAuxiliaryWeight δ t * lowerAuxiliaryError (t - 1)))
      (Ioi 1) := by
  simpa only [zero_add] using
    antitoneOn_mul_childAuxiliaryWeight_shift δ 0 lowerAuxiliaryError hδ le_rfl
      (fun t ht => lowerAuxiliaryError_nonneg t ht) antitoneOn_sq_mul_lowerAuxiliaryError

end Chen.LinearSieve
