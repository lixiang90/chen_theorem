import ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierIntegralLower

namespace Chen.LinearSieve

theorem mul_exp_neg_half_le (v : ℝ) :
    v * Real.exp (-v / 2) ≤ 4 * Real.exp (-v / 4) := by
  have h := Real.add_one_le_exp (v / 4)
  have hm := mul_le_mul_of_nonneg_right
    (show v ≤ 4 * Real.exp (v / 4) by linarith) (Real.exp_pos (-v / 2)).le
  calc
    _ ≤ 4 * Real.exp (v / 4) * Real.exp (-v / 2) := hm
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

theorem exp_neg_quarter_le_inv_sq (s v : ℝ) (hs : 0 < s)
    (hv : 8 * Real.log s ≤ v) : Real.exp (-v / 4) ≤ 1 / s ^ 2 := by
  have h := Real.exp_le_exp.mpr (show -v / 4 ≤ -2 * Real.log s by linarith)
  have he : Real.exp (-2 * Real.log s) = 1 / s ^ 2 := by
    rw [show -2 * Real.log s = -Real.log (s ^ 2) by rw [Real.log_pow]; ring,
      Real.exp_neg, Real.exp_log (sq_pos_of_pos hs), one_div]
  exact he ▸ h

theorem auxiliaryBarrier_upper_factor_gt_one (ℓ s : ℝ)
    (hs : 4 ≤ s) (hℓ : 8 * (Real.log s + 1) ≤ ℓ) :
    0 < ℓ - 5 / s ∧
      1 < (ℓ - 2 / s) * ((1 - Real.exp (-(ℓ - 5 / s) / 2)) / (ℓ - 5 / s)) := by
  have hs0 : 0 < s := by linarith
  have hlog := Real.log_pos (show 1 < s by linarith)
  have hfrac : 5 / s ≤ 5 / 4 := (div_le_div_iff₀ hs0 (by norm_num)).mpr (by linarith)
  have hvlo : 8 * Real.log s ≤ ℓ - 5 / s := by linarith
  have hv : 0 < ℓ - 5 / s := by linarith
  refine ⟨hv, ?_⟩
  have he := exp_neg_quarter_le_inv_sq s (ℓ - 5 / s) hs0 hvlo
  have hfirst := (mul_exp_neg_half_le (ℓ - 5 / s)).trans
    (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 4))
  have hexp := (Real.exp_le_exp.mpr (show -(ℓ - 5 / s) / 2 ≤ -(ℓ - 5 / s) / 4 by linarith)).trans he
  have hthree : 3 / s ≤ (3 : ℝ) := (div_le_iff₀ hs0).mpr (by linarith)
  have hsecond := _root_.mul_le_mul hthree hexp (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 3)
  have heq : 5 / s = 2 / s + 3 / s := by ring
  have hsum : (ℓ - 2 / s) * Real.exp (-(ℓ - 5 / s) / 2) ≤ 7 / s ^ 2 := by
    calc
      _ = (ℓ - 5 / s) * Real.exp (-(ℓ - 5 / s) / 2) +
          (3 / s) * Real.exp (-(ℓ - 5 / s) / 2) := by rw [heq]; ring
      _ ≤ 4 * (1 / s ^ 2) + 3 * (1 / s ^ 2) := _root_.add_le_add hfirst hsecond
      _ = _ := by ring
  have hsmall : 7 / s ^ 2 < 3 / s := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hs0) hs0).mpr
    nlinarith
  have hstrict := hsum.trans_lt hsmall
  rw [← mul_div_assoc, lt_div_iff₀ hv, one_mul]
  nlinarith [heq]

theorem upperAuxiliaryBarrier_no_stationary (C s : ℝ)
    (hC : 0 ≤ C) (hs : 4 ≤ s)
    (hmono : MonotoneOn (auxiliaryBarrierWeight 8 C) (Set.Icc (s - 1) s)) :
    deriv (auxiliaryBarrierWeight 8 C) s ≠ 0 := by
  intro hstat
  have hℓ : 8 * (Real.log s + 1) ≤ auxiliaryBarrierSlope 8 C s := by
    dsimp [auxiliaryBarrierSlope]
    linarith
  obtain ⟨hv, hgt⟩ := auxiliaryBarrier_upper_factor_gt_one (auxiliaryBarrierSlope 8 C s) s hs hℓ
  have he : (1 + (8 : ℝ) / 2) = 5 := by norm_num
  have h := auxiliaryBarrier_stationary_upper_constraint 8 C s
    (by norm_num) hs (by simpa only [he] using hv.ne') hmono hstat
  rw [he] at h
  linarith

end Chen.LinearSieve
