import ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierIntegral

namespace Chen.LinearSieve

/-- A coarse numerical separation is enough for the lower logarithmic
barrier; no sharp asymptotic expansion of the delay solution is needed. -/
theorem auxiliaryBarrier_stationary_factor_lt_one (ℓ s : ℝ)
    (hs : 0 < s) (hlog : 20 ≤ Real.log s)
    (hℓ : ℓ ≤ (Real.log s + 1) / 2) (hr : (1 / 3 : ℝ) ≤ ℓ - 2 / s) :
    0 < ℓ - 5 / s ∧
      (ℓ - 2 / s) * ((1 - Real.exp (-(ℓ - 5 / s))) / (ℓ - 5 / s)) < 1 := by
  have hsb : 21 ≤ s := by linarith [Real.log_le_sub_one_of_pos hs]
  have hinv : 3 / s < (1 / 3 : ℝ) := (div_lt_iff₀ hs).mpr (by linarith)
  have heq : 5 / s = 2 / s + 3 / s := by ring
  have hv : 0 < ℓ - 5 / s := by linarith
  refine ⟨hv, ?_⟩
  have hE : Real.exp (-(Real.log s + 1) / 2) ≤ Real.exp (-(ℓ - 5 / s)) := by
    apply Real.exp_le_exp.mpr
    have := div_pos (by norm_num : (0 : ℝ) < 5) hs
    linarith
  have hbase : 9 < s * Real.exp (-(Real.log s + 1) / 2) := by
    have he : s * Real.exp (-(Real.log s + 1) / 2) =
        Real.exp ((Real.log s - 1) / 2) := by
      conv_lhs => arg 1; rw [← Real.exp_log hs]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have h := Real.add_one_le_exp ((Real.log s - 1) / 2)
    linarith
  have hlarge := hbase.trans_le (mul_le_mul_of_nonneg_left hE hs.le)
  have hm := mul_le_mul_of_nonneg_right hr
    (mul_nonneg hs.le (Real.exp_pos (-(ℓ - 5 / s))).le)
  have hsmall : 3 / s < (ℓ - 2 / s) * Real.exp (-(ℓ - 5 / s)) := by
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  rw [← mul_div_assoc, div_lt_iff₀ hv, one_mul]
  nlinarith [heq]

/-- At a candidate stationary point the pairing forces a factor at least
one, whereas the explicit kernel bound forces it strictly below one. -/
theorem lowerAuxiliaryBarrier_no_stationary (C s : ℝ)
    (hC : 0 ≤ C) (hs : 4 ≤ s) (hlog : 20 ≤ Real.log s)
    (hanti : AntitoneOn (auxiliaryBarrierWeight (1 / 2) (-C)) (Set.Icc (s - 1) s)) :
    deriv (auxiliaryBarrierWeight (1 / 2) (-C)) s ≠ 0 := by
  intro hstat
  have hr := (auxiliaryBarrierWeight_stationary_iff (1 / 2) (-C) s (by linarith)).mp hstat
  have hlo := auxiliaryShiftRatio_lower s (by linarith)
  rw [hr] at hlo
  have hℓ : auxiliaryBarrierSlope (1 / 2) (-C) s ≤ (Real.log s + 1) / 2 := by
    dsimp [auxiliaryBarrierSlope]
    linarith
  obtain ⟨hv, hlt⟩ := auxiliaryBarrier_stationary_factor_lt_one
    (auxiliaryBarrierSlope (1 / 2) (-C) s) s (by linarith) hlog hℓ hlo
  have he : (2 * (1 / 2 : ℝ) + 4) = 5 := by norm_num
  have h := auxiliaryBarrier_stationary_constraint (1 / 2) (-C) s
    (by norm_num) hs (by simpa only [he] using hv.ne') hanti hstat
  rw [he] at h
  linarith

end Chen.LinearSieve
