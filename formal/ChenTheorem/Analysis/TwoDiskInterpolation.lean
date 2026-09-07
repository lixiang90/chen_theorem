import ChenTheorem.Analysis.ThreeCircleBound

namespace Chen

/-- An inner bound independent of `q` and an outer cubic bound yield an arbitrarily
small power of `q` when the logarithmic separation of the circles is large enough. -/
theorem norm_le_small_power_of_two_disks {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c z : ℂ} {r R A C q ε : ℝ} (hr : 0 < r) (hrR : r < R)
    (hA : 1 ≤ A) (hC : 1 ≤ C) (hq : 1 ≤ q) (hε : 0 ≤ ε)
    (hscale : 3 * Real.log 3 ≤ ε * (Real.log R - Real.log r))
    (hinner : ∀ w, ‖w - c‖ ≤ r → ‖f w‖ ≤ A)
    (houter : ∀ w, ‖w - c‖ ≤ R → ‖f w‖ ≤ C * q ^ 3)
    (hz : ‖z - c‖ ≤ 3 * r) (hzR : ‖z - c‖ ≤ R) :
    ‖f z‖ ≤ A * C * q ^ ε := by
  have hq0 : 0 ≤ q := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hC0 : 0 ≤ C := by linarith
  by_cases hzr : ‖z - c‖ ≤ r
  · apply (hinner z hzr).trans
    have hpow : 1 ≤ q ^ ε := Real.one_le_rpow hq hε
    have h1 := mul_le_mul_of_nonneg_left hC hA0
    have h2 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hA0 hC0)
    nlinarith
  have hzr' : r ≤ ‖z - c‖ := le_of_lt (lt_of_not_ge hzr)
  have hgap : 0 < Real.log R - Real.log r := sub_pos.mpr (Real.log_lt_log hr hrR)
  let θ := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr (Real.log_le_log hr hzr')) hgap.le
  have hθ1 : θ ≤ 1 := by
    apply (div_le_iff₀ hgap).mpr
    have h := Real.log_le_log (hr.trans_le hzr') hzR
    linarith
  have hlog : Real.log ‖z - c‖ - Real.log r ≤ Real.log 3 := by
    have h := Real.log_le_log (hr.trans_le hzr') hz
    rw [Real.log_mul (by norm_num) hr.ne'] at h
    linarith
  have hθε : 3 * θ ≤ ε := by
    dsimp [θ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hgap).mpr
    linarith
  have hApow : A ^ (1 - θ) ≤ A := by
    simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - θ ≤ 1 by linarith)
  have hCpow : C ^ θ ≤ C := by
    simpa using Real.rpow_le_rpow_of_exponent_le hC hθ1
  have hqpow : q ^ (3 * θ) ≤ q ^ ε := Real.rpow_le_rpow_of_exponent_le hq hθε
  have hBpow : (C * q ^ (3 : ℕ)) ^ θ ≤ C * q ^ ε := by
    rw [Real.mul_rpow hC0 (pow_nonneg hq0 _), ← Real.rpow_natCast_mul hq0 3 θ]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul hCpow hqpow (Real.rpow_nonneg hq0 _) hC0
  have h := norm_le_three_circle hf hr hrR hinner houter hzr' hzR
  change ‖f z‖ ≤ A ^ (1 - θ) * (C * q ^ (3 : ℕ)) ^ θ at h
  calc
    ‖f z‖ ≤ _ := h
    _ ≤ A * (C * q ^ ε) := mul_le_mul hApow hBpow
      (Real.rpow_nonneg (mul_nonneg hC0 (pow_nonneg hq0 _)) _) hA0
    _ = _ := by ring

end Chen
