import ChenTheorem.Lemma9.LinearSieve.AuxiliaryInflation

namespace Chen.LinearSieve

/-- Both shifts zero and one occur in the quantitative comparison. -/
noncomputable def shiftedAuxiliaryInflation (d D a s : ℝ) : ℝ :=
  (1 + (s + a) ^ d / Real.log D) ^ s

noncomputable def auxiliaryInflationSlope (d D a s : ℝ) : ℝ :=
  Real.log (1 + (s + a) ^ d / Real.log D) +
    d * s * (s + a) ^ (d - 1) / (Real.log D + (s + a) ^ d)

theorem hasDerivAt_shiftedAuxiliaryInflation (d D a s : ℝ)
    (hD : 1 < D) (hs : 0 < s + a) :
    HasDerivAt (shiftedAuxiliaryInflation d D a)
      (shiftedAuxiliaryInflation d D a s * auxiliaryInflationSlope d D a s) s := by
  have hL := Real.log_pos hD
  have hp := Real.rpow_pos_of_pos hs d
  have hb : 0 < 1 + (s + a) ^ d / Real.log D := by positivity
  have hd := (((((hasDerivAt_id s).add_const a).rpow_const
    (p := d) (Or.inl hs.ne')).div_const (Real.log D)).const_add 1).rpow
      (hasDerivAt_id s) hb
  apply hd.congr_deriv
  dsimp only [id_eq, shiftedAuxiliaryInflation, auxiliaryInflationSlope]
  rw [Real.rpow_sub hb, Real.rpow_one]
  field_simp
  ring

theorem auxiliaryInflationSlope_le (d D a s : ℝ)
    (hd : 0 ≤ d) (hD : 1 < D) (ha : 0 ≤ a) (hs : 0 < s) :
    auxiliaryInflationSlope d D a s ≤
      (d + 1) * Real.log (1 + (s + a) ^ d / Real.log D) := by
  have hsa : 0 < s + a := by linarith
  have hL := Real.log_pos hD
  have hp := Real.rpow_pos_of_pos hsa d
  have hden : 0 < Real.log D + (s + a) ^ d := by positivity
  have hb : 0 < 1 + (s + a) ^ d / Real.log D := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hb
  have heq : 1 - (1 + (s + a) ^ d / Real.log D)⁻¹ =
      (s + a) ^ d / (Real.log D + (s + a) ^ d) := by
    field_simp
    ring
  rw [heq] at hlog
  have hmul : s * (s + a) ^ (d - 1) ≤ (s + a) ^ d := by
    rw [Real.rpow_sub hsa, Real.rpow_one, ← mul_div_assoc, div_le_iff₀ hsa]
    nlinarith [mul_nonneg hp.le ha]
  have hnum := mul_le_mul_of_nonneg_left hmul hd
  have hfrac := div_le_div_of_nonneg_right hnum hden.le
  have hlast := mul_le_mul_of_nonneg_left hlog hd
  dsimp only [auxiliaryInflationSlope]
  have heq' : d * ((s + a) ^ d / (Real.log D + (s + a) ^ d)) =
      (d * (s + a) ^ d) / (Real.log D + (s + a) ^ d) := by ring
  rw [heq'] at hlast
  have heq'' : (d * (s * (s + a) ^ (d - 1))) / (Real.log D + (s + a) ^ d) =
      d * s * (s + a) ^ (d - 1) / (Real.log D + (s + a) ^ d) := by ring
  rw [heq''] at hfrac
  nlinarith

theorem deriv_shiftedAuxiliaryInflation_le (d D a s : ℝ)
    (hd : 0 ≤ d) (hD : 1 < D) (ha : 0 ≤ a) (hs : 0 < s) :
    deriv (shiftedAuxiliaryInflation d D a) s ≤
      (d + 1) * shiftedAuxiliaryInflation d D a s *
        Real.log (1 + (s + a) ^ d / Real.log D) := by
  rw [(hasDerivAt_shiftedAuxiliaryInflation d D a s hD (by linarith)).deriv]
  have hp : 0 ≤ shiftedAuxiliaryInflation d D a s := by
    apply Real.rpow_nonneg
    have := div_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ s + a) d) (Real.log_pos hD).le
    linarith
  have hm := mul_le_mul_of_nonneg_left (auxiliaryInflationSlope_le d D a s hd hD ha hs) hp
  calc
    _ ≤ shiftedAuxiliaryInflation d D a s *
        ((d + 1) * Real.log (1 + (s + a) ^ d / Real.log D)) := hm
    _ = _ := by ring

end Chen.LinearSieve
