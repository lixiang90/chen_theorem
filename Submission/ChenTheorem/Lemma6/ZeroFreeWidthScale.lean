import Submission.ChenTheorem.Lemma6.ZeroFreeRegionDisks

set_option autoImplicit true
namespace Chen

noncomputable def primitiveZeroFreeScaleAt (N q : ℕ) (t : ℝ) : ℝ :=
  (q : ℝ) ^ ((1 : ℝ) / N) + Real.log ((q : ℝ) * (|t| + 2)) + 1

theorem conductor_height_log_ge_threeQuarters (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    (3 / 4 : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < (q : ℝ) * (|t| + 2) by linarith)
  have hinv : ((q : ℝ) * (|t| + 2))⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hA
  linarith

theorem primitiveZeroFreeWidthAt_le_quarter (N : ℕ) (cH cS : ℝ)
    (hcH : cH ≤ 1 / 8) (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    primitiveZeroFreeWidthAt N cH cS q t ≤ 1 / 4 := by
  apply (min_le_left _ _).trans
  apply (div_le_iff₀ (primitiveZeroFreeHeightLog_pos hq t)).mpr
  linarith [conductor_height_log_ge_threeQuarters q hq t]

/-- The reciprocal mixed width is controlled by the exact scale appearing
in the requested global logarithmic-derivative bound. -/
theorem inv_primitiveZeroFreeWidthAt_le_scale (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcS : 0 < cS) (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    1 / primitiveZeroFreeWidthAt N cH cS q t ≤
      (1 / cH + 1 / cS) * primitiveZeroFreeScaleAt N q t := by
  have hL := primitiveZeroFreeHeightLog_pos hq t
  have hQ := Real.rpow_pos_of_pos (show (0 : ℝ) < q by exact_mod_cast (show 0 < q by omega)) ((1 : ℝ) / N)
  have hSL : Real.log ((q : ℝ) * (|t| + 2)) ≤ primitiveZeroFreeScaleAt N q t := by
    unfold primitiveZeroFreeScaleAt
    linarith
  have hSQ : (q : ℝ) ^ ((1 : ℝ) / N) ≤ primitiveZeroFreeScaleAt N q t := by
    unfold primitiveZeroFreeScaleAt
    linarith
  by_cases hm : cH / Real.log ((q : ℝ) * (|t| + 2)) ≤ cS * (q : ℝ) ^ ((-1 : ℝ) / N)
  · rw [primitiveZeroFreeWidthAt, min_eq_left hm, one_div_div]
    calc
      _ = (1 / cH) * Real.log ((q : ℝ) * (|t| + 2)) := by ring
      _ ≤ _ := mul_le_mul (by linarith [one_div_pos.mpr hcS]) hSL hL.le (by positivity)
  · rw [primitiveZeroFreeWidthAt, min_eq_right (le_of_not_ge hm)]
    have he : 1 / (cS * (q : ℝ) ^ ((-1 : ℝ) / N)) = (1 / cS) * (q : ℝ) ^ ((1 : ℝ) / N) := by
      rw [show (-1 : ℝ) / N = -((1 : ℝ) / N) by ring,
        Real.rpow_neg (Nat.cast_nonneg q)]
      field_simp
    rw [he]
    exact mul_le_mul (by linarith [one_div_pos.mpr hcH]) hSQ hQ.le (by positivity)

theorem zeroFreeDiskCenter_norm_add_radius_le (R t : ℝ) (hR : 0 < R) (hRsmall : R ≤ 1 / 4) :
    ‖zeroFreeDiskCenter R t‖ + R ≤ |t| + 3 := by
  have hc : ‖zeroFreeDiskCenter R t‖ ≤ 1 + R / 4 + |t| := by
    unfold zeroFreeDiskCenter
    calc
      _ ≤ ‖((1 + R / 4 : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, abs_of_pos (show 0 < 1 + R / 4 by linarith)]
  linarith

end Chen
