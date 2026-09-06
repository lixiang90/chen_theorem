import ChenTheorem.Lemma6.ZeroFreeRegionData

open Set Metric

namespace Chen

/-- Moving the height by at most one quarter changes the conductor-height
logarithm by at most a factor of four thirds. -/
theorem conductor_height_log_le (q : ℕ) (hq : 2 ≤ q) (t u : ℝ)
    (htu : |u - t| ≤ 1 / 4) :
    Real.log ((q : ℝ) * (|u| + 2)) ≤ (4 / 3) * Real.log ((q : ℝ) * (|t| + 2)) := by
  let A : ℝ := (q : ℝ) * (|t| + 2)
  let B : ℝ := (q : ℝ) * (|u| + 2)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : B ≤ (9 / 8) * A := by
    have hu : |u| ≤ |t| + 1 / 4 := by
      have := abs_sub_abs_le_abs_sub u t
      linarith
    dsimp [A, B]
    nlinarith [mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ q by positivity),
      mul_nonneg (show (0 : ℝ) ≤ q by positivity) (abs_nonneg t)]
  have hratio : B / A ≤ 9 / 8 := (div_le_iff₀ (by linarith : 0 < A)).mpr hAB
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hB (by linarith : 0 < A))
  rw [Real.log_div hB.ne' (show A ≠ 0 by linarith)] at hlogratio
  have hlogA := Real.one_sub_inv_le_log_of_pos (show 0 < A by linarith)
  have hinv : A⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hA
  change Real.log B ≤ (4 / 3) * Real.log A
  linarith

/-- The mixed zero-free width retains at least three quarters of its value
through a vertical displacement of size at most one quarter. -/
theorem primitiveZeroFreeWidthAt_height_comparison (N : ℕ) (cH cS : ℝ)
    (hcH : 0 ≤ cH) (hcS : 0 ≤ cS) (q : ℕ) (hq : 2 ≤ q) (t u : ℝ)
    (htu : |u - t| ≤ 1 / 4) :
    (3 / 4) * primitiveZeroFreeWidthAt N cH cS q t ≤ primitiveZeroFreeWidthAt N cH cS q u := by
  have hLt := primitiveZeroFreeHeightLog_pos hq t
  have hLu := primitiveZeroFreeHeightLog_pos hq u
  have hlogs := conductor_height_log_le q hq t u htu
  have hfirst : (3 / 4) * (cH / Real.log ((q : ℝ) * (|t| + 2))) ≤
      cH / Real.log ((q : ℝ) * (|u| + 2)) := by
    apply (le_div_iff₀ hLu).mpr
    calc
      _ = ((3 / 4) * cH * Real.log ((q : ℝ) * (|u| + 2))) /
          Real.log ((q : ℝ) * (|t| + 2)) := by ring
      _ ≤ cH := (div_le_iff₀ hLt).mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hlogs hcH])
  have hsecond : (3 / 4) * (cS * (q : ℝ) ^ ((-1 : ℝ) / N)) ≤
      cS * (q : ℝ) ^ ((-1 : ℝ) / N) := by
    nlinarith [mul_nonneg hcS (Real.rpow_nonneg (Nat.cast_nonneg q) ((-1 : ℝ) / N))]
  unfold primitiveZeroFreeWidthAt
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  exact min_le_min hfirst hsecond

end Chen
