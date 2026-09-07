import Submission.ChenTheorem.Lemma9.LinearSieve.ComparisonEnvelope

set_option autoImplicit true
namespace Chen.LinearSieve

noncomputable def depthMassLevelConstant (K : ℝ) : ℝ :=
  1 + (1 + K / Real.log 2) / Real.log 2

theorem depthMassLevelConstant_ge_one (K : ℝ) (hK : 0 < K) :
    1 ≤ depthMassLevelConstant K := by
  have hL := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold depthMassLevelConstant
  have : 0 ≤ (1 + K / Real.log 2) / Real.log 2 := by positivity
  linarith

/-- The cutoff-dependent mass is bounded by a fixed multiple of `log D`
once the sieve parameter is at least one. -/
theorem depthMassMajorant_le_log_level (K D z : ℝ) (hK : 0 < K) (hD : 1 < D)
    (hz : 2 ≤ z) (hs : 1 ≤ sieveParameter D (z + 1)) :
    depthMassMajorant K z ≤ depthMassLevelConstant K * Real.log D := by
  have hL2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hz0 : 0 < z := by linarith
  have hz1 : 1 < z + 1 := by linarith
  have hlz : Real.log (z + 1) ≤ Real.log D := by
    have h := (le_div_iff₀ (Real.log_pos hz1)).mp hs
    simpa only [one_mul] using h
  have hzlog := (Real.log_le_log hz0 (by linarith : z ≤ z + 1)).trans hlz
  have hcoeff : 0 ≤ (1 + K / Real.log 2) / Real.log 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hzlog hcoeff
  unfold depthMassMajorant depthMassLevelConstant
  have hL := (Real.log_pos hD).le
  nlinarith [show (1 + K / Real.log 2) * (Real.log z / Real.log 2) =
    ((1 + K / Real.log 2) / Real.log 2) * Real.log z by ring]

end Chen.LinearSieve
