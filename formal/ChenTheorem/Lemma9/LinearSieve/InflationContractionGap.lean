import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryChildSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Chen.LinearSieve

/-- The loss combines the child inflation denominator with the logarithmic
error exponent. Both contributions are needed near the initial interval. -/
noncomputable def inflationContractionGap (α x t : ℝ) : ℝ := (x + α / t) / (1 + x)

theorem childAuxiliaryWeight_linear_loss (δ t : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (ht : 1 < t) :
    childAuxiliaryWeight δ t ≤ t - (1 - δ) := by
  have ht0 : 0 < t := by linarith
  have hfrac : -1 ≤ -(1 / t) := by
    have h := (div_le_one ht0).mpr ht.le
    linarith
  have h := rpow_one_add_le_one_add_mul_self hfrac (by linarith : 0 ≤ 1 - δ) (by linarith : 1 - δ ≤ 1)
  have he : 1 + -(1 / t) = (t - 1) / t := by field_simp; ring
  rw [he] at h
  rw [childAuxiliaryWeight_eq_complement_power δ t ht]
  have hm := mul_le_mul_of_nonneg_right h ht0.le
  convert! hm using 1
  field_simp
  ring

theorem inflationContractionGap_bounds (α x t : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hx : 0 ≤ x) (ht : 1 ≤ t) :
    0 ≤ inflationContractionGap α x t ∧ α / t ≤ inflationContractionGap α x t ∧
      inflationContractionGap α x t ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have hb : 0 < 1 + x := by linarith
  have ha : 0 ≤ α / t := div_nonneg hα ht0.le
  have ha1 : α / t ≤ 1 := (div_le_one ht0).mpr (hα1.trans ht)
  refine ⟨div_nonneg (add_nonneg hx ha) hb.le, ?_, ?_⟩
  · rw [inflationContractionGap, le_div_iff₀ hb]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr ha1)]
  · exact (div_le_one hb).mpr (by linarith)

theorem inflationContractionGap_contraction (α x t B : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hx : 0 ≤ x) (ht : 2 ≤ t) (htB : t ≤ B) :
    0 ≤ 1 - α / (4 * B) ∧
      1 - inflationContractionGap α x t ≤
        (1 - α / (4 * B)) * (1 - inflationContractionGap α x t / 2) := by
  have hB : 0 < B := by linarith
  have hg := inflationContractionGap_bounds α x t hα hα1 hx (by linarith)
  have hab : α / B ≤ α / t := div_le_div_of_nonneg_left hα (by linarith) htB
  have hc0 : 0 ≤ α / (4 * B) := by positivity
  have he : α / B = 4 * (α / (4 * B)) := by field_simp
  rw [he] at hab
  constructor
  · linarith [hg.2.1, hg.2.2]
  · nlinarith [mul_nonneg hc0 hg.1]

theorem auxiliaryChildInflation_eq_div (d D t : ℝ) (hD : 1 < D) (ht : 0 ≤ t) :
    auxiliaryChildInflation d D t = auxiliaryInflation d D t / (1 + t ^ d / Real.log D) := by
  have hp := Real.rpow_nonneg ht d
  have hL := Real.log_pos hD
  have hb : 0 < 1 + t ^ d / Real.log D := by positivity
  unfold auxiliaryChildInflation auxiliaryInflation
  rw [Real.rpow_sub hb, Real.rpow_one]

end Chen.LinearSieve
