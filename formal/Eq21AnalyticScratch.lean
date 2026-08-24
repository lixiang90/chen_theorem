import ChenTheorem.Lemma6.Core

open Filter Real MeasureTheory ENNReal Set
open scoped ArithmeticFunction.Moebius Classical

namespace Chen


noncomputable def testEquation21Sigma (x : ℕ) : ℝ :=
  1 - 1 / Real.sqrt (Real.log (x : ℝ))

noncomputable def testEquation21Point (x : ℕ) (ν : ℝ) : ℂ :=
  (testEquation21Sigma x : ℂ) + (ν : ℂ) * Complex.I

theorem test_sigma_half_le {x : ℕ} (hxlog : 4 ≤ Real.log (x : ℝ)) :
    (1 / 2 : ℝ) ≤ testEquation21Sigma x := by
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
    calc
      (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      _ ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_le_sqrt hxlog
  have hsqrtpos : 0 < Real.sqrt (Real.log (x : ℝ)) := by linarith
  unfold testEquation21Sigma
  have hinv : (Real.sqrt (Real.log (x : ℝ)))⁻¹ ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hsqrt
  norm_num at hinv
  simpa only [one_div] using (by linarith :
    (1 / 2 : ℝ) ≤ 1 - (Real.sqrt (Real.log (x : ℝ)))⁻¹)

theorem test_kernel_shift_le_log5
    {x : ℕ} (hxlog : 4 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ) (testEquation21Point x ν)‖ ≤
      2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4) := by
  let L : ℝ := Real.log (x : ℝ)
  let a : ℝ := lemma6SmoothingScale (x : ℝ)
  let σ : ℝ := testEquation21Sigma x
  have hL : 0 < L := by dsimp only [L]; linarith
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hL _
  have ha1 : 1 ≤ a := by
    dsimp only [a, lemma6SmoothingScale, L]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor (by linarith : (3 : ℝ) ≤ Real.log (x : ℝ))
  have hσhalf : (1 / 2 : ℝ) ≤ σ := by
    dsimp only [σ]
    exact test_sigma_half_le hxlog
  have hσ : 0 < σ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hσhalf
  have hpoint : testEquation21Point x ν =
      (σ : ℂ) + (ν : ℂ) * Complex.I := by rfl
  have hk := norm_lemma6SmoothingMellinKernel_le_quartic ha hn hσ ν
  rw [← hpoint] at hk
  apply hk.trans
  have hσInv : σ⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hσ (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact hσhalf
  have hscale := scale_pow_four_inv_quartic_le ha1 ν
  have ha4log : a ^ 4 ≤ Real.log (x : ℝ) ^ 5 :=
    lemma6SmoothingScale_four_le_log_five (by linarith)
  calc
    σ⁻¹ * ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤
        2 * ((1 + (ν / a) ^ 2) ^ 2)⁻¹ := by gcongr
    _ ≤ 2 * (a ^ 4 / (1 + ν ^ 4)) := by gcongr
    _ ≤ 2 * (Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) := by gcongr
    _ = 2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4) := by ring

theorem test_kernel_shift_mul_one_add_sq_le
    {x : ℕ} (hxlog : 4 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ) (testEquation21Point x ν)‖ *
        (1 + ν ^ 2) ≤
      4 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 2) := by
  have hk := test_kernel_shift_le_log5 hxlog ν
  have hden : (0 : ℝ) < 1 + ν ^ 2 := by positivity
  calc
    ‖lemma6SmoothingMellinKernel (x : ℝ) (testEquation21Point x ν)‖ *
        (1 + ν ^ 2) ≤
      (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * (1 + ν ^ 2) := by
        gcongr
    _ = 2 * Real.log (x : ℝ) ^ 5 * ((1 + ν ^ 2) / (1 + ν ^ 4)) := by ring
    _ ≤ 2 * Real.log (x : ℝ) ^ 5 * (2 / (1 + ν ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ν ^ 4) hden]
      simpa only [pow_two] using one_add_sq_sq_le_two_mul_one_add_pow_four ν
    _ = 4 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 2) := by ring

end Chen
