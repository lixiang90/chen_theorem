/-
The scalar `ν`-integral common to equations (19) and (20) in Chen's proof.

After the derivative fourth moment is inserted into the `2,4,4` Hölder
bound, both estimates contain

  `(1 + ν²)^(1/4) / (1 + ν⁴)`.

The paper only needs that its integral over `(0, ∞)` is an absolute
constant.  We dominate it by the standard Cauchy kernel.
-/
import ChenTheorem.Lemma6.Equation20
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real MeasureTheory Set

namespace Chen

/-- The scalar kernel left in the `B` integrals of equations (19) and (20). -/
noncomputable def lemma6BKernel (ν : ℝ) : ℝ :=
  (1 + ν ^ 2) ^ ((1 : ℝ) / 4) / (1 + ν ^ 4)

theorem lemma6BKernel_nonneg (ν : ℝ) : 0 ≤ lemma6BKernel ν := by
  unfold lemma6BKernel
  positivity

theorem continuous_lemma6BKernel : Continuous lemma6BKernel := by
  unfold lemma6BKernel
  exact
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)).comp
        (continuous_const.add (continuous_id.pow 2))).div
      (continuous_const.add (continuous_id.pow 4)) (fun ν => by positivity)

/-- The elementary pointwise comparison used to integrate the kernel:
`(1+ν²)^(1/4)/(1+ν⁴) ≤ 2/(1+ν²)`.
-/
theorem lemma6BKernel_le_cauchy (ν : ℝ) :
    lemma6BKernel ν ≤ 2 * (1 + ν ^ 2)⁻¹ := by
  have hbase : (1 : ℝ) ≤ 1 + ν ^ 2 := by
    nlinarith [sq_nonneg ν]
  have hrpow :
      (1 + ν ^ 2) ^ ((1 : ℝ) / 4) ≤ 1 + ν ^ 2 :=
    Real.rpow_le_self_of_one_le hbase (by norm_num)
  have hden : (0 : ℝ) < 1 + ν ^ 4 := by positivity
  calc
    lemma6BKernel ν ≤ (1 + ν ^ 2) / (1 + ν ^ 4) := by
      exact div_le_div_of_nonneg_right hrpow hden.le
    _ ≤ 2 * (1 + ν ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 1 + ν ^ 2)).2
      nlinarith [sq_nonneg (ν ^ 2 - 1)]

/-- For `log x ≥ 2`, the real part of Chen's `β`-line lies in `[0,1]`, so
its complex norm has the expected scalar bound. -/
theorem lemma6BetaPoint_norm_sq_le
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6BetaPoint x ν‖ ^ 2 ≤ 1 + ν ^ 2 := by
  have hlog : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hxlog
  have hinv : (1 : ℝ) / Real.log x ≤ 1 / 2 := by
    rw [div_le_iff₀ hlog]
    nlinarith
  have hre0 : 0 ≤ (lemma6BetaPoint x ν).re := by
    rw [lemma6BetaPoint_re]
    positivity
  have hre1 : (lemma6BetaPoint x ν).re ≤ 1 := by
    rw [lemma6BetaPoint_re]
    linarith
  rw [Complex.sq_norm, Complex.normSq_apply, lemma6BetaPoint_im]
  nlinarith

/-- The square root of the norm factor supplied by Lemma 3 is exactly
dominated by the numerator of `lemma6BKernel`. -/
theorem lemma6BetaPoint_norm_rpow_half_le
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) ≤
      (1 + ν ^ 2) ^ ((1 : ℝ) / 4) := by
  have hsquare := lemma6BetaPoint_norm_sq_le hxlog ν
  have hrpow := Real.rpow_le_rpow (sq_nonneg ‖lemma6BetaPoint x ν‖)
    hsquare (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
  calc
    ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) =
        ‖lemma6BetaPoint x ν‖ ^ ((2 : ℝ) * ((1 : ℝ) / 4)) := by
      congr 1
      ring
    _ = (‖lemma6BetaPoint x ν‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_mul (norm_nonneg _) _ _
    _ = (‖lemma6BetaPoint x ν‖ ^ 2) ^ ((1 : ℝ) / 4) := by
      rw [Real.rpow_two]
    _ ≤ (1 + ν ^ 2) ^ ((1 : ℝ) / 4) := hrpow

theorem lemma6BetaPoint_norm_kernel_le
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) / (1 + ν ^ 4) ≤
      lemma6BKernel ν := by
  unfold lemma6BKernel
  exact div_le_div_of_nonneg_right
    (lemma6BetaPoint_norm_rpow_half_le hxlog ν) (by positivity)

/-- The actual scalar kernel produced by taking the fourth root of the
Lemma-3 derivative moment. -/
noncomputable def lemma6DerivativeKernel (x : ℕ) (ν : ℝ) : ℝ :=
  ‖lemma6BetaPoint x ν‖ ^ ((1 : ℝ) / 2) / (1 + ν ^ 4)

theorem continuous_lemma6DerivativeKernel (x : ℕ) :
    Continuous (lemma6DerivativeKernel x) := by
  have hbeta : Continuous (fun ν : ℝ => lemma6BetaPoint x ν) := by
    unfold lemma6BetaPoint
    fun_prop
  unfold lemma6DerivativeKernel
  exact
    ((continuous_norm.comp hbeta).rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2))).div
        (continuous_const.add (continuous_id.pow 4)) (fun ν => by positivity)

theorem lemma6DerivativeKernel_nonneg (x : ℕ) (ν : ℝ) :
    0 ≤ lemma6DerivativeKernel x ν := by
  unfold lemma6DerivativeKernel
  positivity

theorem integrable_lemma6BKernel : Integrable lemma6BKernel := by
  apply (Integrable.const_mul integrable_inv_one_add_sq 2).mono_nonneg
      continuous_lemma6BKernel.aestronglyMeasurable
  · exact ae_of_all _ lemma6BKernel_nonneg
  · exact ae_of_all _ lemma6BKernel_le_cauchy

theorem integrable_lemma6DerivativeKernel
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) :
    Integrable (lemma6DerivativeKernel x) := by
  apply integrable_lemma6BKernel.mono_nonneg
      (continuous_lemma6DerivativeKernel x).aestronglyMeasurable
  · exact ae_of_all _ (lemma6DerivativeKernel_nonneg x)
  · exact ae_of_all _ (lemma6BetaPoint_norm_kernel_le hxlog)

/-- The precise absolute constant needed after equations (19) and (20).
The paper only records convergence; the convenient bound `π` is enough. -/
theorem integral_Ioi_lemma6BKernel_le_pi :
    ∫ ν in Ioi (0 : ℝ), lemma6BKernel ν ≤ Real.pi := by
  calc
    ∫ ν in Ioi (0 : ℝ), lemma6BKernel ν ≤
        ∫ ν in Ioi (0 : ℝ), 2 * (1 + ν ^ 2)⁻¹ := by
      exact setIntegral_mono
        integrable_lemma6BKernel.integrableOn
        (Integrable.const_mul integrable_inv_one_add_sq 2).integrableOn
        lemma6BKernel_le_cauchy
    _ = Real.pi := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_inv_one_add_sq]
      rw [Real.arctan_zero]
      ring

theorem integral_Ioi_lemma6DerivativeKernel_le_pi
    {x : ℕ} (hxlog : 2 ≤ Real.log (x : ℝ)) :
    ∫ ν in Ioi (0 : ℝ), lemma6DerivativeKernel x ν ≤ Real.pi := by
  exact (setIntegral_mono
      (integrable_lemma6DerivativeKernel hxlog).integrableOn
      integrable_lemma6BKernel.integrableOn
      (lemma6BetaPoint_norm_kernel_le hxlog)).trans
    integral_Ioi_lemma6BKernel_le_pi

end Chen
