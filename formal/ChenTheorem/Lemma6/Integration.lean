/-
The scalar `ν`-integral common to equations (19) and (20) in Chen's proof.

After the derivative fourth moment is inserted into the `2,4,4` Hölder
bound, both estimates contain

  `(1 + ν²)^(1/4) / (1 + ν⁴)`.

The paper only needs that its integral over `(0, ∞)` is an absolute
constant.  We dominate it by the standard Cauchy kernel.
-/
import ChenTheorem.Lemma6.Equation20
import ChenTheorem.Lemma6.SmoothingMellin
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real MeasureTheory Set

namespace Chen

/-- The fourth power of Chen's smoothing scale is bounded by the fifth
integer power of `log x`. -/
theorem lemma6SmoothingScale_four_le_log_five
    {x : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6SmoothingScale (x : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ 5 := by
  let L : ℝ := Real.log (x : ℝ)
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hL1 : 1 ≤ L := by exact hxlog
  calc
    lemma6SmoothingScale (x : ℝ) ^ 4 =
        (L ^ (1.1 : ℝ)) ^ (4 : ℝ) := by
      unfold lemma6SmoothingScale
      dsimp only [L]
      exact (Real.rpow_natCast _ 4).symm
    _ = L ^ ((1.1 : ℝ) * 4) :=
      (Real.rpow_mul hL0 (1.1 : ℝ) 4).symm
    _ ≤ L ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    _ = Real.log (x : ℝ) ^ 5 := by
      dsimp only [L]
      exact Real.rpow_natCast _ 5

/-- Chen's exact smoothing kernel retains a quartic tail after the contour
is moved to `beta`; the factor `2` bounds the reciprocal real part. -/
theorem norm_lemma6SmoothingMellinKernel_beta_le_two_mul_scale_four
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖ ≤
      2 * lemma6SmoothingScale (x : ℝ) ^ 4 / (1 + nu ^ 4) := by
  let L : ℝ := Real.log (x : ℝ)
  let a : ℝ := lemma6SmoothingScale (x : ℝ)
  let sigma : ℝ := 1 / 2 + 1 / L
  have hL : 0 < L := by dsimp only [L]; linarith
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hL _
  have ha1 : 1 ≤ a := by
    dsimp only [a, lemma6SmoothingScale, L]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hsigma : 0 < sigma := by dsimp only [sigma]; positivity
  have hpoint : lemma6BetaPoint x nu =
      (sigma : ℂ) + (nu : ℂ) * Complex.I := by
    unfold lemma6BetaPoint
    dsimp only [sigma, L]
  have hk := norm_lemma6SmoothingMellinKernel_le_quartic
    ha hn hsigma nu
  rw [← hpoint] at hk
  apply hk.trans
  have hsigmaHalf : (1 / 2 : ℝ) ≤ sigma := by
    dsimp only [sigma]
    have : 0 ≤ (1 : ℝ) / L := by positivity
    linarith
  have hsigmaInv : sigma⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hsigma (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact hsigmaHalf
  have hdenpos : 0 < (1 + (nu / a) ^ 2) ^ 2 := by positivity
  have htargetpos : 0 < 1 + nu ^ 4 := by positivity
  have hscale :
      ((1 + (nu / a) ^ 2) ^ 2)⁻¹ ≤
        a ^ 4 / (1 + nu ^ 4) := by
    rw [le_div_iff₀ htargetpos]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hdenpos).2
    field_simp [ha.ne']
    nlinarith [sq_nonneg nu, sq_nonneg (nu ^ 2),
      sq_nonneg (a ^ 2 - 1)]
  calc
    sigma⁻¹ * ((1 + (nu / a) ^ 2) ^ 2)⁻¹ ≤
        2 * ((1 + (nu / a) ^ 2) ^ 2)⁻¹ := by gcongr
    _ ≤ 2 * (a ^ 4 / (1 + nu ^ 4)) := by gcongr
    _ = 2 * a ^ 4 / (1 + nu ^ 4) := by ring

/-- Integer-log form of the shifted-line kernel bound. -/
theorem norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖ ≤
      2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4) := by
  exact
    (norm_lemma6SmoothingMellinKernel_beta_le_two_mul_scale_four hxlog nu).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (lemma6SmoothingScale_four_le_log_five (by linarith)) (by positivity))
        (by positivity))

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

/-- The shifted `B` block is nonnegative. -/
theorem lemma6BBlockAtBeta_nonneg
    (x m l k H : ℕ) (nu : ℝ) :
    0 ≤ lemma6BBlockAtBeta x m l k H nu := by
  unfold lemma6BBlockAtBeta
  apply Finset.sum_nonneg
  intro d hd
  apply mul_nonneg (lemma6LinearWeight_nonneg d)
  unfold lemma6BModulusTotal
  split_ifs
  · exact le_rfl
  · unfold lemma6BModulus primSum
    exact tsum_nonneg fun chi => by
      split_ifs
      · positivity
      · exact le_rfl

/-- On a genuine dyadic modulus block the shifted `B` block is continuous
in the height.  Only primitive characters survive, and their `L'` is
entire. -/
theorem continuous_lemma6BBlockAtBeta
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (m k H : ℕ) :
    Continuous (lemma6BBlockAtBeta x m l k H) := by
  let beta : ℝ → ℂ := fun nu => lemma6BetaPoint x nu
  have hbeta : Continuous beta := by
    dsimp only [beta]
    unfold lemma6BetaPoint
    fun_prop
  have heq : lemma6BBlockAtBeta x m l k H = fun nu =>
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (beta nu) i *
          lemma6MollifierNorm H (beta nu) i *
          lemma6LDerivNorm (beta nu) i := by
    funext nu
    simpa only [beta] using
      lemma6BBlockAtBeta_eq_characterBlock_sum x m l k H nu
  rw [heq]
  apply continuous_finsetSum
  intro i hi
  have hid : i.1 ∈ lemma6ModulusBlock x l := by
    rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
    exact hi.1
  have hd2 : 2 ≤ i.1 :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hid)).1
  have hd0 : i.1 ≠ 0 := by omega
  by_cases hp : i.2.IsPrimitive
  · have hpair : Continuous (fun nu =>
        lemma6PairBlockNorm x m k (beta nu) i) := by
      unfold lemma6PairBlockNorm
      exact ((differentiable_lemma6PairBlockPolynomial x m k i.2).continuous.comp
        hbeta).norm
    have hmoll : Continuous (fun nu =>
        lemma6MollifierNorm H (beta nu) i) := by
      unfold lemma6MollifierNorm
      exact ((differentiable_lemma6MollifierAt H i.2).continuous.comp hbeta).norm
    have hderiv : Continuous (fun nu =>
        lemma6LDerivNorm (beta nu) i) := by
      letI : NeZero i.1 := ⟨hd0⟩
      simp only [lemma6LDerivNorm, hd0]
      exact ((primitiveCharacter_differentiable_LFunction_deriv hd2 hp).continuous.comp
        hbeta).norm
    exact ((((continuous_const.mul continuous_const).mul hpair).mul hmoll).mul hderiv)
  · have hweight : lemma6PrimitiveBaseWeight i = 0 := by
      simp [lemma6PrimitiveBaseWeight, hp]
    simp only [hweight, zero_mul]
    exact continuous_const

/-- Any standard fourth-moment height bound for the shifted `B` block is
integrable against Chen's exact smoothing kernel.  This is the analytic
reason the factor `(1+nu^2)^(1/4)` in equations (19) and (20) is harmless. -/
theorem integrable_kernelNorm_mul_lemma6BBlockAtBeta_of_le
    {x l : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ))
    (m k H : ℕ) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ nu : ℝ,
      lemma6BBlockAtBeta x m l k H nu ≤
        C * (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) :
    Integrable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu) := by
  let A : ℝ := 2 * Real.log (x : ℝ) ^ 5 * C
  have hmajor : Integrable (fun nu : ℝ => A * lemma6BKernel nu) :=
    integrable_lemma6BKernel.const_mul A
  have hkernel : AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖) := by
    have hlog : 0 < Real.log (x : ℝ) := by linarith
    have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
      unfold lemma6SmoothingScale
      exact Real.rpow_pos_of_pos hlog _
    have hn : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
      unfold lemma6SmoothingOrder
      rw [Nat.one_le_floor_iff]
      linarith
    have hsigma : 0 < (1 / 2 + 1 / Real.log (x : ℝ) : ℝ) := by
      positivity
    have hk := verticalIntegrable_lemma6SmoothingMellinKernel ha hn hsigma
    rw [Complex.VerticalIntegrable] at hk
    have hpoint (nu : ℝ) :
        lemma6BetaPoint x nu =
          ((1 / 2 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) +
            (nu : ℂ) * Complex.I := by
      unfold lemma6BetaPoint
      rfl
    simpa only [hpoint] using hk.norm.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu) :=
    hkernel.mul
      (continuous_lemma6BBlockAtBeta (by linarith) m k H).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards with nu
  have hk := norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five
    hxlog nu
  have hb := hbound nu
  have hB0 := lemma6BBlockAtBeta_nonneg x m l k H nu
  have hnum0 : 0 ≤ (1 + nu ^ 2) ^ ((1 : ℝ) / 4) := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hB0)]
  calc
    ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu ≤
      (2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4)) *
        (C * (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul hk hb hB0 (by positivity)
    _ = A * lemma6BKernel nu := by
      unfold A lemma6BKernel
      ring

end Chen
