/-
Scalar vertical masses of Chen's smoothing kernel on the `alpha` and
`beta` lines, in the shape required by the final assembly of equations
(19) and (20) in Lemma 6.

The kernel decays like `(1 + nu^4)^{-1}` along both lines, so multiplying
it by the polynomial-height factors produced by the Hoelder moment bounds
still leaves an integrable function whose integral is an absolute constant
times `(log x)^5`.
-/
import ChenTheorem.Lemma6.Integration
import ChenTheorem.Lemma6.Parameters

open Real MeasureTheory Filter

namespace Chen

/-! ### Elementary quadratic domination facts -/

theorem one_add_sq_sq_le_two_mul_one_add_pow_four (nu : ℝ) :
    (1 + nu ^ 2) ^ 2 ≤ 2 * (1 + nu ^ 4) := by
  nlinarith [sq_nonneg (nu ^ 2 - 1)]

/-! ### Measurability of the vertical kernel norms -/

theorem aestronglyMeasurable_norm_kernel_alpha
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖) volume := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hxlog
  have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlogpos _
  have hn : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    linarith
  have hsigma : (0 : ℝ) < 1 + 1 / Real.log (x : ℝ) := by positivity
  have hk := verticalIntegrable_lemma6SmoothingMellinKernel ha hn hsigma
  rw [Complex.VerticalIntegrable] at hk
  refine hk.norm.aestronglyMeasurable.congr ?_
  filter_upwards with nu
  unfold lemma6AlphaPoint
  rfl

theorem aestronglyMeasurable_norm_kernel_beta
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖) volume := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hxlog
  have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlogpos _
  have hn : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    linarith
  have hsigma : (0 : ℝ) < 1 / 2 + 1 / Real.log (x : ℝ) := by positivity
  have hk := verticalIntegrable_lemma6SmoothingMellinKernel ha hn hsigma
  rw [Complex.VerticalIntegrable] at hk
  refine hk.norm.aestronglyMeasurable.congr ?_
  filter_upwards with nu
  unfold lemma6BetaPoint
  rfl

/-! ### Pointwise domination of the weighted kernel norms -/

/-- The elementary dyadic-tail comparison: enlarging the smoothing scale
to its fourth power dominates the quartic Cauchy denominator. -/
theorem scale_pow_four_inv_quartic_le {a : ℝ} (ha1 : 1 ≤ a) (nu : ℝ) :
    ((1 + (nu / a) ^ 2) ^ 2)⁻¹ ≤ a ^ 4 / (1 + nu ^ 4) := by
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha1
  have hden : (0 : ℝ) < 1 + nu ^ 4 := by positivity
  have hdenpos : (0 : ℝ) < (1 + (nu / a) ^ 2) ^ 2 := by positivity
  rw [inv_eq_one_div,
    div_le_div_iff₀ hdenpos hden]
  have h21 : (1 : ℝ) ≤ a ^ 2 := by nlinarith
  have h41 : (1 : ℝ) ≤ a ^ 4 := by nlinarith [sq_nonneg (a ^ 2 - 1)]
  have hcross : (0 : ℝ) ≤ 2 * a ^ 2 * nu ^ 2 := by positivity
  have hexpr : a ^ 4 * ((1 + (nu / a) ^ 2) ^ 2) = (a ^ 2 + nu ^ 2) ^ 2 := by
    field_simp
  calc 1 * (1 + nu ^ 4) ≤ a ^ 4 + 2 * a ^ 2 * nu ^ 2 + nu ^ 4 := by linarith
    _ ≤ a ^ 4 * ((1 + (nu / a) ^ 2) ^ 2) := by
        rw [hexpr]; nlinarith

/-- The exact smoothing kernel on Chen's `alpha`-line has a quartic tail
with the natural smoothing scale as numerator.  This is the copy of the
corresponding `Core` estimate that does not depend on `Core`. -/
theorem norm_lemma6Kernel_alpha_le_scale_four
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x nu)‖ ≤
      lemma6SmoothingScale (x : ℝ) ^ 4 / (1 + nu ^ 4) := by
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hxlog
  have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hL _
  have ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hsigma : 0 < (1 + 1 / Real.log (x : ℝ) : ℝ) := by positivity
  have hpoint : lemma6AlphaPoint x nu =
      ((1 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) + (nu : ℂ) * Complex.I := by
    unfold lemma6AlphaPoint
    rfl
  have hk := norm_lemma6SmoothingMellinKernel_le_quartic ha hn hsigma nu
  rw [← hpoint] at hk
  refine hk.trans ?_
  have hposlog : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := by positivity
  have hsigmaInv : (1 + 1 / Real.log (x : ℝ))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    linarith
  calc
    (1 + 1 / Real.log (x : ℝ))⁻¹ *
        ((1 + (nu / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ ≤
        1 * ((1 + (nu / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
      gcongr
    _ = ((1 + (nu / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by ring
    _ ≤ lemma6SmoothingScale (x : ℝ) ^ 4 / (1 + nu ^ 4) :=
        scale_pow_four_inv_quartic_le ha1 nu

/-- The integer-log form of the rigorous `alpha`-line kernel majorant. -/
theorem norm_lemma6Kernel_alpha_le_log_five
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x nu)‖ ≤
      Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4) := by
  exact (norm_lemma6Kernel_alpha_le_scale_four hxlog nu).trans
    (div_le_div_of_nonneg_right
      (lemma6SmoothingScale_four_le_log_five (by linarith)) (by positivity))

/-- On the `alpha`-line the smoothing kernel against the quadratic height
factor is dominated by a multiple of the Cauchy kernel. -/
theorem norm_kernel_alpha_mul_one_add_sq_le
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
        (1 + nu ^ 2) ≤
      2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 2) := by
  have hk := norm_lemma6Kernel_alpha_le_log_five hxlog nu
  have hden : (0 : ℝ) < 1 + nu ^ 2 := by positivity
  calc ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
        (1 + nu ^ 2) ≤
      Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4) * (1 + nu ^ 2) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
    _ = Real.log (x : ℝ) ^ 5 * ((1 + nu ^ 2) / (1 + nu ^ 4)) := by ring
    _ ≤ Real.log (x : ℝ) ^ 5 * (2 / (1 + nu ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + nu ^ 4) hden]
        simpa only [pow_two] using one_add_sq_sq_le_two_mul_one_add_pow_four nu
    _ = 2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 2) := by ring

/-- Same domination on the shifted `beta`-line, with the extra factor two
coming from the smaller real part. -/
theorem norm_kernel_beta_mul_one_add_sq_le
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        (1 + nu ^ 2) ≤
      4 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 2) := by
  have hk := norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five hxlog nu
  have hden : (0 : ℝ) < 1 + nu ^ 2 := by positivity
  calc ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        (1 + nu ^ 2) ≤
      2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4) * (1 + nu ^ 2) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
    _ = 2 * Real.log (x : ℝ) ^ 5 * ((1 + nu ^ 2) / (1 + nu ^ 4)) := by ring
    _ ≤ 2 * Real.log (x : ℝ) ^ 5 * (2 / (1 + nu ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + nu ^ 4) hden]
        simpa only [pow_two] using one_add_sq_sq_le_two_mul_one_add_pow_four nu
    _ = 4 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 2) := by ring

/-! ### Integrability and integral values -/

theorem integrable_kernelNorm_alpha_mul_one_add_sq
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    Integrable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
        (1 + nu ^ 2)) := by
  refine Integrable.mono
    (g := fun nu : ℝ => 2 * Real.log (x : ℝ) ^ 5 * (1 + nu ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul (2 * Real.log (x : ℝ) ^ 5))
    ((aestronglyMeasurable_norm_kernel_alpha hxlog).mul
      ((continuous_const.add (continuous_id.pow 2)).aestronglyMeasurable)) ?_
  filter_upwards with nu
  have h1 : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
      (lemma6AlphaPoint x nu)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 1 + nu ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_kernel_alpha_mul_one_add_sq_le hxlog nu

theorem integrable_kernelNorm_beta_mul_one_add_sq
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    Integrable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        (1 + nu ^ 2)) := by
  refine Integrable.mono
    (g := fun nu : ℝ => 4 * Real.log (x : ℝ) ^ 5 * (1 + nu ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul (4 * Real.log (x : ℝ) ^ 5))
    ((aestronglyMeasurable_norm_kernel_beta hxlog).mul
      ((continuous_const.add (continuous_id.pow 2)).aestronglyMeasurable)) ?_
  filter_upwards with nu
  have h1 : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
      (lemma6BetaPoint x nu)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 1 + nu ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_kernel_beta_mul_one_add_sq_le hxlog nu

/-- The full-line `alpha`-kernel quadratic mass: an absolute constant times
the fifth power of the logarithm. -/
theorem integral_kernelNorm_alpha_mul_one_add_sq_le
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
          (1 + nu ^ 2)) ≤
      2 * Real.pi * Real.log (x : ℝ) ^ 5 := by
  have hint := integrable_kernelNorm_alpha_mul_one_add_sq hxlog
  have hmaj := integrable_inv_one_add_sq.const_mul
    (2 * Real.log (x : ℝ) ^ 5)
  have hmono := MeasureTheory.integral_mono hint hmaj
    (fun nu => norm_kernel_alpha_mul_one_add_sq_le hxlog nu)
  calc (∫ nu : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
            (1 + nu ^ 2)) ≤
        ∫ nu : ℝ, 2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 2) := hmono
      _ = 2 * Real.pi * Real.log (x : ℝ) ^ 5 := by
        have hstep : (∫ nu : ℝ, 2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 2)) =
            ∫ nu : ℝ, (2 * Real.log (x : ℝ) ^ 5) * (1 + nu ^ 2)⁻¹ := by
          simp only [div_eq_mul_inv]
        rw [hstep, MeasureTheory.integral_const_mul,
          integral_univ_inv_one_add_sq]
        ring

/-! ### The crude scalar majorant for the equation-(14) remainder -/

/-- The squared norm of Chen's `α`-line point. -/
theorem norm_sq_lemma6AlphaPoint_le
    {x : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6AlphaPoint x ν‖ ^ 2 ≤ 4 * (1 + ν ^ 2) := by
  have hlog : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
  have him : (lemma6AlphaPoint x ν).im = ν := by
    change 0 + (ν * 1 + 0 * 0) = ν
    ring
  rw [Complex.sq_norm, Complex.normSq_apply, lemma6AlphaPoint_re, him]
  have h1 : 1 / Real.log (x : ℝ) ≤ 1 := by
    rw [div_le_one hlog]
    exact hxlog
  have h2 : 0 < 1 / Real.log (x : ℝ) := by positivity
  have hu2 : (1 / Real.log (x : ℝ)) ^ 2 ≤ 1 := pow_le_one₀ h2.le h1
  nlinarith [sq_nonneg ν, h2, hu2]

/-- The integer dyadic logarithm against the real logarithm. -/
theorem natLog_two_add_one_le_three_mul_log
    {H : ℕ} (hH : 1 ≤ H) (hlogH : 1 ≤ Real.log (H : ℝ)) :
    (Nat.log 2 H : ℝ) + 1 ≤ 3 * Real.log (H : ℝ) := by
  have h := natLog_two_cast_le hH
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h1 := Real.log_two_gt_d9
    linarith
  have hkey : Real.log (H : ℝ) ≤ 2 * Real.log (H : ℝ) * Real.log 2 := by
    have h2 := mul_le_mul_of_nonneg_right hlog2
      (show (0 : ℝ) ≤ Real.log (H : ℝ) by linarith)
    nlinarith [h2]
  calc
    (Nat.log 2 H : ℝ) + 1 ≤ Real.log (H : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ 2 * Real.log (H : ℝ) + 1 := by
      have h3 : Real.log (H : ℝ) / Real.log 2 ≤ 2 * Real.log (H : ℝ) := by
        rw [div_le_iff₀ hlog2pos]
        linarith
      linarith
    _ ≤ 3 * Real.log (H : ℝ) := by linarith

/-- Crude scale bound for the equation-(14) remainder majorant: all
logarithmic factors are collected into `(log x)^3 (log H)^2` and the
dyadic dependence into the three displayed terms. -/
theorem lemma6RemainderSecondMajorant_le_crude
    {Cp Ct : ℝ} (hCp : 0 < Cp) (hCt : 0 < Ct)
    {x l H : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (hl : 1 ≤ l) (hH : 1 ≤ H)
    (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hlogH : 1 ≤ Real.log (H : ℝ))
    (hlogHH : Real.log ((2 * H * H : ℕ) : ℝ) ≤ 8 * Real.log (x : ℝ))
    (hlogQ : Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
      2 * Real.log (x : ℝ))
    (ν : ℝ) :
    lemma6RemainderSecondMajorant Cp Ct x l H ν ≤
      (36864 * Cp + 200 * Ct ^ 2) * Real.log (x : ℝ) ^ 3 *
        Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
  have hP0 : (0 : ℝ) < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
  have hP : 1 ≤ Real.log (x : ℝ) := hxlog
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlogH
  have hDpos : 0 < lemma6DyadicModulusScale x l := by
    unfold lemma6DyadicModulusScale
    positivity
  have hQge : lemma6DyadicModulusScale x l ≤ (lemma6ModulusCutoff x l : ℝ) :=
    lemma6DyadicModulusScale_le_modulusCutoff x l
  have hQ54 : (lemma6ModulusCutoff x l : ℝ) ≤
      5 / 4 * lemma6DyadicModulusScale x l :=
    lemma6ModulusCutoff_cast_le_five_quarters_scale hD4
  have hR : lemma6DyadicModulusScale x l / 4 ≤
      (lemma6ModulusLowerCutoff x l : ℝ) :=
    lemma6_quarter_scale_le_modulusLowerCutoff hl hD4
  have hRpos : (0 : ℝ) < (lemma6ModulusLowerCutoff x l : ℝ) :=
    (div_pos hDpos (by norm_num)).trans_le hR
  have hRinv : (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
      4 / lemma6DyadicModulusScale x l := by
    have h := one_div_le_one_div_of_le (div_pos hDpos (by norm_num)) hR
    rw [one_div, one_div, inv_div] at h
    exact h
  have hnl : (Nat.log 2 H : ℝ) + 1 ≤ 3 * Real.log (H : ℝ) :=
    natLog_two_add_one_le_three_mul_log hH hlogH
  have hL20 : 0 ≤ Real.log ((2 * H * H : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * H * H by nlinarith [hH]))
  have hL2pow : Real.log ((2 * H * H : ℕ) : ℝ) ^ 3 ≤
      (8 * Real.log (x : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hL20 hlogHH 3
  have hL30 : 0 ≤ Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) :=
    Real.log_nonneg (by linarith [hQge, hD4])
  have hL3pow : Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2 ≤
      (2 * Real.log (x : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hL30 hlogQ 2
  have hnormsq : ‖lemma6AlphaPoint x ν‖ ^ 2 ≤ 4 * (1 + ν ^ 2) :=
    norm_sq_lemma6AlphaPoint_le hxlog ν
  have hharm0 : (0 : ℝ) ≤ (harmonic H : ℝ) := by
    have h : (0 : ℚ) ≤ harmonic H := by
      rw [harmonic_eq_sum_Icc]
      exact Finset.sum_nonneg fun i _ => by positivity
    exact_mod_cast h
  have hharm : (harmonic H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
    have h := harmonic_le_one_add_log H
    linarith
  have hinner0 : 0 ≤ 2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
      ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ := by
    positivity
  have hinner : 2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
        ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
      (5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
        12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l := by
    have e1 : 2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) ≤
        (5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) := by
      rw [show (5 / 2 : ℝ) * (lemma6DyadicModulusScale x l / (H : ℝ)) =
          (5 / 2 * lemma6DyadicModulusScale x l) / (H : ℝ) by ring]
      rw [div_le_div_iff_of_pos_right hHpos]
      nlinarith [hQ54]
    have e2 : ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
        12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l := by
      have h2 := mul_le_mul hnl hRinv (inv_nonneg.mpr hRpos.le)
        (by linarith : (0 : ℝ) ≤ 3 * Real.log (H : ℝ))
      calc ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
          (3 * Real.log (H : ℝ)) * (4 / lemma6DyadicModulusScale x l) := h2
        _ = 12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l := by ring
    exact add_le_add e1 e2
  have hpart1 :
      2 * (Cp * ((Nat.log 2 H : ℝ) + 1) *
          (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
            ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) *
          Real.log ((2 * H * H : ℕ) : ℝ) ^ 3) ≤
        36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
    have hcore : Cp * ((Nat.log 2 H : ℝ) + 1) *
          (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
            ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) *
          Real.log ((2 * H * H : ℕ) : ℝ) ^ 3 ≤
        Cp * (3 * Real.log (H : ℝ)) *
          ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
            12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l) *
          (8 * Real.log (x : ℝ)) ^ 3 := by
      have s1 : Cp * ((Nat.log 2 H : ℝ) + 1) ≤ Cp * (3 * Real.log (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hnl hCp.le
      have s2 : Cp * ((Nat.log 2 H : ℝ) + 1) *
            (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
              ((Nat.log 2 H : ℝ) + 1) *
                (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) ≤
          Cp * (3 * Real.log (H : ℝ)) *
            ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l) :=
        mul_le_mul s1 hinner hinner0 (by positivity)
      exact mul_le_mul s2 hL2pow (pow_nonneg hL20 3) (by positivity)
    calc 2 * (Cp * ((Nat.log 2 H : ℝ) + 1) *
          (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
            ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) *
          Real.log ((2 * H * H : ℕ) : ℝ) ^ 3)
        ≤ 2 * (Cp * (3 * Real.log (H : ℝ)) *
            ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l) *
            (8 * Real.log (x : ℝ)) ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hcore
      _ = 3072 * Cp * Real.log (x : ℝ) ^ 3 *
            (Real.log (H : ℝ) * ((5 / 2) *
                (lemma6DyadicModulusScale x l / (H : ℝ))) +
              12 * Real.log (H : ℝ) ^ 2 / lemma6DyadicModulusScale x l) := by
          field_simp [hDpos.ne', hHpos.ne']
          ring
      _ ≤ 3072 * Cp * Real.log (x : ℝ) ^ 3 *
            (Real.log (H : ℝ) ^ 2 * ((5 / 2) *
                (lemma6DyadicModulusScale x l / (H : ℝ))) +
              12 * Real.log (H : ℝ) ^ 2 / lemma6DyadicModulusScale x l) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hLHsq : Real.log (H : ℝ) ≤ Real.log (H : ℝ) ^ 2 := by
            have hsq : Real.log (H : ℝ) * 1 ≤
                Real.log (H : ℝ) * Real.log (H : ℝ) :=
              mul_le_mul_of_nonneg_left hlogH hlogH0.le
            simpa only [pow_two, mul_one] using hsq
          exact add_le_add
            (mul_le_mul_of_nonneg_right hLHsq (by positivity)) le_rfl
      _ = 3072 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 / lemma6DyadicModulusScale x l) := by ring
      _ ≤ 3072 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (12 * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 * (1 / lemma6DyadicModulusScale x l)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          · exact le_of_eq (by ring)
      _ = 36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l) := by ring
      _ ≤ 36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_right (by positivity)
  have hsq : (Ct * ‖lemma6AlphaPoint x ν‖ *
        Real.sqrt (lemma6ModulusCutoff x l : ℝ) *
        Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) / (H : ℝ)) ^ 2 ≤
      Ct ^ 2 * (4 * (1 + ν ^ 2)) * (lemma6ModulusCutoff x l : ℝ) *
        (2 * Real.log (x : ℝ)) ^ 2 / (H : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ (lemma6ModulusCutoff x l : ℝ) by positivity)]
    have h2 : Ct ^ 2 * ‖lemma6AlphaPoint x ν‖ ^ 2 *
          (lemma6ModulusCutoff x l : ℝ) *
          Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2 ≤
        Ct ^ 2 * (4 * (1 + ν ^ 2)) * (lemma6ModulusCutoff x l : ℝ) *
          (2 * Real.log (x : ℝ)) ^ 2 := by
      have t1 : ‖lemma6AlphaPoint x ν‖ ^ 2 *
            Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2 ≤
          (4 * (1 + ν ^ 2)) * (2 * Real.log (x : ℝ)) ^ 2 :=
        mul_le_mul hnormsq hL3pow (sq_nonneg _) (by positivity)
      calc Ct ^ 2 * ‖lemma6AlphaPoint x ν‖ ^ 2 *
              (lemma6ModulusCutoff x l : ℝ) *
              Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2
          = Ct ^ 2 * (lemma6ModulusCutoff x l : ℝ) *
              (‖lemma6AlphaPoint x ν‖ ^ 2 *
                Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2) := by ring
        _ ≤ Ct ^ 2 * (lemma6ModulusCutoff x l : ℝ) *
              ((4 * (1 + ν ^ 2)) * (2 * Real.log (x : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left t1 (by positivity)
        _ = Ct ^ 2 * (4 * (1 + ν ^ 2)) * (lemma6ModulusCutoff x l : ℝ) *
              (2 * Real.log (x : ℝ)) ^ 2 := by ring
    exact (div_le_div_iff_of_pos_right
      (by positivity : (0 : ℝ) < (H : ℝ) ^ 2)).2 h2
  have hpart2 : (lemma6ModulusCutoff x l : ℝ) *
        (2 * ((Ct * ‖lemma6AlphaPoint x ν‖ *
            Real.sqrt (lemma6ModulusCutoff x l : ℝ) *
            Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) / (H : ℝ)) ^ 2 *
          (harmonic H : ℝ) ^ 2)) ≤
        200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
    have h1 : (harmonic H : ℝ) ^ 2 ≤ (2 * Real.log (H : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hharm0 hharm 2
    calc (lemma6ModulusCutoff x l : ℝ) *
          (2 * ((Ct * ‖lemma6AlphaPoint x ν‖ *
              Real.sqrt (lemma6ModulusCutoff x l : ℝ) *
              Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) / (H : ℝ)) ^ 2 *
            (harmonic H : ℝ) ^ 2))
        ≤ (5 / 4 * lemma6DyadicModulusScale x l) *
            (2 * ((Ct ^ 2 * (4 * (1 + ν ^ 2)) *
                (lemma6ModulusCutoff x l : ℝ) *
                (2 * Real.log (x : ℝ)) ^ 2 / (H : ℝ) ^ 2) *
              (2 * Real.log (H : ℝ)) ^ 2)) := by
          apply mul_le_mul hQ54 _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hsq h1 (by positivity) (by positivity)
      _ = 160 * Ct ^ 2 *
            (lemma6DyadicModulusScale x l * (lemma6ModulusCutoff x l : ℝ)) *
            (Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by
          field_simp [hHpos.ne']
          ring
      _ ≤ 160 * Ct ^ 2 *
            (lemma6DyadicModulusScale x l *
              (5 / 4 * lemma6DyadicModulusScale x l)) *
            (Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ54 hDpos.le
      _ = 200 * Ct ^ 2 * lemma6DyadicModulusScale x l ^ 2 *
            (Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by ring
      _ ≤ 200 * Ct ^ 2 * lemma6DyadicModulusScale x l ^ 2 *
            (Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hP23 : Real.log (x : ℝ) ^ 2 ≤ Real.log (x : ℝ) ^ 3 :=
            pow_le_pow_right₀ hP (by norm_num)
          rw [show Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
                (1 + ν ^ 2) / (H : ℝ) ^ 2 =
              Real.log (x : ℝ) ^ 2 *
                (Real.log (H : ℝ) ^ 2 * (1 + ν ^ 2) / (H : ℝ) ^ 2) by ring,
            show Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
                (1 + ν ^ 2) / (H : ℝ) ^ 2 =
              Real.log (x : ℝ) ^ 3 *
                (Real.log (H : ℝ) ^ 2 * (1 + ν ^ 2) / (H : ℝ) ^ 2) by ring]
          exact mul_le_mul_of_nonneg_right hP23 (by positivity)
      _ = 200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            ((1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
          ring
      _ ≤ 200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_left (by positivity)
  unfold lemma6RemainderSecondMajorant
  rw [show (36864 * Cp + 200 * Ct ^ 2) * Real.log (x : ℝ) ^ 3 *
        Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) =
      36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) +
        200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) by
      ring]
  exact add_le_add hpart1 hpart2


/-! ### Square-root algebra helpers -/

theorem real_sqrt_add_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt (p + q) ≤ Real.sqrt p + Real.sqrt q := by
  have h1 : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg p
  have h2 : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg q
  have h3 : (0 : ℝ) ≤ 2 * Real.sqrt p * Real.sqrt q :=
    mul_nonneg (mul_nonneg zero_le_two h1) h2
  have e1 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp
  have e2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  have key : (p + q) ≤ (Real.sqrt p + Real.sqrt q) ^ 2 := by
    rw [add_pow_two]
    nlinarith [e1, e2, h3]
  calc Real.sqrt (p + q) ≤
        Real.sqrt ((Real.sqrt p + Real.sqrt q) ^ 2) := Real.sqrt_le_sqrt key
      _ = Real.sqrt p + Real.sqrt q := by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (add_nonneg h1 h2)]

theorem real_sqrt_three_le (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    Real.sqrt (p + q + r) ≤ Real.sqrt p + Real.sqrt q + Real.sqrt r := by
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have h := real_sqrt_add_le hpq hr
  have h' := real_sqrt_add_le hp hq
  exact h.trans (add_le_add h' (le_refl _))

theorem real_le_sqrt_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (hab : a * a ≤ b) :
    a ≤ Real.sqrt b := by
  rw [← Real.sqrt_mul_self ha]
  exact Real.sqrt_le_sqrt hab

/-- Pointwise majorization transfer into a scalar multiple of the
quadratic height factor, on the model of equations (19) and (20). -/
theorem ablock_majorant
    {x l m k H : ℕ} {Cpair CremP CremT : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 < CremP) (hCremT : 0 < CremT)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k)
    (hH1 : 1 ≤ H) (hxlogH : 1 ≤ Real.log (H : ℝ))
    (hlogHH : Real.log ((2 * H * H : ℕ) : ℝ) ≤ 8 * Real.log (x : ℝ))
    (hlogQ : Real.log (2 * (lemma6ModulusCutoff x l : ℕ)) ≤
      2 * Real.log (x : ℝ))
    (ν : ℝ)
    (hsq : lemma6ABlockAtAlpha x m l k H ν ^ 2 ≤
        (lemma6ExceptionalFactorAt x l *
            (Cpair * lemma6PairSecondMajorant x l m k
              (lemma6AlphaPoint x ν))) *
          lemma6RemainderSecondMajorant CremP CremT x l H ν) :
    lemma6ABlockAtAlpha x m l k H ν ≤
      Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
        Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ) *
        (Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l)) +
          Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (lemma6DyadicModulusScale x l / (H : ℝ)) *
            Real.sqrt (1 + ν ^ 2)) := by
  have hHpos : (0 : ℝ) < H := by positivity
  have hDpos : (0 : ℝ) < lemma6DyadicModulusScale x l := by positivity
  have hEpos : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  have hA0 : 0 ≤ lemma6ABlockAtAlpha x m l k H ν := by
    unfold lemma6ABlockAtAlpha
    apply Finset.sum_nonneg
    intro d _
    refine mul_nonneg (lemma6LinearWeight_nonneg d) ?_
    by_cases hd0 : d = 0
    · simp only [hd0, lemma6AModulusTotal]
      rfl
    · unfold lemma6AModulusTotal
      rw [dif_neg hd0]
      unfold lemma6AModulus primSum
      rw [tsum_fintype]
      refine Finset.sum_nonneg fun χ _ => ?_
      split_ifs <;> positivity
  have hsqA : lemma6ABlockAtAlpha x m l k H ν *
      lemma6ABlockAtAlpha x m l k H ν =
      lemma6ABlockAtAlpha x m l k H ν ^ 2 := by ring
  -- the two moment majorants
  have hpsm := lemma6PairSecondMajorant_alpha_le_scales
    (x := x) (l := l) (m := m) (k := k) ν hxlog hl hD4 hY
  have hrsm := lemma6RemainderSecondMajorant_le_crude hCremP hCremT
    (by linarith) hl hH1 hD4 hxlogH hlogHH hlogQ ν
  -- combine the two moment bounds into one squared estimate
  have hW : lemma6ABlockAtAlpha x m l k H ν ^ 2 ≤
      (lemma6ExceptionalFactorAt x l * (Cpair * (((5 / 4 : ℝ) *
              lemma6DyadicModulusScale x l +
            10 * lemma6PairDyadicScale x k /
              lemma6DyadicModulusScale x l) *
          (2 / lemma6PairDyadicScale x k)))) *
        ((36864 * CremP + 200 * CremT ^ 2) * (Real.log (x : ℝ)) ^ 3 *
          (Real.log (H : ℝ)) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
              (H : ℝ) ^ 2)) := by
    calc lemma6ABlockAtAlpha x m l k H ν ^ 2 ≤
        (lemma6ExceptionalFactorAt x l *
            (Cpair * lemma6PairSecondMajorant x l m k
              (lemma6AlphaPoint x ν))) *
          lemma6RemainderSecondMajorant CremP CremT x l H ν := hsq
      _ ≤ (lemma6ExceptionalFactorAt x l * (Cpair * (((5 / 4 : ℝ) *
                lemma6DyadicModulusScale x l +
              10 * lemma6PairDyadicScale x k /
                lemma6DyadicModulusScale x l) *
            (2 / lemma6PairDyadicScale x k)))) *
          lemma6RemainderSecondMajorant CremP CremT x l H ν := by
        have hmid : Cpair * lemma6PairSecondMajorant x l m k
                (lemma6AlphaPoint x ν) ≤
            Cpair * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                10 * lemma6PairDyadicScale x k /
                  lemma6DyadicModulusScale x l) *
              (2 / lemma6PairDyadicScale x k)) :=
          mul_le_mul_of_nonneg_left hpsm hCpair
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmid hEpos)
          (by unfold lemma6RemainderSecondMajorant; positivity)
      _ ≤ (lemma6ExceptionalFactorAt x l * (Cpair * (((5 / 4 : ℝ) *
                lemma6DyadicModulusScale x l +
              10 * lemma6PairDyadicScale x k /
                lemma6DyadicModulusScale x l) *
            (2 / lemma6PairDyadicScale x k)))) *
          ((36864 * CremP + 200 * CremT ^ 2) * (Real.log (x : ℝ)) ^ 3 *
            (Real.log (H : ℝ)) ^ 2 *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                (H : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hrsm (by positivity)
  -- pass to the square root of the right-hand side
  have hK123pos : 0 ≤ (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
      Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ)) := by positivity
  have hA1 : lemma6ABlockAtAlpha x m l k H ν ≤
      Real.sqrt (((Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ)) ^
            2) *
          ((lemma6ExceptionalFactorAt x l *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (2 / lemma6PairDyadicScale x k))) *
              (lemma6DyadicModulusScale x l / (H : ℝ) +
                1 / lemma6DyadicModulusScale x l +
                (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                  (H : ℝ) ^ 2))) := by
    apply real_le_sqrt_of_sq_le hA0
    rw [hsqA]
    have hsqrtpart :
        (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt ((Real.log (x : ℝ)) ^ 3) *
                Real.log (H : ℝ)) ^
            2 =
          (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            (Real.log (x : ℝ)) ^ 3 * (Real.log (H : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have heq :
        ((Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
                  Real.sqrt ((Real.log (x : ℝ)) ^ 3) *
                    Real.log (H : ℝ)) ^
              2) *
            ((lemma6ExceptionalFactorAt x l *
                  (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                      10 * lemma6PairDyadicScale x k /
                        lemma6DyadicModulusScale x l) *
                    (2 / lemma6PairDyadicScale x k))) *
              (lemma6DyadicModulusScale x l / (H : ℝ) +
                1 / lemma6DyadicModulusScale x l +
                (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                  (H : ℝ) ^ 2)) =
          (lemma6ExceptionalFactorAt x l * (Cpair * (((5 / 4 : ℝ) *
                    lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k)))) *
            ((36864 * CremP + 200 * CremT ^ 2) * (Real.log (x : ℝ)) ^ 3 *
              (Real.log (H : ℝ)) ^ 2 *
              (lemma6DyadicModulusScale x l / (H : ℝ) +
                1 / lemma6DyadicModulusScale x l +
                (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                  (H : ℝ) ^ 2)) := by
      rw [hsqrtpart]
      ring
    rw [heq]
    exact hW
  have hsqrtT : Real.sqrt (((Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ)) ^
          2) *
        ((lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                (H : ℝ) ^ 2))) =
      (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ)) *
        Real.sqrt ((lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                (H : ℝ) ^ 2)) := by
    rw [Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hK123pos]
  have hkey : lemma6ABlockAtAlpha x m l k H ν ≤
      (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ)) *
        Real.sqrt ((lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                (H : ℝ) ^ 2)) :=
    hA1.trans hsqrtT.le
  -- split the remaining square root into the three dyadic pieces
  have hwub : Real.sqrt ((lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                (H : ℝ) ^ 2)) ≤
      Real.sqrt (lemma6ExceptionalFactorAt x l *
            (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                10 * lemma6PairDyadicScale x k /
                  lemma6DyadicModulusScale x l) *
              (2 / lemma6PairDyadicScale x k))) *
        (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
          Real.sqrt (1 / lemma6DyadicModulusScale x l) +
          Real.sqrt ((1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
            (H : ℝ) ^ 2)) := by
    have hsplit : Real.sqrt ((lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                (H : ℝ) ^ 2)) =
        Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
          Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
              (H : ℝ) ^ 2) :=
      Real.sqrt_mul (by positivity) _
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left
      (real_sqrt_three_le (by positivity) (by positivity) (by positivity))
      (Real.sqrt_nonneg _)
  have hwsq : Real.sqrt ((1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
      (H : ℝ) ^ 2) =
      Real.sqrt (1 + ν ^ 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) := by
    rw [Real.sqrt_div
        (show (0 : ℝ) ≤ (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 by
          positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ 1 + ν ^ 2 by positivity),
      Real.sqrt_sq hDpos.le, Real.sqrt_sq hHpos.le]; ring
  calc lemma6ABlockAtAlpha x m l k H ν ≤
        (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ)) *
          Real.sqrt ((lemma6ExceptionalFactorAt x l *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (2 / lemma6PairDyadicScale x k))) *
              (lemma6DyadicModulusScale x l / (H : ℝ) +
                1 / lemma6DyadicModulusScale x l +
                (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 /
                  (H : ℝ) ^ 2)) := hkey
      _ ≤ Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt ((Real.log (x : ℝ)) ^ 3) * Real.log (H : ℝ) *
            (Real.sqrt (lemma6ExceptionalFactorAt x l *
                  (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                      10 * lemma6PairDyadicScale x k /
                        lemma6DyadicModulusScale x l) *
                    (2 / lemma6PairDyadicScale x k))) *
                (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
                  Real.sqrt (1 / lemma6DyadicModulusScale x l)) +
              Real.sqrt (lemma6ExceptionalFactorAt x l *
                  (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                      10 * lemma6PairDyadicScale x k /
                        lemma6DyadicModulusScale x l) *
                    (2 / lemma6PairDyadicScale x k))) *
                (lemma6DyadicModulusScale x l / (H : ℝ)) *
                  Real.sqrt (1 + ν ^ 2)) := by
        refine le_trans
          (mul_le_mul_of_nonneg_left hwub (by positivity)) ?_
        apply le_of_eq
        rw [hwsq]
        ring

/-- Fourth-root extraction for nonnegative quantities. -/
theorem real_le_rpow_quarter_of_pow_four_le {a x : ℝ} (ha : 0 ≤ a)
    (h : a ^ 4 ≤ x) :
    a ≤ x ^ ((1 : ℝ) / 4) := by
  have hx0 : 0 ≤ x := (pow_nonneg ha 4).trans h
  have hrw : x ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt x) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0,
      show ((1 : ℝ) / 2) * ((1 : ℝ) / 2) = (1 : ℝ) / 4 by ring]
  have h2 : a * a ≤ Real.sqrt x :=
    real_le_sqrt_of_sq_le (by positivity) (by
      have h4 : a * a * (a * a) = a ^ 4 := by ring
      rw [h4]
      exact h)
  calc a ≤ Real.sqrt (Real.sqrt x) := real_le_sqrt_of_sq_le ha h2
    _ ≤ x ^ ((1 : ℝ) / 4) := hrw.ge

/-- Splitting a quarter power of a binary product. -/
theorem real_rpow_quarter_mul2 {u v w : ℝ} (hu : 0 ≤ u) (hvw : 0 ≤ v * w) :
    (u * (v * w)) ^ ((1 : ℝ) / 4) =
      u ^ ((1 : ℝ) / 4) * (v * w) ^ ((1 : ℝ) / 4) :=
  Real.mul_rpow hu hvw

/-- Quarter power of a real fourth power is the identity. -/
theorem real_rpow_quarter_four {t : ℝ} (ht : 0 ≤ t) :
    ((t : ℝ) ^ ((4 : ℝ))) ^ ((1 : ℝ) / 4) = t := by
  rw [← Real.rpow_mul ht ((4 : ℝ)) ((1 : ℝ) / 4),
    show ((4 : ℝ)) * ((1 : ℝ) / 4) = 1 by ring, Real.rpow_one]

/-- Quarter power of a real square is the square root. -/
theorem real_rpow_quarter_two {t : ℝ} (ht : 0 ≤ t) :
    ((t : ℝ) ^ ((2 : ℝ))) ^ ((1 : ℝ) / 4) = t ^ ((1 : ℝ) / 2) := by
  rw [← Real.rpow_mul ht ((2 : ℝ)) ((1 : ℝ) / 4),
    show ((2 : ℝ)) * ((1 : ℝ) / 4) = 1 / 2 by ring]

/-! ### Pointwise majorants for the shifted `B` block -/

/-- Combining a square, a fourth power and a plain factor under one
fourth root. -/
theorem real_rpow_quarter_combine {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    (((a ^ 2) * b) * c) ^ ((1 : ℝ) / 4)
        = a ^ ((1 : ℝ) / 2) *
          ((b ^ ((1 : ℝ) / 4)) * (c ^ ((1 : ℝ) / 4))) := by
  rw [mul_assoc, Real.mul_rpow (pow_nonneg ha 2) (mul_nonneg hb hc),
    ← Real.rpow_natCast, ← Real.rpow_mul ha,
    show (((2 : ℕ) : ℝ)) * ((1 : ℝ) / 4) = (1 : ℝ) / 2 by ring,
    Real.mul_rpow hb hc]

set_option maxHeartbeats 2000000 in
/-- Equation (19), `B` part: the shifted block against the mollifier
fourth-moment ordering, with all dyadic scales made explicit. -/
theorem bblock_eq19_majorant
    {x l m k H : ℕ} {Cp Cm Cd : ℝ} (ν : ℝ)
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hCd : 0 ≤ Cd)
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k)
    (hH2 : 2 ≤ H)
    (hpair2 : (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ≤
      Cp * lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν))
    (hmol4 : (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤
      Cm * lemma6MollifierFourthMajorant x l H)
    (hder4 : (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤
      Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110 *
        ‖lemma6BetaPoint x ν‖ ^ 2)) :
    lemma6BBlockAtBeta x m l k H ν ≤
      ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
          ((1 : ℝ) / 2)) *
        ((((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  4 * ((H * H : ℕ) : ℝ) /
                    lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
          ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
              ((1 : ℝ) / 4) *
            (1 + ν ^ 2) ^ ((1 : ℝ) / 4)))) := by
  have hEpos : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  have hB0 : 0 ≤ lemma6BBlockAtBeta x m l k H ν :=
    lemma6BBlockAtBeta_nonneg x m l k H ν
  have hpsmB := lemma6PairSecondMajorant_beta_le_scales
    (x := x) (l := l) (m := m) (k := k) ν hxlog hl hD4 hY
  have hmfb := lemma6MollifierFourthMajorant_le_scales (x := x) (l := l) (H := H) hl hD4
  have hbeta := lemma6BetaPoint_norm_sq_le (x := x) (by linarith) ν

  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hW0 : (0 : ℝ) ≤ (2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110 :=
    mul_nonneg (by positivity) (pow_nonneg hlogx0 110)
  have hCDQ0 : (0 : ℝ) ≤
      (Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) * (1 + ν ^ 2) :=
    mul_nonneg (mul_nonneg hCd hW0) (by positivity)
  have hlogHHpos : (0 : ℝ) ≤ Real.log ((H * H : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (show 1 ≤ H * H by nlinarith)
  have hDpos : (0 : ℝ) < lemma6DyadicModulusScale x l :=
    lt_of_lt_of_le (by norm_num) hD4
  have hT0 : (0 : ℝ) ≤ (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
      4 * ((H * H : ℕ) : ℝ) / lemma6DyadicModulusScale x l :=
    add_nonneg (mul_nonneg (by norm_num) hDpos.le)
      (div_nonneg (by positivity) hDpos.le)
  have hBB0 : (0 : ℝ) ≤ (Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * ((H * H : ℕ) : ℝ) / lemma6DyadicModulusScale x l)) *
      (Real.log ((H * H : ℕ) : ℝ)) ^ 4) :=
    mul_nonneg (mul_nonneg hCm hT0) (pow_nonneg hlogHHpos 4)
  have hU1 : (1 : ℝ) ≤ lemma6PairUpperCutoff x k :=
    (show (1 : ℝ) ≤ lemma6PairDyadicScale x k by linarith).trans
      (lemma6PairScale_le_pairUpperCutoff x k)
  have hlogU0 : (0 : ℝ) ≤ 1 + Real.log (lemma6PairUpperCutoff x k) :=
    add_nonneg zero_le_one (Real.log_nonneg hU1)
  have hS10 : (0 : ℝ) ≤ ((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
      10 * lemma6PairDyadicScale x k / lemma6DyadicModulusScale x l) *
      (1 + Real.log (lemma6PairUpperCutoff x k)) :=
    mul_nonneg
      (add_nonneg (mul_nonneg (by norm_num) hDpos.le)
        (div_nonneg
          (mul_nonneg (by norm_num) (lemma6PairDyadicScale_nonneg x k))
          hDpos.le))
      hlogU0
  have hACS0 : (0 : ℝ) ≤ lemma6ExceptionalFactorAt x l * Cp *
      (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          10 * lemma6PairDyadicScale x k /
            lemma6DyadicModulusScale x l) *
        (1 + Real.log (lemma6PairUpperCutoff x k))) :=
    mul_nonneg (mul_nonneg hEpos hCp) hS10
  have hACS20 : (0 : ℝ) ≤ (lemma6ExceptionalFactorAt x l * Cp *
        (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
            10 * lemma6PairDyadicScale x k /
              lemma6DyadicModulusScale x l) *
          (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
      2 :=
    pow_nonneg hACS0 2
  have assocECS :
      lemma6ExceptionalFactorAt x l *
          (Cp * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              10 * lemma6PairDyadicScale x k /
                lemma6DyadicModulusScale x l) *
            (1 + Real.log (lemma6PairUpperCutoff x k)))) =
      lemma6ExceptionalFactorAt x l * Cp *
          (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              10 * lemma6PairDyadicScale x k /
                lemma6DyadicModulusScale x l) *
            (1 + Real.log (lemma6PairUpperCutoff x k))) := by
    ring
  have assocCM :
      Cm * ((((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * ((H * H : ℕ) : ℝ) / lemma6DyadicModulusScale x l) *
        (Real.log ((H * H : ℕ) : ℝ)) ^ 4)) =
      (Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * ((H * H : ℕ) : ℝ) / lemma6DyadicModulusScale x l)) *
        (Real.log ((H * H : ℕ) : ℝ)) ^ 4) := by
    ring
  have assocCD :
      Cd * (((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110) * (1 + ν ^ 2)) =
      (Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) * (1 + ν ^ 2) := by
    ring
  have e1 : lemma6ExceptionalFactorAt x l *
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2 ≤
      lemma6ExceptionalFactorAt x l * Cp *
        (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
            10 * lemma6PairDyadicScale x k /
              lemma6DyadicModulusScale x l) *
          (1 + Real.log (lemma6PairUpperCutoff x k))) := by
    refine le_trans (mul_le_mul_of_nonneg_left hpair2 hEpos) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpsmB hCp) hEpos) (le_of_eq assocECS)
  have e2 : ∑ i ∈ lemma6CharacterBlock x l,
      lemma6PrimitiveBaseWeight i *
        lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4 ≤
      (Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * ((H * H : ℕ) : ℝ) / lemma6DyadicModulusScale x l)) *
        (Real.log ((H * H : ℕ) : ℝ)) ^ 4) := by
    refine le_trans (hmol4.trans (mul_le_mul_of_nonneg_left hmfb hCm))
      (le_of_eq assocCM)
  have e3 : ∑ i ∈ lemma6CharacterBlock x l,
      lemma6PrimitiveBaseWeight i *
        lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 ≤
      (Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) * (1 + ν ^ 2) := by
    refine le_trans (hder4.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbeta hW0) hCd)) (le_of_eq assocCD)

  have hpow : lemma6BBlockAtBeta x m l k H ν ^ 4 ≤
      (((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            2) *
          ((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l)) *
            (Real.log ((H * H : ℕ) : ℝ)) ^ 4)) *
        ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) *
          (1 + ν ^ 2))) := by
    rw [lemma6BBlockAtBeta_eq_characterBlock_sum x m l k H ν]
    refine (lemma6_equation19_B_holder hxlarge m k H ν).trans ?_
    have hsumP : (0 : ℝ) ≤ ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
    have hsumM : (0 : ℝ) ≤ ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
    have hsumL : (0 : ℝ) ≤ ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
    refine mul_le_mul ?_ e3 hsumL (mul_nonneg hACS20 hBB0)
    refine mul_le_mul ?_ e2 hsumM hACS20
    exact pow_le_pow_left₀ (mul_nonneg hEpos hsumP) e1 2
  -- extract the fourth root and split the quarter powers
  have hroot := real_le_rpow_quarter_of_pow_four_le hB0 hpow
  have hexp :
      (((lemma6ExceptionalFactorAt x l * Cp *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            2) *
          ((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l)) *
            (Real.log ((H * H : ℕ) : ℝ)) ^ 4)) *
        ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) *
          (1 + ν ^ 2))) ^ ((1 : ℝ) / 4) =
      ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
          ((1 : ℝ) / 2)) *
        ((((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  4 * ((H * H : ℕ) : ℝ) /
                    lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
          ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
              ((1 : ℝ) / 4) *
            (1 + ν ^ 2) ^ ((1 : ℝ) / 4)))) := by

    have hCT0 : (0 : ℝ) ≤ Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * ((H * H : ℕ) : ℝ) / lemma6DyadicModulusScale x l)) :=
      mul_nonneg hCm hT0
    have hBC0 : (0 : ℝ) ≤ ((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        4 * ((H * H : ℕ) : ℝ) /
          lemma6DyadicModulusScale x l)) *
      (Real.log ((H * H : ℕ) : ℝ)) ^ 4)) :=
      mul_nonneg hCT0 (pow_nonneg hlogHHpos 4)
    refine Eq.trans (real_rpow_quarter_combine hACS0 hBC0 hCDQ0) ?_
    rw [Real.mul_rpow hCT0 (pow_nonneg hlogHHpos 4),
      ← Real.rpow_natCast, ← Real.rpow_mul hlogHHpos,
      show (((4 : ℕ) : ℝ)) * ((1 : ℝ) / 4) = 1 by ring, Real.rpow_one,
      Real.mul_rpow (mul_nonneg hCd hW0) (by positivity)]
  rw [hexp] at hroot
  exact hroot

/-! ### The equation-(20) `2,4,4` ordering -/

/-- The height-independent fourth-power majorant produced by equation (20). -/
noncomputable def lemma6B20BaseMajorant
    (x l k H : ℕ) (Cs Cd Cp C4 : ℝ) : ℝ :=
  (lemma6ExceptionalFactorAt x l *
      (Cs * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * (H : ℝ) / lemma6DyadicModulusScale x l) *
        (1 + Real.log (H : ℝ))))) ^ 2 *
    (Cd * ((2 : ℝ) ^ l * Real.log (x : ℝ) ^ 110)) *
    ((Cp * C4) *
      (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
        Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4))

/-- Pointwise equation-(20) majorant after taking the fourth root. -/
theorem bblock_eq20_majorant
    {x l m k H : ℕ} {Cs Cd Cp C4 : ℝ}
    (nu : ℝ) (hCs : 0 ≤ Cs) (hCd : 0 ≤ Cd)
    (hCp : 0 ≤ Cp) (hC4 : 0 ≤ C4)
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) (_hH2 : 2 ≤ H)
    (hmol2 :
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x nu) i ^ 2) ≤
        Cs * lemma6MollifierSecondMajorant x l H)
    (hder4 :
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x nu) i ^ 4) ≤
        Cd * lemma6DerivativeFourthMajorant x l nu)
    (hpair4 :
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k (lemma6BetaPoint x nu) i ^ 4) ≤
        Cp * lemma6PairFourthMajorant x l m k (lemma6BetaPoint x nu))
    (hpairMajorant :
      lemma6PairFourthMajorant x l m k (lemma6BetaPoint x nu) ≤
        C4 * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4)) :
    lemma6BBlockAtBeta x m l k H nu ≤
      lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4) := by
  have hmScale := lemma6MollifierSecondMajorant_le_scales (H := H) hl hD4
  have hdScale := lemma6DerivativeFourthMajorant_le_kernel
    (x := x) (l := l) nu (by linarith)
  have eM :
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x nu) i ^ 2) ≤
        Cs * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * (H : ℝ) / lemma6DyadicModulusScale x l) *
          (1 + Real.log (H : ℝ))) :=
    hmol2.trans (mul_le_mul_of_nonneg_left hmScale hCs)
  have eD :
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x nu) i ^ 4) ≤
        (Cd * ((2 : ℝ) ^ l * Real.log (x : ℝ) ^ 110)) *
          (1 + nu ^ 2) := by
    refine hder4.trans ?_
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdScale hCd
  have eP :
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k (lemma6BetaPoint x nu) i ^ 4) ≤
        (Cp * C4) * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4) := by
    refine hpair4.trans ?_
    calc Cp * lemma6PairFourthMajorant x l m k (lemma6BetaPoint x nu) ≤
        Cp * (C4 * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hpairMajorant hCp
      _ = (Cp * C4) * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4) := by ring
  have hpow : lemma6BBlockAtBeta x m l k H nu ^ 4 ≤
      lemma6B20BaseMajorant x l k H Cs Cd Cp C4 * (1 + nu ^ 2) := by
    rw [lemma6BBlockAtBeta_eq_characterBlock_sum x m l k H nu]
    refine (lemma6_equation20_B_of_moment_bounds hxlarge m k H nu _ _ _
      eM eD eP).trans ?_
    unfold lemma6B20BaseMajorant
    ring_nf
    exact le_rfl
  have hbase0 : 0 ≤ lemma6B20BaseMajorant x l k H Cs Cd Cp C4 := by
    unfold lemma6B20BaseMajorant
    positivity
  have hroot := real_le_rpow_quarter_of_pow_four_le
    (lemma6BBlockAtBeta_nonneg x m l k H nu) hpow
  calc lemma6BBlockAtBeta x m l k H nu ≤
      (lemma6B20BaseMajorant x l k H Cs Cd Cp C4 *
        (1 + nu ^ 2)) ^ ((1 : ℝ) / 4) := hroot
    _ = lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4) := by
      rw [Real.mul_rpow hbase0 (by positivity)]

end Chen
