/-
Final assembly of the occupied-block estimate underlying equations (19)
and (20) of Chen's proof of Lemma 6: every occupied `(l, k)` block sum is
eventually bounded by `x / (log x)^20`.
-/
import ChenTheorem.Lemma6.PairBlockEstimate

open Real MeasureTheory Filter
open scoped Classical

namespace Chen

/-! ### The quarter-moment mass of the shifted-line kernel -/

/-- Pointwise domination of the kernel against the Cauchy denominator. -/
theorem kernelNorm_mul_rpow_quarter_le
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (nu : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4) ≤
      4 * Real.log (x : ℝ) ^ 5 * (1 + nu ^ 2)⁻¹ := by
  have hker := norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five
    hxlog nu
  have hpow : (0 : ℝ) ≤ (1 + nu ^ 2) ^ ((1 : ℝ) / 4) := by positivity
  have hB := lemma6BKernel_le_cauchy nu
  calc ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4) ≤
      (2 * Real.log (x : ℝ) ^ 5 / (1 + nu ^ 4)) *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_right hker hpow
  _ = (2 * Real.log (x : ℝ) ^ 5) * lemma6BKernel nu := by
      unfold lemma6BKernel
      ring
  _ ≤ (2 * Real.log (x : ℝ) ^ 5) * (2 * (1 + nu ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  _ = 4 * Real.log (x : ℝ) ^ 5 * (1 + nu ^ 2)⁻¹ := by ring

/-- Integrability of the quarter-moment weighted kernel on the `beta` line. -/
theorem integrable_kernelNorm_mul_rpow_quarter
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    Integrable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) := by
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hmeas : AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) volume :=
    (aestronglyMeasurable_norm_kernel_beta hxlog).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun _ => Or.inr (by norm_num))).aestronglyMeasurable
  have hmaj : Integrable (fun nu : ℝ =>
      (4 * Real.log (x : ℝ) ^ 5) * (1 + nu ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hmaj.mono' hmeas ?_
  filter_upwards with nu
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
    (show (0 : ℝ) ≤ (1 + nu ^ 2) ^ ((1 : ℝ) / 4) by positivity))]
  exact kernelNorm_mul_rpow_quarter_le hxlog nu

/-- The full-line quarter-moment kernel mass: an absolute constant times
the fifth power of the logarithm. -/
theorem integral_kernelNorm_mul_rpow_quarter_le
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) :
    (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) ≤
      4 * Real.pi * Real.log (x : ℝ) ^ 5 := by
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hstep : (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) ≤
      ∫ nu : ℝ, (4 * Real.log (x : ℝ) ^ 5) * (1 + nu ^ 2)⁻¹ := by
    apply MeasureTheory.integral_mono
      (integrable_kernelNorm_mul_rpow_quarter hxlog)
      (integrable_inv_one_add_sq.const_mul (4 * Real.log (x : ℝ) ^ 5))
    intro nu
    exact kernelNorm_mul_rpow_quarter_le hxlog nu
  have hval : (∫ nu : ℝ, (4 * Real.log (x : ℝ) ^ 5) * (1 + nu ^ 2)⁻¹) =
      4 * Real.log (x : ℝ) ^ 5 * Real.pi := by
    rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  calc (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) ≤
      ∫ nu : ℝ, (4 * Real.log (x : ℝ) ^ 5) * (1 + nu ^ 2)⁻¹ := hstep
    _ = 4 * Real.log (x : ℝ) ^ 5 * Real.pi := hval
    _ = 4 * Real.pi * Real.log (x : ℝ) ^ 5 := by ring

/-! ### Continuity and integrability of the `A` block -/

/-- On a genuine dyadic modulus block the `A` block is continuous in the
height: only primitive characters survive, and both the pair polynomial
and `1 - L * S` are entire in the spectral parameter. -/
theorem continuous_lemma6ABlockAtAlpha
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (m k H : ℕ) :
    Continuous (lemma6ABlockAtAlpha x m l k H) := by
  have hbeta : Continuous (fun nu : ℝ => lemma6AlphaPoint x nu) := by
    dsimp only [lemma6AlphaPoint]
    fun_prop
  have heq : lemma6ABlockAtAlpha x m l k H = fun nu =>
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6AlphaPoint x nu) i *
          lemma6RemainderNorm H (lemma6AlphaPoint x nu) i := by
    funext nu
    simpa only [] using
      lemma6ABlockAtAlpha_eq_characterBlock_sum x m l k H nu
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
  · have hpair : Continuous (fun nu : ℝ =>
        lemma6PairBlockNorm x m k (lemma6AlphaPoint x nu) i) := by
      unfold lemma6PairBlockNorm
      exact ((differentiable_lemma6PairBlockPolynomial x m k i.2).continuous.comp
        hbeta).norm
    have hrem : Continuous (fun nu : ℝ =>
        lemma6RemainderNorm H (lemma6AlphaPoint x nu) i) := by
      letI : NeZero i.1 := ⟨hd0⟩
      simp only [lemma6RemainderNorm, hd0]
      have hL : Differentiable ℂ (DirichletCharacter.LFunction i.2) :=
        primitiveCharacter_differentiable_LFunction hd2 hp
      have hM : Differentiable ℂ (fun s : ℂ => lemma6MollifierAt H s i.2) :=
        differentiable_lemma6MollifierAt H i.2
      exact ((differentiable_one.sub (hL.mul hM)).continuous.comp hbeta).norm
    exact ((((continuous_const.mul continuous_const).mul hpair).mul hrem))
  · have hweight : lemma6PrimitiveBaseWeight i = 0 := by
      simp [lemma6PrimitiveBaseWeight, hp]
    simp only [hweight, zero_mul]
    exact continuous_const

/-- Nonnegativity of the scalar `A` block, stated here so that the final
integration layer does not depend on `Core`. -/
theorem lemma6ABlockAtAlpha_nonneg_base (x m l k H : ℕ) (nu : ℝ) :
    0 ≤ lemma6ABlockAtAlpha x m l k H nu := by
  unfold lemma6ABlockAtAlpha
  exact Finset.sum_nonneg fun d _ =>
    mul_nonneg (lemma6LinearWeight_nonneg d) (by
      unfold lemma6AModulusTotal
      split_ifs
      · exact le_rfl
      · unfold lemma6AModulus primSum
        exact tsum_nonneg fun chi => by split_ifs <;> positivity)

/-- Any quadratic height bound for the `A` block is integrable against the
`alpha`-line kernel. -/
theorem integrable_kernelNorm_mul_lemma6ABlockAtAlpha_of_le
    {x l : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ))
    (m k H : ℕ) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ nu : ℝ,
      lemma6ABlockAtAlpha x m l k H nu ≤ C * (1 + nu ^ 2)) :
    Integrable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x nu)‖ *
        lemma6ABlockAtAlpha x m l k H nu) := by
  have hbase := integrable_kernelNorm_alpha_mul_one_add_sq hxlog
  have hmeas : AEStronglyMeasurable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x nu)‖ *
        lemma6ABlockAtAlpha x m l k H nu) volume :=
    (aestronglyMeasurable_norm_kernel_alpha hxlog).mul
      (continuous_lemma6ABlockAtAlpha (x := x) (l := l) (by linarith)
        m k H).aestronglyMeasurable
  have hmaj := hbase.const_mul C
  refine hmaj.mono' hmeas ?_
  filter_upwards with nu
  have h1 : C * (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
      (1 + nu ^ 2)) =
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
        (C * (1 + nu ^ 2)) := by ring
  rw [h1]
  have hk : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
      (lemma6AlphaPoint x nu)‖ := norm_nonneg _
  have hA : (0 : ℝ) ≤ lemma6ABlockAtAlpha x m l k H nu :=
    lemma6ABlockAtAlpha_nonneg_base x m l k H nu
  have h3 : ‖(‖lemma6SmoothingMellinKernel (x : ℝ)
      (lemma6AlphaPoint x nu)‖ *
      lemma6ABlockAtAlpha x m l k H nu : ℝ)‖ =
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
        lemma6ABlockAtAlpha x m l k H nu :=
    Real.norm_of_nonneg (mul_nonneg hk hA)
  rw [h3]
  exact mul_le_mul_of_nonneg_left (hbound nu) hk

/-! ### Integral forms of the two block majorants -/

/-- Scalar majorant for the integrated `A` block. -/
noncomputable def lemma6AIntegralMajorant
    (x l k H : ℕ) (Cpair CremP CremT : ℝ) : ℝ :=
  Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
    Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
    (Real.sqrt (lemma6ExceptionalFactorAt x l *
          (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              10 * lemma6PairDyadicScale x k /
                lemma6DyadicModulusScale x l) *
            (2 / lemma6PairDyadicScale x k))) *
        (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
          Real.sqrt (1 / lemma6DyadicModulusScale x l) +
          lemma6DyadicModulusScale x l / (H : ℝ))) *
    (2 * Real.pi * Real.log (x : ℝ) ^ 5)

/-- Scalar majorant for the integrated `B` block. -/
noncomputable def lemma6BIntegralMajorant
    (x l k H : ℕ) (Cp Cm Cd : ℝ) : ℝ :=
  ((lemma6ExceptionalFactorAt x l * Cp *
          (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              10 * lemma6PairDyadicScale x k /
                lemma6DyadicModulusScale x l) *
            (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
        ((1 : ℝ) / 2) *
      (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
            4 * ((H * H : ℕ) : ℝ) /
              lemma6DyadicModulusScale x l))) ^
          ((1 : ℝ) / 4) *
        Real.log ((H * H : ℕ) : ℝ)) *
        ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
          ((1 : ℝ) / 4)))) *
    (4 * Real.pi * Real.log (x : ℝ) ^ 5)

/-- The `alpha`-line block integral, bounded by the scalar `A` majorant
times the quadratic kernel mass. -/
theorem integrable_and_integral_kernelNorm_mul_ABlock_le
    {x l m k H : ℕ} {Cpair CremP CremT : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 < CremP) (hCremT : 0 < CremT)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k)
    (hH1 : 1 ≤ H) (hlogH : 1 ≤ Real.log (H : ℝ))
    (hlogHH : Real.log ((2 * H * H : ℕ) : ℝ) ≤ 8 * Real.log (x : ℝ))
    (hlogQ : Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
      2 * Real.log (x : ℝ))
    (hsq : ∀ nu : ℝ,
      lemma6ABlockAtAlpha x m l k H nu ^ 2 ≤
        (lemma6ExceptionalFactorAt x l *
            (Cpair * lemma6PairSecondMajorant x l m k
              (lemma6AlphaPoint x nu))) *
          lemma6RemainderSecondMajorant CremP CremT x l H nu) :
    Integrable (fun nu : ℝ =>
        ‖lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x nu)‖ *
          lemma6ABlockAtAlpha x m l k H nu) ∧
      (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x nu)‖ *
          lemma6ABlockAtAlpha x m l k H nu) ≤
      lemma6AIntegralMajorant x l k H Cpair CremP CremT := by
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hc0 : (0 : ℝ) ≤ Real.sqrt (Cpair * (36864 * CremP +
      200 * CremT ^ 2)) * Real.sqrt (Real.log (x : ℝ) ^ 3) *
      Real.log (H : ℝ) * Real.sqrt (lemma6ExceptionalFactorAt x l *
        (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
            10 * lemma6PairDyadicScale x k /
              lemma6DyadicModulusScale x l) *
          (2 / lemma6PairDyadicScale x k))) := by
    positivity
  have hB1pos : (0 : ℝ) ≤ Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
      Real.sqrt (1 / lemma6DyadicModulusScale x l) := by positivity
  have hB2pos : (0 : ℝ) ≤ lemma6DyadicModulusScale x l / (H : ℝ) := by
    positivity
  have hab : ∀ nu : ℝ, lemma6ABlockAtAlpha x m l k H nu ≤
      (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k)))) *
          (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
            Real.sqrt (1 / lemma6DyadicModulusScale x l) +
            lemma6DyadicModulusScale x l / (H : ℝ) * (1 + nu ^ 2)) := by
    intro nu
    have h := ablock_majorant hCpair hCremP hCremT hxlog hl hD4 hY hH1 hlogH
      hlogHH hlogQ nu (hsq nu)
    have hpos1 : (0 : ℝ) ≤ (1 : ℝ) + nu ^ 2 := by positivity
    have h2 : ((1 : ℝ) + nu ^ 2) ≤ ((1 : ℝ) + nu ^ 2) ^ 2 := by
      nlinarith [sq_nonneg nu]
    have hsqrt : Real.sqrt ((1 : ℝ) + nu ^ 2) ≤ (1 : ℝ) + nu ^ 2 := by
      calc Real.sqrt ((1 : ℝ) + nu ^ 2) ≤
          Real.sqrt (((1 : ℝ) + nu ^ 2) ^ 2) := Real.sqrt_le_sqrt h2
        _ = (1 : ℝ) + nu ^ 2 := Real.sqrt_sq hpos1
    have hkey : Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
        Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
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
            Real.sqrt ((1 : ℝ) + nu ^ 2)) =
        (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k)))) *
          (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
            Real.sqrt (1 / lemma6DyadicModulusScale x l) +
            lemma6DyadicModulusScale x l / (H : ℝ) *
              Real.sqrt ((1 : ℝ) + nu ^ 2)) := by
      ring
    rw [hkey] at h
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [mul_le_mul_of_nonneg_right hsqrt hB2pos]
  have hbound : ∀ nu : ℝ, lemma6ABlockAtAlpha x m l k H nu ≤
      (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k)))) *
          (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
            Real.sqrt (1 / lemma6DyadicModulusScale x l) +
            lemma6DyadicModulusScale x l / (H : ℝ)) *
          (1 + nu ^ 2) := by
    intro nu
    have ht : (1 : ℝ) ≤ 1 + nu ^ 2 := by nlinarith [sq_nonneg nu]
    have hstep : Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
        Real.sqrt (1 / lemma6DyadicModulusScale x l) +
        lemma6DyadicModulusScale x l / (H : ℝ) * (1 + nu ^ 2) ≤
        (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
            Real.sqrt (1 / lemma6DyadicModulusScale x l) +
            lemma6DyadicModulusScale x l / (H : ℝ)) *
          (1 + nu ^ 2) := by
      calc Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
            Real.sqrt (1 / lemma6DyadicModulusScale x l) +
            lemma6DyadicModulusScale x l / (H : ℝ) * (1 + nu ^ 2) ≤
          (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
                Real.sqrt (1 / lemma6DyadicModulusScale x l)) *
              (1 + nu ^ 2) +
            lemma6DyadicModulusScale x l / (H : ℝ) * (1 + nu ^ 2) := by
            linarith [le_mul_of_one_le_right hB1pos ht]
      _ = (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ)) *
            (1 + nu ^ 2) := by
            ring
    calc lemma6ABlockAtAlpha x m l k H nu ≤
        (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
              Real.sqrt (lemma6ExceptionalFactorAt x l *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (2 / lemma6PairDyadicScale x k)))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ) * (1 + nu ^ 2)) :=
      hab nu
      _ ≤ (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
              Real.sqrt (lemma6ExceptionalFactorAt x l *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (2 / lemma6PairDyadicScale x k)))) *
            ((Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
                  Real.sqrt (1 / lemma6DyadicModulusScale x l) +
                  lemma6DyadicModulusScale x l / (H : ℝ)) *
                (1 + nu ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep hc0
      _ = (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
              Real.sqrt (lemma6ExceptionalFactorAt x l *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (2 / lemma6PairDyadicScale x k)))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ)) *
            (1 + nu ^ 2) := by
        ring
  have hint := integrable_kernelNorm_mul_lemma6ABlockAtAlpha_of_le
    (C := Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
      Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
      Real.sqrt (lemma6ExceptionalFactorAt x l *
        (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
            10 * lemma6PairDyadicScale x k /
              lemma6DyadicModulusScale x l) *
          (2 / lemma6PairDyadicScale x k))) *
      (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
        Real.sqrt (1 / lemma6DyadicModulusScale x l) +
        lemma6DyadicModulusScale x l / (H : ℝ)))
    hxlog m k H (by positivity) hbound
  have hmass := integral_kernelNorm_alpha_mul_one_add_sq_le hxlog
  have hKint : Integrable (fun nu : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖) := by
    refine (integrable_kernelNorm_alpha_mul_one_add_sq hxlog).mono'
      (aestronglyMeasurable_norm_kernel_alpha hxlog) ?_
    filter_upwards with nu
    have hk : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x nu)‖ := norm_nonneg _
    rw [Real.norm_of_nonneg hk]
    exact le_mul_of_one_le_right hk
      (show (1 : ℝ) ≤ 1 + nu ^ 2 by nlinarith [sq_nonneg nu])
  have hKmass : (∫ nu : ℝ,
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖) ≤
      2 * Real.pi * Real.log (x : ℝ) ^ 5 := by
    have hstep : (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖) ≤
        ∫ nu : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
            (1 + nu ^ 2) := by
      apply MeasureTheory.integral_mono hKint
        (integrable_kernelNorm_alpha_mul_one_add_sq hxlog)
      intro nu
      have hk : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x nu)‖ := norm_nonneg _
      exact le_mul_of_one_le_right hk
        (show (1 : ℝ) ≤ 1 + nu ^ 2 by nlinarith [sq_nonneg nu])
    exact hstep.trans hmass
  have hpoint : ∀ nu : ℝ,
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
        lemma6ABlockAtAlpha x m l k H nu ≤
      (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ))) *
        (‖lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x nu)‖ * (1 + nu ^ 2)) := by
    intro nu
    have hk : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x nu)‖ := norm_nonneg _
    calc ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
        lemma6ABlockAtAlpha x m l k H nu ≤
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
          ((Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
                Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
                Real.sqrt (lemma6ExceptionalFactorAt x l *
                  (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                      10 * lemma6PairDyadicScale x k /
                        lemma6DyadicModulusScale x l) *
                    (2 / lemma6PairDyadicScale x k)))) *
              (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
                Real.sqrt (1 / lemma6DyadicModulusScale x l) +
                lemma6DyadicModulusScale x l / (H : ℝ)) *
              (1 + nu ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbound nu) hk
    _ = (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ))) *
        (‖lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x nu)‖ * (1 + nu ^ 2)) := by
      ring
  have hint2 : Integrable (fun nu : ℝ =>
      (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ))) *
        (‖lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x nu)‖ * (1 + nu ^ 2))) :=
    (integrable_kernelNorm_alpha_mul_one_add_sq hxlog).const_mul _
  have hmono : (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
          lemma6ABlockAtAlpha x m l k H nu) ≤
      ∫ nu : ℝ,
        (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
              Real.sqrt (lemma6ExceptionalFactorAt x l *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (2 / lemma6PairDyadicScale x k))) *
              (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
                Real.sqrt (1 / lemma6DyadicModulusScale x l) +
                lemma6DyadicModulusScale x l / (H : ℝ))) *
          (‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x nu)‖ * (1 + nu ^ 2)) :=
    MeasureTheory.integral_mono hint hint2 (fun nu => hpoint nu)
  refine ⟨hint, ?_⟩
  calc (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖ *
          lemma6ABlockAtAlpha x m l k H nu) ≤
      ∫ nu : ℝ,
        (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
              Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
              Real.sqrt (lemma6ExceptionalFactorAt x l *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (2 / lemma6PairDyadicScale x k))) *
              (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
                Real.sqrt (1 / lemma6DyadicModulusScale x l) +
                lemma6DyadicModulusScale x l / (H : ℝ))) *
          (‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x nu)‖ * (1 + nu ^ 2)) := hmono
    _ = (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ))) *
          ∫ nu : ℝ,
            ‖lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x nu)‖ * (1 + nu ^ 2) :=
      MeasureTheory.integral_const_mul _
        (fun nu : ℝ =>
          ‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x nu)‖ * (1 + nu ^ 2))
    _ ≤ (Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
            Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
            Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ))) *
        (2 * Real.pi * Real.log (x : ℝ) ^ 5) := by
      refine mul_le_mul_of_nonneg_left hmass ?_
      positivity
    _ = Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
        Real.sqrt (Real.log (x : ℝ) ^ 3) * Real.log (H : ℝ) *
        (Real.sqrt (lemma6ExceptionalFactorAt x l *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (2 / lemma6PairDyadicScale x k))) *
            (Real.sqrt (lemma6DyadicModulusScale x l / (H : ℝ)) +
              Real.sqrt (1 / lemma6DyadicModulusScale x l) +
              lemma6DyadicModulusScale x l / (H : ℝ))) *
        (2 * Real.pi * Real.log (x : ℝ) ^ 5) := by
      ring


/-- The `beta`-line block integral, bounded by the scalar `B` majorant
times the quarter-moment kernel mass. -/
theorem integrable_and_integral_kernelNorm_mul_BBlock_le
    {x l m k H : ℕ} {Cp Cm Cd : ℝ}
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hCd : 0 ≤ Cd)
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) (hH2 : 2 ≤ H)
    (hpair2 : ∀ ν : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ≤
        Cp * lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν))
    (hmol4 : ∀ ν : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤
        Cm * lemma6MollifierFourthMajorant x l H)
    (hder4 : ∀ ν : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤
        Cd * lemma6DerivativeFourthMajorant x l ν) :
    Integrable (fun nu : ℝ =>
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu) ∧
      (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu) ≤
      lemma6BIntegralMajorant x l k H Cp Cm Cd := by
  have hBpoint : ∀ nu : ℝ, lemma6BBlockAtBeta x m l k H nu ≤
      ((lemma6ExceptionalFactorAt x l * Cp *
            (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                10 * lemma6PairDyadicScale x k /
                  lemma6DyadicModulusScale x l) *
              (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
          ((1 : ℝ) / 2) *
        (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              4 * ((H * H : ℕ) : ℝ) /
                lemma6DyadicModulusScale x l))) ^
            ((1 : ℝ) / 4) *
          Real.log ((H * H : ℕ) : ℝ)) *
          ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
              ((1 : ℝ) / 4)))) *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4) := by
    intro nu
    have h := bblock_eq19_majorant nu hCp hCm hCd hxlarge hxlog hl hD4 hY hH2
      (hpair2 nu) (hmol4 nu) (hder4 nu)
    convert h using 1
    all_goals ring
  have hE0 : (0 : ℝ) ≤ lemma6ExceptionalFactorAt x l := by
    exact (lemma6ExceptionalFactor_pos _).le
  have hlogHH0 : (0 : ℝ) ≤ Real.log ((H * H : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (show 1 ≤ H * H by nlinarith)
  have hcoef0 : (0 : ℝ) ≤
      ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            ((1 : ℝ) / 2) *
          (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
            ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
                ((1 : ℝ) / 4)))) := by
    positivity
  have hint := integrable_kernelNorm_mul_lemma6BBlockAtBeta_of_le hxlog m k H
    hcoef0 hBpoint
  have hmass := integral_kernelNorm_mul_rpow_quarter_le hxlog
  have hpoint : ∀ nu : ℝ,
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu ≤
      ((lemma6ExceptionalFactorAt x l * Cp *
            (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                10 * lemma6PairDyadicScale x k /
                  lemma6DyadicModulusScale x l) *
              (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
          ((1 : ℝ) / 2) *
        (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              4 * ((H * H : ℕ) : ℝ) /
                lemma6DyadicModulusScale x l))) ^
            ((1 : ℝ) / 4) *
          Real.log ((H * H : ℕ) : ℝ)) *
          ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
              ((1 : ℝ) / 4)))) *
        (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) := by
    intro nu
    have hk : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖ := norm_nonneg _
    calc ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu ≤
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (((lemma6ExceptionalFactorAt x l * Cp *
                (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                    10 * lemma6PairDyadicScale x k /
                      lemma6DyadicModulusScale x l) *
                  (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
              ((1 : ℝ) / 2) *
            (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  4 * ((H * H : ℕ) : ℝ) /
                    lemma6DyadicModulusScale x l))) ^
                ((1 : ℝ) / 4) *
              Real.log ((H * H : ℕ) : ℝ)) *
              ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
                  ((1 : ℝ) / 4)))) *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (hBpoint nu) hk
    _ = ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            ((1 : ℝ) / 2) *
          (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
            ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
                ((1 : ℝ) / 4)))) *
        (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) := by
      ring
  have hint2 : Integrable (fun nu : ℝ =>
      ((lemma6ExceptionalFactorAt x l * Cp *
            (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                10 * lemma6PairDyadicScale x k /
                  lemma6DyadicModulusScale x l) *
              (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
          ((1 : ℝ) / 2) *
        (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              4 * ((H * H : ℕ) : ℝ) /
                lemma6DyadicModulusScale x l))) ^
            ((1 : ℝ) / 4) *
          Real.log ((H * H : ℕ) : ℝ)) *
          ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
              ((1 : ℝ) / 4)))) *
        (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (1 + nu ^ 2) ^ ((1 : ℝ) / 4))) :=
    (integrable_kernelNorm_mul_rpow_quarter hxlog).const_mul _
  have hmono : (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu) ≤
      ∫ nu : ℝ,
        ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            ((1 : ℝ) / 2) *
          (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
            ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
                ((1 : ℝ) / 4)))) *
          (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) :=
    MeasureTheory.integral_mono hint hint2 (fun nu => hpoint nu)
  refine ⟨hint, ?_⟩
  calc (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu) ≤
      ∫ nu : ℝ,
        ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            ((1 : ℝ) / 2) *
          (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
            ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
                ((1 : ℝ) / 4)))) *
          (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) := hmono
    _ = ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            ((1 : ℝ) / 2) *
          (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
            ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
                ((1 : ℝ) / 4)))) *
          ∫ nu : ℝ,
            ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
              (1 + nu ^ 2) ^ ((1 : ℝ) / 4) :=
      MeasureTheory.integral_const_mul _
        (fun nu : ℝ =>
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4))
    _ ≤ ((lemma6ExceptionalFactorAt x l * Cp *
              (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                  10 * lemma6PairDyadicScale x k /
                    lemma6DyadicModulusScale x l) *
                (1 + Real.log (lemma6PairUpperCutoff x k)))) ^
            ((1 : ℝ) / 2) *
          (((Cm * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
                4 * ((H * H : ℕ) : ℝ) /
                  lemma6DyadicModulusScale x l))) ^
              ((1 : ℝ) / 4) *
            Real.log ((H * H : ℕ) : ℝ)) *
            ((Cd * ((2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 110)) ^
                ((1 : ℝ) / 4)))) *
          (4 * Real.pi * Real.log (x : ℝ) ^ 5) := by
      refine le_trans (mul_le_mul_of_nonneg_left hmass hcoef0) ?_
      ring_nf
      exact le_rfl

/-! ### Integrated equation-(20) `B` majorant -/

/-- Scalar majorant for the integrated equation-(20) `B` block. -/
noncomputable def lemma6B20IntegralMajorant
    (x l k H : ℕ) (Cs Cd Cp C4 : ℝ) : ℝ :=
  lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
    (4 * Real.pi * Real.log (x : ℝ) ^ 5)

/-- The complete occupied-block scalar majorant using equation (19)'s
shifted-line Hölder ordering. -/
noncomputable def lemma6LargePairBlockMajorant
    (x l k H : ℕ) (Cpair CremP CremT Cp Cm Cd : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
        lemma6AIntegralMajorant x l k H Cpair CremP CremT +
      (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
        lemma6BIntegralMajorant x l k H Cp Cm Cd)

/-- The complete occupied-block scalar majorant using equation (20)'s
`2,4,4` shifted-line Hölder ordering. -/
noncomputable def lemma6LargePairBlock20Majorant
    (x l k H : ℕ)
    (Cpair CremP CremT Cs Cd Cp C4 : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
        lemma6AIntegralMajorant x l k H Cpair CremP CremT +
      (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
        lemma6B20IntegralMajorant x l k H Cs Cd Cp C4)

/-! ### Scalar simplifications in the `D ≤ Y` regimes -/

/-- The pair-polynomial factor in the `A` majorant is bounded by a constant
multiple of the exceptional factor whenever `D ≤ Y`. -/
theorem lemma6A_pair_factor_le_twentyfive_exceptional
    {x l k : ℕ}
    (hD1 : 1 ≤ lemma6DyadicModulusScale x l)
    (hYpos : 0 < lemma6PairDyadicScale x k)
    (hDY : lemma6DyadicModulusScale x l ≤ lemma6PairDyadicScale x k) :
    lemma6ExceptionalFactorAt x l *
        (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
            10 * lemma6PairDyadicScale x k /
              lemma6DyadicModulusScale x l) *
          (2 / lemma6PairDyadicScale x k)) ≤
      25 * lemma6ExceptionalFactorAt x l := by
  let dScale := lemma6DyadicModulusScale x l
  let yScale := lemma6PairDyadicScale x k
  let eFactor := lemma6ExceptionalFactorAt x l
  have hDpos : 0 < dScale := zero_lt_one.trans_le hD1
  have hDYdiv : dScale / yScale ≤ 1 := (div_le_one hYpos).2 hDY
  have hDinv : 1 / dScale ≤ 1 := (div_le_one hDpos).2 hD1
  have hinner : (5 / 2 : ℝ) * (dScale / yScale) +
      20 * (1 / dScale) ≤ 25 := by
    nlinarith
  have hE0 : 0 ≤ eFactor := by
    dsimp only [eFactor]
    exact (lemma6ExceptionalFactor_pos _).le
  change eFactor * (((5 / 4 : ℝ) * dScale + 10 * yScale / dScale) *
      (2 / yScale)) ≤ 25 * eFactor
  calc eFactor * (((5 / 4 : ℝ) * dScale + 10 * yScale / dScale) *
          (2 / yScale)) =
        eFactor * ((5 / 2 : ℝ) * (dScale / yScale) +
          20 * ((yScale / yScale) * (1 / dScale))) := by ring
    _ =
        eFactor * ((5 / 2 : ℝ) * (dScale / yScale) +
          20 * (1 / dScale)) := by
      rw [div_self hYpos.ne']
      ring
    _ ≤ eFactor * 25 := mul_le_mul_of_nonneg_left hinner hE0
    _ = 25 * eFactor := by ring

/-- In the complementary equation-(20) region, the pair-polynomial factor
is controlled by `23 E D / Y`. -/
theorem lemma6A_pair_factor_le_twentythree_exceptional_mul_D_div_Y
    {x l k : ℕ}
    (hD1 : 1 ≤ lemma6DyadicModulusScale x l)
    (hYpos : 0 < lemma6PairDyadicScale x k)
    (hYD : lemma6PairDyadicScale x k ≤ lemma6DyadicModulusScale x l) :
    lemma6ExceptionalFactorAt x l *
        (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
            10 * lemma6PairDyadicScale x k /
              lemma6DyadicModulusScale x l) *
          (2 / lemma6PairDyadicScale x k)) ≤
      23 * lemma6ExceptionalFactorAt x l *
        (lemma6DyadicModulusScale x l / lemma6PairDyadicScale x k) := by
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  let E := lemma6ExceptionalFactorAt x l
  have hDpos : 0 < D := by dsimp only [D]; linarith
  have hYDD : Y ≤ D ^ 2 := by
    have hDsq : D ≤ D ^ 2 := by nlinarith
    exact hYD.trans hDsq
  have hquot : 1 / D ≤ D / Y := by
    rw [div_le_div_iff₀ hDpos hYpos]
    simpa only [one_mul, pow_two] using hYDD
  have hDY0 : 0 ≤ D / Y := by positivity
  have hinner : (5 / 2 : ℝ) * (D / Y) + 20 * (1 / D) ≤
      23 * (D / Y) := by
    nlinarith
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact (lemma6ExceptionalFactor_pos _).le
  change E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y)) ≤
    23 * E * (D / Y)
  calc
    E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y)) =
        E * ((5 / 2 : ℝ) * (D / Y) +
          20 * ((Y / Y) * (1 / D))) := by ring
    _ = E * ((5 / 2 : ℝ) * (D / Y) + 20 * (1 / D)) := by
          rw [div_self hYpos.ne']
          ring
    _ ≤ E * (23 * (D / Y)) := mul_le_mul_of_nonneg_left hinner hE0
    _ = 23 * E * (D / Y) := by ring

/-- A square-root quotient absorbs half of an available even logarithmic
power.  This is the elementary scalar step used for the `1 / D` term in
the equation-(19) `A` estimate. -/
theorem sqrt_mul_sqrt_inv_le_inv_pow
    {a b L : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hL : 0 < L)
    (hab : a * L ^ (2 * n) ≤ b) :
    Real.sqrt a * Real.sqrt (1 / b) ≤ 1 / L ^ n := by
  have hleft0 : 0 ≤ Real.sqrt a * Real.sqrt (1 / b) := by positivity
  have hright0 : 0 ≤ 1 / L ^ n := by positivity
  have hsquares :
      (Real.sqrt a * Real.sqrt (1 / b)) ^ 2 ≤
        (1 / L ^ n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt (by positivity)]
    rw [div_pow]
    have hp : (L ^ n) ^ 2 = L ^ (2 * n) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [one_pow, hp]
    rw [show a * (1 / b) = a / b by ring]
    exact (div_le_div_iff₀ hb (pow_pos hL (2 * n))).2 (by simpa using hab)
  exact le_of_pow_le_pow_left₀ (by norm_num) hright0 hsquares

/-- The corresponding cutoff form: a lower bound
`a * b * L^(2n) ≤ H` saves `L^n` after taking the two square roots. -/
theorem sqrt_mul_sqrt_div_le_inv_pow
    {a b H L : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hH : 0 < H) (hL : 0 < L)
    (habH : a * b * L ^ (2 * n) ≤ H) :
    Real.sqrt a * Real.sqrt (b / H) ≤ 1 / L ^ n := by
  have hleft0 : 0 ≤ Real.sqrt a * Real.sqrt (b / H) := by positivity
  have hright0 : 0 ≤ 1 / L ^ n := by positivity
  have hsquares :
      (Real.sqrt a * Real.sqrt (b / H)) ^ 2 ≤
        (1 / L ^ n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt (by positivity)]
    rw [div_pow]
    have hp : (L ^ n) ^ 2 = L ^ (2 * n) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [one_pow, hp]
    rw [show a * (b / H) = a * b / H by ring]
    exact (div_le_div_iff₀ hH (pow_pos hL (2 * n))).2 (by simpa using habH)
  exact le_of_pow_le_pow_left₀ (by norm_num) hright0 hsquares

/-- Scalar simplification of the integrated `A` term in either of the
equation-(19) regions.  The statement deliberately retains the three saved
logarithmic powers, so its eventual application does not need to unfold the
analytic majorant again. -/
theorem lemma6AIntegralMajorant_le_of_D_le_Y
    {x l k H : ℕ} {Cpair CremP CremT : ℝ}
    (_hCpair : 0 ≤ Cpair) (_hCremP : 0 ≤ CremP) (_hCremT : 0 ≤ CremT)
    (hL1 : 1 ≤ Real.log (x : ℝ))
    (_hlogH0 : 0 ≤ Real.log (H : ℝ))
    (hlogH : Real.log (H : ℝ) ≤ 8 * Real.log (x : ℝ))
    (hD1 : 1 ≤ lemma6DyadicModulusScale x l)
    (hE1 : 1 ≤ lemma6ExceptionalFactorAt x l)
    (hYpos : 0 < lemma6PairDyadicScale x k)
    (hDY : lemma6DyadicModulusScale x l ≤ lemma6PairDyadicScale x k)
    (hEL80 : lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 80 ≤
      lemma6DyadicModulusScale x l)
    (hEDL100 : lemma6ExceptionalFactorAt x l *
        lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 100 ≤ H) :
    lemma6AIntegralMajorant x l k H Cpair CremP CremT ≤
      80 * Real.pi * Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
        Real.log (x : ℝ) ^ 8 *
          (1 / Real.log (x : ℝ) ^ 50 +
            1 / Real.log (x : ℝ) ^ 40 +
            1 / Real.log (x : ℝ) ^ 100) := by
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  let E := lemma6ExceptionalFactorAt x l
  let K := Cpair * (36864 * CremP + 200 * CremT ^ 2)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hDpos : 0 < D := by dsimp only [D]; linarith
  have hE0 : 0 ≤ E := by dsimp only [E]; linarith
  have hHpos : (0 : ℝ) < H := by
    have hleft : 0 < E * D * L ^ 100 := by positivity
    exact hleft.trans_le (by exact_mod_cast hEDL100)
  have hpair : E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y)) ≤
      25 * E := by
    dsimp only [D, Y, E]
    exact lemma6A_pair_factor_le_twentyfive_exceptional hD1 hYpos hDY
  have hsqrt25 : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have hsqrtPair :
      Real.sqrt (E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y))) ≤
        5 * Real.sqrt E := by
    calc
      Real.sqrt (E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y))) ≤
          Real.sqrt (25 * E) := Real.sqrt_le_sqrt hpair
      _ = 5 * Real.sqrt E := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 25)]
        rw [hsqrt25]
  have hcut : E * D * L ^ 100 ≤ (H : ℝ) := by
    dsimp only [E, D, L]
    calc
      lemma6ExceptionalFactorAt x l * lemma6DyadicModulusScale x l *
          Real.log (x : ℝ) ^ 100 =
        lemma6ExceptionalFactorAt x l * lemma6DyadicModulusScale x l *
          Real.log (x : ℝ) ^ 100 := rfl
      _ ≤ (H : ℝ) := hEDL100
  have hfirst : Real.sqrt E * Real.sqrt (D / (H : ℝ)) ≤ 1 / L ^ 50 := by
    apply sqrt_mul_sqrt_div_le_inv_pow hE0 hDpos.le hHpos hLpos
    simpa only [show 2 * 50 = 100 by norm_num] using hcut
  have hsecond : Real.sqrt E * Real.sqrt (1 / D) ≤ 1 / L ^ 40 := by
    apply sqrt_mul_sqrt_inv_le_inv_pow hE0 hDpos hLpos
    simpa only [show 2 * 40 = 80 by norm_num] using hEL80
  have hsqrtE : Real.sqrt E ≤ E :=
    Real.sqrt_le_self_iff.mpr (Or.inr hE1)
  have hratio : E * (D / (H : ℝ)) ≤ 1 / L ^ 100 := by
    rw [show E * (D / (H : ℝ)) = E * D / (H : ℝ) by ring]
    apply (div_le_div_iff₀ hHpos (pow_pos hLpos 100)).2
    simpa only [mul_one, one_mul] using hcut
  have hthird : Real.sqrt E * (D / (H : ℝ)) ≤ 1 / L ^ 100 :=
    (mul_le_mul_of_nonneg_right hsqrtE (by positivity)).trans hratio
  have hsaved :
      Real.sqrt (E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y))) *
          (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ)) ≤
        5 * (1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100) := by
    calc
      Real.sqrt (E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y))) *
          (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ)) ≤
        (5 * Real.sqrt E) *
          (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ)) :=
            mul_le_mul_of_nonneg_right hsqrtPair (by positivity)
      _ ≤ 5 * (1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100) := by
        nlinarith
  have hsqrtL : Real.sqrt (L ^ 3) ≤ L ^ 2 := by
    calc Real.sqrt (L ^ 3) ≤ Real.sqrt (L ^ 4) := by
          apply Real.sqrt_le_sqrt
          nlinarith [pow_nonneg (show 0 ≤ L by linarith) 3]
      _ = L ^ 2 := by
          rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (sq_nonneg L)]
  unfold lemma6AIntegralMajorant
  change Real.sqrt K * Real.sqrt (L ^ 3) * Real.log (H : ℝ) *
      (Real.sqrt (E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y))) *
        (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ))) *
      (2 * Real.pi * L ^ 5) ≤ _
  calc
    Real.sqrt K * Real.sqrt (L ^ 3) * Real.log (H : ℝ) *
        (Real.sqrt (E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y))) *
          (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ))) *
        (2 * Real.pi * L ^ 5) ≤
      Real.sqrt K * L ^ 2 * (8 * L) *
        (5 * (1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100)) *
        (2 * Real.pi * L ^ 5) := by
          gcongr
    _ = 80 * Real.pi * Real.sqrt K * L ^ 8 *
        (1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100) := by ring

/-- Scalar simplification of the integrated `A` term in the equation-(20)
region `Y ≤ D`.  Both the cutoff lower bound and `E L^200 ≤ Y` give one
hundred logarithmic powers after taking square roots. -/
theorem lemma6AIntegralMajorant_le_of_Y_le_D
    {x l k H : ℕ} {Cpair CremP CremT : ℝ}
    (_hCpair : 0 ≤ Cpair) (_hCremP : 0 ≤ CremP) (_hCremT : 0 ≤ CremT)
    (hL1 : 1 ≤ Real.log (x : ℝ))
    (_hlogH0 : 0 ≤ Real.log (H : ℝ))
    (hlogH : Real.log (H : ℝ) ≤ 8 * Real.log (x : ℝ))
    (hD1 : 1 ≤ lemma6DyadicModulusScale x l)
    (hE1 : 1 ≤ lemma6ExceptionalFactorAt x l)
    (hYpos : 0 < lemma6PairDyadicScale x k)
    (hYD : lemma6PairDyadicScale x k ≤ lemma6DyadicModulusScale x l)
    (hEL200 : lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 200 ≤
      lemma6PairDyadicScale x k)
    (hcut : lemma6ExceptionalFactorAt x l *
        lemma6DyadicModulusScale x l ^ 2 * Real.log (x : ℝ) ^ 200 /
          lemma6PairDyadicScale x k ≤ H) :
    lemma6AIntegralMajorant x l k H Cpair CremP CremT ≤
      240 * Real.pi * Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) /
        Real.log (x : ℝ) ^ 92 := by
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  let E := lemma6ExceptionalFactorAt x l
  let K := Cpair * (36864 * CremP + 200 * CremT ^ 2)
  let P := E * (((5 / 4 : ℝ) * D + 10 * Y / D) * (2 / Y))
  let F := E * D ^ 2 * L ^ 200 / Y
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hDpos : 0 < D := by dsimp only [D]; linarith
  have hY0 : 0 ≤ Y := hYpos.le
  have hE0 : 0 ≤ E := by dsimp only [E]; linarith
  have hHpos : (0 : ℝ) < H := by
    have hFpos : 0 < F := by dsimp only [F]; positivity
    exact hFpos.trans_le (by simpa only [F] using hcut)
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hP : P ≤ 23 * E * (D / Y) := by
    dsimp only [P, E, D, Y]
    exact lemma6A_pair_factor_le_twentythree_exceptional_mul_D_div_Y
      hD1 hYpos hYD
  have hF : F ≤ (H : ℝ) := by simpa only [F] using hcut
  have hFdiv : F / (H : ℝ) ≤ 1 := (div_le_one hHpos).2 hF
  have hGdiv : E * L ^ 200 / Y ≤ 1 := by
    apply (div_le_one hYpos).2
    simpa only [E, L, Y] using hEL200
  have hfirstBase : P * (D / (H : ℝ)) ≤ 25 / L ^ 200 := by
    calc
      P * (D / (H : ℝ)) ≤
          (23 * E * (D / Y)) * (D / (H : ℝ)) :=
        mul_le_mul_of_nonneg_right hP (by positivity)
      _ = 23 * (F / (H : ℝ)) * (1 / L ^ 200) := by
        dsimp only [F]
        field_simp [hYpos.ne', hHpos.ne', hLpos.ne']
      _ ≤ 23 * 1 * (1 / L ^ 200) := by gcongr
      _ ≤ 25 / L ^ 200 := by
        rw [show 23 * 1 * (1 / L ^ 200) = 23 * (1 / L ^ 200) by ring,
          show 25 / L ^ 200 = 25 * (1 / L ^ 200) by ring]
        gcongr
        norm_num
  have hsecondBase : P * (1 / D) ≤ 25 / L ^ 200 := by
    calc
      P * (1 / D) ≤ (23 * E * (D / Y)) * (1 / D) :=
        mul_le_mul_of_nonneg_right hP (by positivity)
      _ = 23 * (E * L ^ 200 / Y) * (1 / L ^ 200) := by
        field_simp [hDpos.ne', hYpos.ne', hLpos.ne']
      _ ≤ 23 * 1 * (1 / L ^ 200) := by gcongr
      _ ≤ 25 / L ^ 200 := by
        rw [show 23 * 1 * (1 / L ^ 200) = 23 * (1 / L ^ 200) by ring,
          show 25 / L ^ 200 = 25 * (1 / L ^ 200) by ring]
        gcongr
        norm_num
  have hfirst : Real.sqrt P * Real.sqrt (D / (H : ℝ)) ≤ 5 / L ^ 100 := by
    have hsquares : (Real.sqrt P * Real.sqrt (D / (H : ℝ))) ^ 2 ≤
        (5 / L ^ 100) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt (by positivity)]
      calc
        P * (D / (H : ℝ)) ≤ 25 / L ^ 200 := hfirstBase
        _ = (5 / L ^ 100) ^ 2 := by
          field_simp [hLpos.ne']
          norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsquares
  have hsecond : Real.sqrt P * Real.sqrt (1 / D) ≤ 5 / L ^ 100 := by
    have hsquares : (Real.sqrt P * Real.sqrt (1 / D)) ^ 2 ≤
        (5 / L ^ 100) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt (by positivity)]
      calc
        P * (1 / D) ≤ 25 / L ^ 200 := hsecondBase
        _ = (5 / L ^ 100) ^ 2 := by
          field_simp [hLpos.ne']
          norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsquares
  have hDleF : D ≤ F := by
    have hratio : 1 ≤ E * D * L ^ 200 / Y := by
      rw [one_le_div hYpos]
      have hED : Y ≤ E * D := by
        calc Y ≤ D := hYD
          _ = 1 * D := by ring
          _ ≤ E * D := mul_le_mul_of_nonneg_right hE1 hDpos.le
      calc Y ≤ E * D := hED
        _ ≤ E * D * L ^ 200 := by
          have hpow : 1 ≤ L ^ 200 := one_le_pow₀ hL1
          nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hE0 hDpos.le)]
    dsimp only [F]
    rw [show E * D ^ 2 * L ^ 200 / Y =
        D * (E * D * L ^ 200 / Y) by
          field_simp [hYpos.ne']]
    nlinarith
  have hDH : D / (H : ℝ) ≤ 1 :=
    (div_le_one hHpos).2 (hDleF.trans hF)
  have hqSqrt : D / (H : ℝ) ≤ Real.sqrt (D / (H : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    have hq0 : 0 ≤ D / (H : ℝ) := by positivity
    nlinarith
  have hthird : Real.sqrt P * (D / (H : ℝ)) ≤ 5 / L ^ 100 :=
    (mul_le_mul_of_nonneg_left hqSqrt (Real.sqrt_nonneg P)).trans hfirst
  have hsaved : Real.sqrt P *
      (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ)) ≤
      15 / L ^ 100 := by
    calc
      Real.sqrt P *
          (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ)) =
        Real.sqrt P * Real.sqrt (D / (H : ℝ)) +
          Real.sqrt P * Real.sqrt (1 / D) + Real.sqrt P * (D / (H : ℝ)) := by ring
      _ ≤ 5 / L ^ 100 + 5 / L ^ 100 + 5 / L ^ 100 :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = 15 / L ^ 100 := by ring
  have hsqrtL : Real.sqrt (L ^ 3) ≤ L ^ 2 := by
    calc Real.sqrt (L ^ 3) ≤ Real.sqrt (L ^ 4) := by
          apply Real.sqrt_le_sqrt
          nlinarith [pow_nonneg (show 0 ≤ L by linarith) 3]
      _ = L ^ 2 := by
          rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (sq_nonneg L)]
  unfold lemma6AIntegralMajorant
  change Real.sqrt K * Real.sqrt (L ^ 3) * Real.log (H : ℝ) *
      (Real.sqrt P *
        (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ))) *
      (2 * Real.pi * L ^ 5) ≤ _
  calc
    Real.sqrt K * Real.sqrt (L ^ 3) * Real.log (H : ℝ) *
        (Real.sqrt P *
          (Real.sqrt (D / (H : ℝ)) + Real.sqrt (1 / D) + D / (H : ℝ))) *
        (2 * Real.pi * L ^ 5) ≤
      Real.sqrt K * L ^ 2 * (8 * L) * (15 / L ^ 100) *
        (2 * Real.pi * L ^ 5) := by gcongr
    _ = 240 * Real.pi * Real.sqrt K / L ^ 92 := by
      field_simp [hLpos.ne']
      ring

/-- The three logarithmic savings left by the preceding `A` estimate give
thirty-two powers after its elementary positive factors are collected. -/
theorem log_eight_mul_saved_terms_le {L : ℝ} (hL : 1 ≤ L) :
    L ^ 8 * (1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100) ≤
      3 / L ^ 32 := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have h4050 : L ^ 40 ≤ L ^ 50 :=
    pow_le_pow_right₀ hL (by norm_num)
  have h40100 : L ^ 40 ≤ L ^ 100 :=
    pow_le_pow_right₀ hL (by norm_num)
  have h50 : 1 / L ^ 50 ≤ 1 / L ^ 40 :=
    one_div_le_one_div_of_le (pow_pos hLpos 40) h4050
  have h100 : 1 / L ^ 100 ≤ 1 / L ^ 40 :=
    one_div_le_one_div_of_le (pow_pos hLpos 40) h40100
  calc
    L ^ 8 * (1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100) ≤
        L ^ 8 * (3 / L ^ 40) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100 ≤
                1 / L ^ 40 + 1 / L ^ 40 + 1 / L ^ 40 := by
                  exact add_le_add (add_le_add h50 le_rfl) h100
            _ = 3 / L ^ 40 := by ring
    _ = 3 / L ^ 32 := by
      field_simp [hLpos.ne']

/-- Scalar simplification of the integrated equation-(19) `B` term in the
two `D ≤ Y` regions.  Raising the three Hölder roots to the fourth power
reduces the proof to polynomial algebra and leaves the paper's useful
`E (D + sqrt Y)` shape. -/
theorem lemma6BIntegralMajorant_le_of_D_le_Y
    {x l k H : ℕ} {Cp Cm Cd : ℝ}
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hCd : 0 ≤ Cd)
    (hL1 : 1 ≤ Real.log (x : ℝ))
    (hD1 : 1 ≤ lemma6DyadicModulusScale x l)
    (hYpos : 0 < lemma6PairDyadicScale x k)
    (_hlogU0 : 0 ≤ 1 + Real.log (lemma6PairUpperCutoff x k : ℕ))
    (hlogU : 1 + Real.log (lemma6PairUpperCutoff x k : ℕ) ≤
      2 * Real.log (x : ℝ))
    (hmoll : (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * ((H * H : ℕ) : ℝ) / lemma6DyadicModulusScale x l ≤
        18 * lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 200 *
          lemma6ExceptionalFactorAt x l ^ 2)
    (_hlogHH0 : 0 ≤ Real.log ((H * H : ℕ) : ℝ))
    (hlogHH : Real.log ((H * H : ℕ) : ℝ) ≤
      8 * Real.log (x : ℝ)) :
    lemma6BIntegralMajorant x l k H Cp Cm Cd ≤
      32 * Real.pi * (10368 * Cp ^ 2 * Cm * Cd) ^ ((1 : ℝ) / 4) *
        lemma6ExceptionalFactorAt x l *
        (lemma6DyadicModulusScale x l +
          Real.sqrt (lemma6PairDyadicScale x k)) *
        Real.log (x : ℝ) ^ 60 := by
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  let E := lemma6ExceptionalFactorAt x l
  let Ulog := 1 + Real.log (lemma6PairUpperCutoff x k : ℕ)
  let Ppoly := (5 / 4 : ℝ) * D + 10 * Y / D
  let Mfac := (5 / 4 : ℝ) * D + 4 * ((H * H : ℕ) : ℝ) / D
  let P := E * Cp * (Ppoly * Ulog)
  let M := Cm * Mfac
  let R := Cd * ((2 : ℝ) ^ l * L ^ 110)
  let S := D + Real.sqrt Y
  let C := 10368 * Cp ^ 2 * Cm * Cd
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hDpos : 0 < D := by dsimp only [D]; linarith
  have hY0 : 0 ≤ Y := hYpos.le
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact (lemma6ExceptionalFactor_pos _).le
  have hPpoly0 : 0 ≤ Ppoly := by dsimp only [Ppoly]; positivity
  have hMfac0 : 0 ≤ Mfac := by dsimp only [Mfac]; positivity
  have hP0 : 0 ≤ P := by dsimp only [P, Ulog]; positivity
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hDP : D * Ppoly ≤ 12 * S ^ 2 := by
    have hsqrt : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0
    dsimp only [Ppoly, S]
    rw [show D * ((5 / 4 : ℝ) * D + 10 * Y / D) =
        (5 / 4 : ℝ) * D ^ 2 + 10 * Y by
          field_simp [hDpos.ne']]
    nlinarith [mul_nonneg hDpos.le (Real.sqrt_nonneg Y)]
  have hDPsq : (D * Ppoly) ^ 2 ≤ (12 * S ^ 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hDpos.le hPpoly0) hDP 2
  have hL212 : L ^ 212 ≤ L ^ 216 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hP : P ≤ E * Cp * (Ppoly * (2 * L)) := by
    dsimp only [P, Ulog]
    gcongr
  have hM : M ≤ Cm * (18 * D * L ^ 200 * E ^ 2) := by
    dsimp only [M, Mfac, D, L, E] at hmoll ⊢
    exact mul_le_mul_of_nonneg_left hmoll hCm
  have hR : R = Cd * (D * L ^ 10) := by
    dsimp only [R, D, L]
    unfold lemma6DyadicModulusScale
    ring
  have hbase : ((P ^ 2) * M) * R ≤ C * (E * S * L ^ 54) ^ 4 := by
    calc
      ((P ^ 2) * M) * R ≤
          (((E * Cp * (Ppoly * (2 * L))) ^ 2) *
            (Cm * (18 * D * L ^ 200 * E ^ 2))) *
            (Cd * (D * L ^ 10)) := by
              rw [hR]
              gcongr
      _ = 72 * Cp ^ 2 * Cm * Cd * E ^ 4 *
          (D * Ppoly) ^ 2 * L ^ 212 := by ring
      _ ≤ 72 * Cp ^ 2 * Cm * Cd * E ^ 4 *
          (12 * S ^ 2) ^ 2 * L ^ 212 := by gcongr
      _ = C * E ^ 4 * S ^ 4 * L ^ 212 := by
          dsimp only [C]
          ring
      _ ≤ C * E ^ 4 * S ^ 4 * L ^ 216 := by gcongr
      _ = C * (E * S * L ^ 54) ^ 4 := by ring
  have hroot : P ^ ((1 : ℝ) / 2) *
      (M ^ ((1 : ℝ) / 4) * R ^ ((1 : ℝ) / 4)) ≤
      C ^ ((1 : ℝ) / 4) * (E * S * L ^ 54) := by
    calc
      P ^ ((1 : ℝ) / 2) *
          (M ^ ((1 : ℝ) / 4) * R ^ ((1 : ℝ) / 4)) =
        (((P ^ 2) * M) * R) ^ ((1 : ℝ) / 4) :=
          (real_rpow_quarter_combine hP0 hM0 hR0).symm
      _ ≤ (C * (E * S * L ^ 54) ^ 4) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = C ^ ((1 : ℝ) / 4) * (E * S * L ^ 54) := by
        rw [Real.mul_rpow hC0 (pow_nonneg (by positivity) 4),
          ← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity)]
        norm_num
  unfold lemma6BIntegralMajorant
  change P ^ ((1 : ℝ) / 2) *
      ((M ^ ((1 : ℝ) / 4) * Real.log ((H * H : ℕ) : ℝ)) *
        R ^ ((1 : ℝ) / 4)) * (4 * Real.pi * L ^ 5) ≤ _
  calc
    P ^ ((1 : ℝ) / 2) *
        ((M ^ ((1 : ℝ) / 4) * Real.log ((H * H : ℕ) : ℝ)) *
          R ^ ((1 : ℝ) / 4)) * (4 * Real.pi * L ^ 5) =
      (P ^ ((1 : ℝ) / 2) *
          (M ^ ((1 : ℝ) / 4) * R ^ ((1 : ℝ) / 4))) *
        Real.log ((H * H : ℕ) : ℝ) * (4 * Real.pi * L ^ 5) := by ring
    _ ≤ (C ^ ((1 : ℝ) / 4) * (E * S * L ^ 54)) *
        (8 * L) * (4 * Real.pi * L ^ 5) := by gcongr
    _ = 32 * Real.pi * C ^ ((1 : ℝ) / 4) * E * S * L ^ 60 := by ring

/-- In the equation-(20) region `Y ≤ D`, the fourth-moment pair polynomial
is at most `27 D`. -/
theorem lemma6B20_pair_polynomial_le_twentyseven_D
    {x l k : ℕ}
    (hDpos : 0 < lemma6DyadicModulusScale x l)
    (hYD : lemma6PairDyadicScale x k ≤ lemma6DyadicModulusScale x l) :
    (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        25 * lemma6PairDyadicScale x k ^ 2 /
          lemma6DyadicModulusScale x l ≤
      27 * lemma6DyadicModulusScale x l := by
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  have hY0 : 0 ≤ Y := lemma6PairDyadicScale_nonneg x k
  have hYsq : Y ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ hY0 hYD 2
  have hdiv : Y ^ 2 / D ≤ D := by
    rw [div_le_iff₀ (by simpa only [D] using hDpos)]
    simpa only [pow_two] using hYsq
  have hD0 : 0 ≤ D := by dsimp only [D]; exact hDpos.le
  change (5 / 4 : ℝ) * D + 25 * Y ^ 2 / D ≤ 27 * D
  calc
    (5 / 4 : ℝ) * D + 25 * Y ^ 2 / D ≤
        (5 / 4 : ℝ) * D + 25 * D := by
          rw [show 25 * Y ^ 2 / D = 25 * (Y ^ 2 / D) by ring]
          simpa only [add_comm] using
            add_le_add_left (mul_le_mul_of_nonneg_left hdiv
              (show (0 : ℝ) ≤ 25 by norm_num)) ((5 / 4 : ℝ) * D)
    _ ≤ 27 * D := by nlinarith

set_option maxRecDepth 10000 in
/-- Fourth-power scalar simplification of the integrated equation-(20) `B`
term.  The hypotheses expose exactly the three elementary bounds supplied by
the cutoff and occupied-block bookkeeping. -/
theorem lemma6B20IntegralMajorant_le
    {x l k H : ℕ} {T Cs Cd Cp C4 : ℝ}
    (hCs : 0 ≤ Cs) (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hC4 : 0 ≤ C4)
    (hL1 : 1 ≤ Real.log (x : ℝ))
    (hDpos : 0 < lemma6DyadicModulusScale x l)
    (hT0 : 0 ≤ T)
    (hMDbound :
      (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * (H : ℝ) / lemma6DyadicModulusScale x l) *
        lemma6DyadicModulusScale x l) ≤ 32 * T ^ 2)
    (_hlogH0 : 0 ≤ 1 + Real.log (H : ℝ))
    (hlogH : 1 + Real.log (H : ℝ) ≤ 9 * Real.log (x : ℝ))
    (hpair0 : 0 ≤ (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        25 * lemma6PairDyadicScale x k ^ 2 /
          lemma6DyadicModulusScale x l)
    (hpair : (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
        25 * lemma6PairDyadicScale x k ^ 2 /
          lemma6DyadicModulusScale x l ≤
      27 * lemma6DyadicModulusScale x l)
    (_hlogU0 : 0 ≤ Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ))
    (hlogU : Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ≤
      2 * Real.log (x : ℝ)) :
    lemma6B20IntegralMajorant x l k H Cs Cd Cp C4 ≤
      4 * Real.pi *
        (35831808 * Cs ^ 2 * Cd * Cp * C4) ^ ((1 : ℝ) / 4) *
        Real.sqrt (lemma6ExceptionalFactorAt x l) * T *
        Real.log (x : ℝ) ^ 9 := by
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let E := lemma6ExceptionalFactorAt x l
  let Mbase := (5 / 4 : ℝ) * D + 4 * (H : ℝ) / D
  let Pbase := (5 / 4 : ℝ) * D + 25 * lemma6PairDyadicScale x k ^ 2 / D
  let Bbase := lemma6B20BaseMajorant x l k H Cs Cd Cp C4
  let C := 35831808 * Cs ^ 2 * Cd * Cp * C4
  let R := Real.sqrt E * T * L ^ 4
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact (lemma6ExceptionalFactor_pos _).le
  have hMbase0 : 0 ≤ Mbase := by
    dsimp only [Mbase, D]
    positivity
  have hPbase0 : 0 ≤ Pbase := by simpa only [Pbase, D] using hpair0
  have hBbase0 : 0 ≤ Bbase := by
    dsimp only [Bbase]
    unfold lemma6B20BaseMajorant
    positivity
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hder : (2 : ℝ) ^ l * L ^ 110 = D * L ^ 10 := by
    dsimp only [D, L]
    unfold lemma6DyadicModulusScale
    ring
  have hbase : Bbase ≤ C * R ^ 4 := by
    dsimp only [Bbase]
    unfold lemma6B20BaseMajorant
    change
      (E * (Cs * (Mbase * (1 + Real.log (H : ℝ))))) ^ 2 *
          (Cd * ((2 : ℝ) ^ l * L ^ 110)) *
          ((Cp * C4) * (Pbase *
            Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4)) ≤ C * R ^ 4
    calc
      (E * (Cs * (Mbase * (1 + Real.log (H : ℝ))))) ^ 2 *
          (Cd * ((2 : ℝ) ^ l * L ^ 110)) *
          ((Cp * C4) * (Pbase *
            Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4)) ≤
        (E * (Cs * (Mbase * (9 * L)))) ^ 2 *
          (Cd * (D * L ^ 10)) *
          ((Cp * C4) * ((27 * D) * (2 * L) ^ 4)) := by
            rw [hder]
            gcongr
      _ = 34992 * Cs ^ 2 * Cd * Cp * C4 * E ^ 2 *
          (Mbase * D) ^ 2 * L ^ 16 := by ring
      _ ≤ 34992 * Cs ^ 2 * Cd * Cp * C4 * E ^ 2 *
          (32 * T ^ 2) ^ 2 * L ^ 16 := by
            gcongr
      _ = C * E ^ 2 * T ^ 4 * L ^ 16 := by
            dsimp only [C]
            ring
      _ = C * R ^ 4 := by
            dsimp only [R]
            have he : E ^ 2 = Real.sqrt E ^ 4 := by
              rw [show Real.sqrt E ^ 4 = (Real.sqrt E ^ 2) ^ 2 by ring,
                Real.sq_sqrt hE0]
            rw [he]
            ring
  have hroot : Bbase ^ ((1 : ℝ) / 4) ≤ C ^ ((1 : ℝ) / 4) * R := by
    calc
      Bbase ^ ((1 : ℝ) / 4) ≤ (C * R ^ 4) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hBbase0 hbase (by norm_num)
      _ = C ^ ((1 : ℝ) / 4) * R := by
        rw [Real.mul_rpow hC0 (pow_nonneg hR0 4), ← Real.rpow_natCast,
          ← Real.rpow_mul hR0]
        norm_num
  unfold lemma6B20IntegralMajorant
  change Bbase ^ ((1 : ℝ) / 4) * (4 * Real.pi * L ^ 5) ≤ _
  calc
    Bbase ^ ((1 : ℝ) / 4) * (4 * Real.pi * L ^ 5) ≤
        (C ^ ((1 : ℝ) / 4) * R) * (4 * Real.pi * L ^ 5) :=
      mul_le_mul_of_nonneg_right hroot (by positivity)
    _ = 4 * Real.pi * C ^ ((1 : ℝ) / 4) * Real.sqrt E * T * L ^ 9 := by
      dsimp only [R]
      ring

/-- The equation-(20) pointwise fourth-root estimate integrated against the
shifted-line kernel. -/
theorem integrable_and_integral_kernelNorm_mul_B20Block_le
    {x l m k H : ℕ} {Cs Cd Cp C4 : ℝ}
    (hCs : 0 ≤ Cs) (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hC4 : 0 ≤ C4)
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hY : 2 ≤ lemma6PairDyadicScale x k) (hH2 : 2 ≤ H)
    (hmol2 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x nu) i ^ 2) ≤
        Cs * lemma6MollifierSecondMajorant x l H)
    (hder4 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x nu) i ^ 4) ≤
        Cd * lemma6DerivativeFourthMajorant x l nu)
    (hpair4 : ∀ nu : ℝ,
      (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6PairBlockNorm x m k (lemma6BetaPoint x nu) i ^ 4) ≤
        Cp * lemma6PairFourthMajorant x l m k (lemma6BetaPoint x nu))
    (hpairMajorant : ∀ nu : ℝ,
      lemma6PairFourthMajorant x l m k (lemma6BetaPoint x nu) ≤
        C4 * (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          25 * lemma6PairDyadicScale x k ^ 2 /
            lemma6DyadicModulusScale x l) *
          Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ) ^ 4)) :
    Integrable (fun nu : ℝ =>
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu) ∧
      (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu) ≤
        lemma6B20IntegralMajorant x l k H Cs Cd Cp C4 := by
  have hlogH0 : (0 : ℝ) ≤ Real.log (H : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (show 1 ≤ H by omega)
  have hbase0 : 0 ≤ lemma6B20BaseMajorant x l k H Cs Cd Cp C4 := by
    unfold lemma6B20BaseMajorant
    positivity
  have hcoef0 : 0 ≤
      lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hbase0 _
  have hBpoint : ∀ nu : ℝ, lemma6BBlockAtBeta x m l k H nu ≤
      lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
        (1 + nu ^ 2) ^ ((1 : ℝ) / 4) := by
    intro nu
    exact bblock_eq20_majorant nu hCs hCd hCp hC4 hxlarge hxlog hl hD4 hY hH2
      (hmol2 nu) (hder4 nu) (hpair4 nu) (hpairMajorant nu)
  have hint := integrable_kernelNorm_mul_lemma6BBlockAtBeta_of_le
    hxlog m k H hcoef0 hBpoint
  have hmass := integral_kernelNorm_mul_rpow_quarter_le hxlog
  have hpoint : ∀ nu : ℝ,
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
        lemma6BBlockAtBeta x m l k H nu ≤
      lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
        (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) := by
    intro nu
    have hk : (0 : ℝ) ≤ ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x nu)‖ := norm_nonneg _
    calc
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu ≤
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          (lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (hBpoint nu) hk
      _ = lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
          (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) := by ring
  have hint2 := (integrable_kernelNorm_mul_rpow_quarter hxlog).const_mul
    (lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4))
  refine ⟨hint, ?_⟩
  calc
    (∫ nu : ℝ,
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
          lemma6BBlockAtBeta x m l k H nu) ≤
      ∫ nu : ℝ,
        lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
          (‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4)) :=
      MeasureTheory.integral_mono hint hint2 hpoint
    _ = lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
        ∫ nu : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x nu)‖ *
            (1 + nu ^ 2) ^ ((1 : ℝ) / 4) :=
      MeasureTheory.integral_const_mul _ _
    _ ≤ lemma6B20BaseMajorant x l k H Cs Cd Cp C4 ^ ((1 : ℝ) / 4) *
        (4 * Real.pi * Real.log (x : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_left hmass hcoef0
    _ = lemma6B20IntegralMajorant x l k H Cs Cd Cp C4 := by
      rfl

end Chen
