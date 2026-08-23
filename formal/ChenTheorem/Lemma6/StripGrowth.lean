/-
Vertical-strip growth bounds for Dirichlet `L`-functions of primitive
characters, needed for the contour shift in equation (17) of Lemma 6.

The Pólya–Vinogradov bound (`primitive_character_prefix_sum_norm_le`)
supplies bounded partial sums for a primitive nonprincipal character.
Inserted into the Mellin (partial summation) representation

  `LSeries ↗χ s = s * ∫ t in Ioi 1, S(⌊t⌋) * t^(-(s+1))`,

this shows that the right-hand side is analytic on the half-plane
`0 < re s`, where it must coincide with the analytically continued
`LFunction` (identity principle).  The explicit bound
`‖L(s, χ)‖ ≤ 3 √q log(2q) · ‖s‖ / re s` follows, and Cauchy's integral
formula on the disc of radius `re s / 2` turns it into the polynomial
derivative bound `‖L'(s, χ)‖ ≤ 144 √q log(2q) ‖s‖` on the strip
`1/2 ≤ re s ≤ 2`.
-/
import ChenTheorem.Lemma6.PolyaVinogradov
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Function.Floor

open Real Set MeasureTheory Filter Asymptotics Topology
open scoped Classical

namespace Chen

/-- The `Icc` partial sums of a primitive character are bounded by the
Pólya–Vinogradov constant. -/
theorem primitive_char_sum_Icc_norm_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)‖ ≤
      3 * Real.sqrt q * Real.log (2 * q) := by
  have hI : Fact (1 < q) := ⟨by omega⟩
  have h0 : (χ ((0 : ℕ) : ZMod q) : ℂ) = 0 :=
    MulChar.map_nonunit χ (by
      rw [Nat.cast_zero]
      exact not_isUnit_zero)
  have hsum : (∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) =
      ∑ k ∈ Finset.range (n + 1), (χ k : ℂ) := by
    have hset : Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
      omega
    have hmem : 0 ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos n)
    rw [hset]
    conv_rhs => rw [← Finset.insert_erase hmem,
      Finset.sum_insert (by simp : (0 : ℕ) ∉ (Finset.range (n + 1)).erase 0),
      h0, zero_add]
  rw [hsum]
  exact primitive_character_prefix_sum_norm_le hχ hq (n + 1)

/-- The partial sums of a primitive character are `O(1)` at infinity. -/
theorem primitive_char_sum_Icc_isBigO {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) := by
  rw [isBigO_iff]
  refine ⟨3 * Real.sqrt q * Real.log (2 * q),
    Eventually.of_forall fun n => ?_⟩
  simp only [Real.rpow_zero, norm_one, mul_one]
  exact primitive_char_sum_Icc_norm_le hχ hq n

/-- Step function formed from the partial character sums: the kernel of the
Mellin (partial summation) representation of the `L`-series. -/
noncomputable def charPartialSumStep {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (χ k : ℂ)

theorem measurable_charPartialSumStep {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Measurable (charPartialSumStep χ) := by
  have h1 : Measurable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) :=
    measurable_of_countable _
  have h2 : Measurable (fun t : ℝ => ⌊t⌋₊) := Nat.measurable_floor
  have h3 := h1.comp h2
  exact h3

/-- On `t > 1` the complex power factor is an exponential, hence continuous
in `t`. -/
theorem continuousOn_cpow_neg_succ_of_one_lt (w : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(w + 1))) (Set.Ioi 1) := by
  have heq : Set.EqOn (fun t : ℝ => (t : ℂ) ^ (-(w + 1)))
      (fun t : ℝ => Complex.exp (Complex.log (t : ℂ) * (-(w + 1))))
      (Set.Ioi 1) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans ht).ne'
    exact Complex.cpow_def_of_ne_zero ht0 _
  have hlog : ContinuousOn (fun t : ℝ => Complex.log (t : ℂ))
      (Set.Ioi 1) := by
    have heq2 : Set.EqOn (fun t : ℝ => Complex.log (t : ℂ))
        (fun t : ℝ => (Real.log t : ℂ)) (Set.Ioi 1) := by
      intro t ht
      show Complex.log (t : ℂ) = (Real.log t : ℂ)
      rw [← Complex.ofReal_log (zero_le_one.trans ht.le)]
    have hcont2 : ContinuousOn (fun t : ℝ => (Real.log t : ℂ))
        (Set.Ioi 1) :=
      Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun t ht =>
          ne_of_gt (zero_lt_one.trans ht))
    exact hcont2.congr heq2
  have hcont : ContinuousOn
      (fun t : ℝ => Complex.exp (Complex.log (t : ℂ) * (-(w + 1))))
      (Set.Ioi 1) :=
    ContinuousOn.comp Complex.continuous_exp.continuousOn
      (hlog.mul continuousOn_const) (Set.mapsTo_univ _ _)
  exact hcont.congr heq

/-- For `0 < re s₀` the Mellin integral is differentiable in `s`, with the
expected derivative.  This is the analytic input identifying the partial
summation representation with the continued `L`-function. -/
theorem hasDerivAt_mellin_integral {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    HasDerivAt
      (fun s : ℂ => ∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)))
      (∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s₀ + 1)) *
          (-(Real.log t : ℂ))) s₀ := by
  set B : ℝ := 3 * Real.sqrt q * Real.log (2 * q) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (show 1 ≤ q by omega)
    have h2 : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  set σ₀ : ℝ := s₀.re with hσ₀
  set δ : ℝ := σ₀ / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set F : ℂ → ℝ → ℂ := fun s t =>
    charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)) with hF
  set F' : ℂ → ℝ → ℂ := fun s t =>
    charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)) *
      (-(Real.log t : ℂ)) with hF'
  set bound : ℝ → ℝ := fun t =>
    B * (4 / σ₀) * t ^ (-(1 + σ₀ / 4)) with hbound
  have hball : Metric.ball s₀ δ ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ hδpos
  have hre_sub : ∀ s ∈ Metric.ball s₀ δ, σ₀ / 2 ≤ s.re := by
    intro s hs
    have hdist : dist s s₀ < δ := Metric.mem_ball.mp hs
    have hre : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
    rw [← dist_eq_norm] at hre
    have hre' : (s - s₀).re = s.re - σ₀ := by
      simp [Complex.sub_re, hσ₀]
    rw [hre'] at hre
    rcases abs_le.mp hre with ⟨h1, _⟩
    linarith
  -- measurability of the integrand for every parameter
  have hF_meas : ∀ s : ℂ, AEStronglyMeasurable (F s)
      (volume.restrict (Set.Ioi 1)) := fun s =>
    (measurable_charPartialSumStep χ).aestronglyMeasurable.mul
      ((continuousOn_cpow_neg_succ_of_one_lt s).aestronglyMeasurable
        measurableSet_Ioi)
  -- integrability of the integrand at each parameter with positive real part
  have hF_int : ∀ s : ℂ, 0 < s.re → Integrable (F s)
      (volume.restrict (Set.Ioi 1)) := by
    intro s hs
    have hmajor : Integrable (fun t : ℝ => B * t ^ (-(s.re + 1)))
        (volume.restrict (Set.Ioi 1)) :=
      (integrableOn_Ioi_rpow_of_lt
        (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul B
    apply hmajor.mono' (hF_meas s)
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have hre : (-(s + 1)).re = -(s.re + 1) := by
      simp [Complex.neg_re, Complex.add_re]
    have hstep := primitive_char_sum_Icc_norm_le hχ hq ⌊t⌋₊
    rw [← hB] at hstep
    simp only [hF]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
    exact mul_le_mul hstep le_rfl (Real.rpow_nonneg ht0.le _) hB0
  -- measurability of the derivative at `s₀`
  have hF'_meas : AEStronglyMeasurable (F' s₀)
      (volume.restrict (Set.Ioi 1)) := by
    have hlog : ContinuousOn (fun t : ℝ => (-(Real.log t : ℂ)))
        (Set.Ioi 1) :=
      (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun t ht =>
          ne_of_gt (zero_lt_one.trans ht))).neg
    exact ((measurable_charPartialSumStep χ).aestronglyMeasurable.mul
      ((continuousOn_cpow_neg_succ_of_one_lt s₀).aestronglyMeasurable
        measurableSet_Ioi)).mul
      (hlog.aestronglyMeasurable measurableSet_Ioi)
  -- domination of the derivative
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 1)),
      ∀ s ∈ Metric.ball s₀ δ, ‖F' s t‖ ≤ bound t := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht s hs
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have ht1 : (1 : ℝ) ≤ t := ht.le
    have hre := hre_sub s hs
    have hlogpos : 0 < Real.log t := Real.log_pos ht
    have hnorm : ‖F' s t‖ = ‖charPartialSumStep χ t‖ *
        t ^ (-(s.re + 1)) * Real.log t := by
      simp only [hF']
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
        norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogpos]
      have hre' : (-(s + 1)).re = -(s.re + 1) := by
        simp [Complex.neg_re, Complex.add_re]
      rw [hre']
    rw [hnorm]
    have hexp : t ^ (-(s.re + 1)) ≤ t ^ (-(1 + σ₀ / 2)) := by
      apply Real.rpow_le_rpow_of_exponent_le ht1
      linarith
    have hlogle : Real.log t ≤ (4 / σ₀) * t ^ (σ₀ / 4) := by
      have hσ4 : (0 : ℝ) < σ₀ / 4 := by positivity
      have hrp : Real.log (t ^ (σ₀ / 4)) = (σ₀ / 4) * Real.log t :=
        Real.log_rpow ht0 _
      have harg : (0 : ℝ) < t ^ (σ₀ / 4) := Real.rpow_pos_of_pos ht0 _
      have h := Real.log_le_sub_one_of_pos harg
      have h1 : Real.log t = (4 / σ₀) * ((σ₀ / 4) * Real.log t) := by
        rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hs₀)]
        ring
      calc
        Real.log t = (4 / σ₀) * Real.log (t ^ (σ₀ / 4)) := by
          rw [h1, hrp]
        _ ≤ (4 / σ₀) * (t ^ (σ₀ / 4) - 1) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        _ ≤ (4 / σ₀) * t ^ (σ₀ / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [Real.rpow_nonneg ht0.le (σ₀ / 4)]
    have hstep := primitive_char_sum_Icc_norm_le hχ hq ⌊t⌋₊
    rw [← hB] at hstep
    have hexp0 : 0 ≤ t ^ (-(s.re + 1)) := Real.rpow_nonneg ht0.le _
    have hexp0' : 0 ≤ t ^ (-(1 + σ₀ / 2)) := Real.rpow_nonneg ht0.le _
    calc
      ‖charPartialSumStep χ t‖ * t ^ (-(s.re + 1)) * Real.log t ≤
          B * t ^ (-(1 + σ₀ / 2)) * Real.log t :=
        mul_le_mul (mul_le_mul hstep hexp hexp0 hB0) le_rfl
          hlogpos.le (mul_nonneg hB0 hexp0')
      _ ≤ B * t ^ (-(1 + σ₀ / 2)) * ((4 / σ₀) * t ^ (σ₀ / 4)) :=
        mul_le_mul_of_nonneg_left hlogle (mul_nonneg hB0 hexp0')
      _ = bound t := by
        rw [hbound]
        have hpow : t ^ (-(1 + σ₀ / 2)) * t ^ (σ₀ / 4) =
            t ^ (-(1 + σ₀ / 4)) := by
          have hsum : -(1 + σ₀ / 2) + σ₀ / 4 = -(1 + σ₀ / 4) := by ring
          rw [← hsum, Real.rpow_add ht0]
        calc
          B * t ^ (-(1 + σ₀ / 2)) * ((4 / σ₀) * t ^ (σ₀ / 4)) =
              B * (4 / σ₀) * (t ^ (-(1 + σ₀ / 2)) * t ^ (σ₀ / 4)) := by
            ring
          _ = B * (4 / σ₀) * t ^ (-(1 + σ₀ / 4)) := by rw [hpow]
  -- integrability of the bound
  have bound_integrable : Integrable bound (volume.restrict (Set.Ioi 1)) := by
    rw [hbound]
    exact (integrableOn_Ioi_rpow_of_lt
      (by linarith : -(1 + σ₀ / 4) < -1) zero_lt_one).const_mul (B * (4 / σ₀))
  -- differentiability of the integrand
  have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ioi 1)),
      ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (F · t) (F' s t) s := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht s _
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hexp : HasDerivAt
        (fun s : ℂ => Complex.exp (Complex.log (t : ℂ) * -(s + 1)))
        (Complex.exp (Complex.log (t : ℂ) * -(s + 1)) *
          (Complex.log (t : ℂ) * -1)) s := by
      have h1 : HasDerivAt (fun s : ℂ => -(s + 1)) (-1) s :=
        (hasDerivAt_id s |>.add_const 1).neg
      have h2 : HasDerivAt (fun s : ℂ => Complex.log (t : ℂ) * -(s + 1))
          (Complex.log (t : ℂ) * -1) s := h1.const_mul _
      exact h2.cexp
    have hF'eq : F' s t = charPartialSumStep χ t *
        (Complex.exp (Complex.log (t : ℂ) * -(s + 1)) *
          (Complex.log (t : ℂ) * -1)) := by
      simp only [hF']
      rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
      ring
    rw [hF'eq]
    have hFeq : (F · t) = fun s : ℂ => charPartialSumStep χ t *
        Complex.exp (Complex.log (t : ℂ) * -(s + 1)) := by
      funext s'
      simp only [hF]
      rw [Complex.cpow_def_of_ne_zero htC]
    rw [hFeq]
    exact hexp.const_mul _
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hball (Eventually.of_forall hF_meas) (hF_int s₀ hs₀) hF'_meas
    h_bound bound_integrable h_diff
  simp only [hF, hF'] at hderiv
  exact hderiv

/-- On the half-plane `0 < re s`, the `L`-function of a primitive character
of modulus at least two equals its partial-summation (Mellin) integral. -/
theorem LFunction_eq_mellin_integral {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hχne : χ ≠ 1 := by
    intro hχone
    have hcondOne : χ.conductor = 1 :=
      DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  have hU : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_Ioi.preimage Complex.continuous_re
  have hGdiff : DifferentiableOn ℂ (fun s : ℂ => s * ∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)))
      {s : ℂ | 0 < s.re} := by
    intro s hs
    have hs0 : 0 < s.re := hs
    exact ((((hasDerivAt_id s).mul
      (hasDerivAt_mellin_integral hχ hq hs0)).differentiableAt).differentiableWithinAt)
  have hGan : AnalyticOnNhd ℂ (fun s : ℂ => s * ∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)))
      {s : ℂ | 0 < s.re} :=
    hGdiff.analyticOnNhd hU
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      {s : ℂ | 0 < s.re} :=
    ((DirichletCharacter.differentiable_LFunction
      hχne).differentiableOn).analyticOnNhd hU
  have hconv : Convex ℝ {s : ℂ | 0 < s.re} := by
    intro a ha b hb u v hu hv huv
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul,
      smul_eq_mul]
    rcases eq_or_lt_of_le hu with hu0 | hupos
    · subst hu0
      have hv1 : v = 1 := by linarith
      subst hv1
      simpa using hb
    · have h1p : 0 < u * a.re := mul_pos hupos ha
      have h2p : 0 ≤ v * b.re := mul_nonneg hv hb.le
      linarith
  have hV : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := by
    apply IsOpen.mem_nhds (isOpen_Ioi.preimage Complex.continuous_re)
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hfg : (fun s : ℂ => s * ∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))) =ᶠ[𝓝 (2 : ℂ)]
      DirichletCharacter.LFunction χ := by
    apply Filter.eventuallyEq_of_mem hV
    intro s hs
    have hs1 : (1 : ℝ) < s.re := hs
    have hS : LSeriesSummable (fun n : ℕ => (χ n : ℂ)) s :=
      χ.LSeriesSummable_of_one_lt_re hs1
    have hrep := LSeries_eq_mul_integral (fun n : ℕ => (χ n : ℂ))
      (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) < s.re) hS
      (primitive_char_sum_Icc_isBigO hχ hq)
    show s * ∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)) =
      DirichletCharacter.LFunction χ s
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs1, hrep]
    rfl
  have h2mem : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hGan hLan
    hconv.isPreconnected h2mem hfg hs).symm

/-- The `L`-function of a primitive character of modulus at least two grows
at most linearly along vertical lines, with an explicit
Pólya–Vinogradov constant. -/
theorem norm_LFunction_le_of_re_pos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      3 * Real.sqrt q * Real.log (2 * q) * ‖s‖ / s.re := by
  set B : ℝ := 3 * Real.sqrt q * Real.log (2 * q) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (show 1 ≤ q by omega)
    have h2 : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  rw [LFunction_eq_mellin_integral hχ hq hs, norm_mul]
  have hJint : Integrable (fun t : ℝ => B * t ^ (-(s.re + 1)))
      (volume.restrict (Set.Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul B
  have hFint : Integrable (fun t : ℝ =>
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Set.Ioi 1)) := by
    apply hJint.mono'
      ((measurable_charPartialSumStep χ).aestronglyMeasurable.mul
        ((continuousOn_cpow_neg_succ_of_one_lt s).aestronglyMeasurable
          measurableSet_Ioi))
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have hre : (-(s + 1)).re = -(s.re + 1) := by
      simp [Complex.neg_re, Complex.add_re]
    have hstep := primitive_char_sum_Icc_norm_le hχ hq ⌊t⌋₊
    rw [← hB] at hstep
    simp only [Pi.mul_apply]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
    exact mul_le_mul hstep le_rfl (Real.rpow_nonneg ht0.le _) hB0
  have hJ : ‖∫ t in Set.Ioi (1 : ℝ),
        charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ ≤ B / s.re := by
    calc
      ‖∫ t in Set.Ioi (1 : ℝ),
            charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
          ∫ t in Set.Ioi (1 : ℝ),
            ‖charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), B * t ^ (-(s.re + 1)) := by
        apply setIntegral_mono_ae_restrict hFint.norm hJint
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro t ht
        have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
        have hre : (-(s + 1)).re = -(s.re + 1) := by
          simp [Complex.neg_re, Complex.add_re]
        have hstep := primitive_char_sum_Icc_norm_le hχ hq ⌊t⌋₊
        rw [← hB] at hstep
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
        exact mul_le_mul hstep le_rfl (Real.rpow_nonneg ht0.le _) hB0
      _ = B / s.re := by
        rw [MeasureTheory.integral_const_mul,
          integral_Ioi_rpow_of_lt
            (by linarith : -(s.re + 1) < -1) zero_lt_one]
        have h1 : -(s.re + 1) + 1 = -s.re := by ring
        rw [h1, Real.one_rpow]
        field_simp [hs.ne']
  calc
    ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ),
          charPartialSumStep χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖s‖ * (B / s.re) :=
      mul_le_mul_of_nonneg_left hJ (norm_nonneg _)
    _ = 3 * Real.sqrt q * Real.log (2 * q) * ‖s‖ / s.re := by
      rw [hB]
      ring

/-- Cauchy's estimate: a circle bound on `f` bounds its derivative at the
center.  First-power companion of `norm_deriv_pow_four_le_circleIntegral`. -/
theorem norm_deriv_le_div_of_circle_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} {r : ℝ} (hr : 0 < r) {M : ℝ}
    (hM : ∀ θ : ℝ, ‖f (circleMap c r θ)‖ ≤ M) :
    ‖deriv f c‖ ≤ M / r := by
  let g : ℝ → ℝ := fun θ => ‖f (circleMap c r θ)‖
  have hnorm : 2 * Real.pi * ‖deriv f c‖ ≤
      ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r := by
    calc
      2 * Real.pi * ‖deriv f c‖ =
          ‖(2 * Real.pi * Complex.I : ℂ) • deriv f c‖ := by
        simp [Complex.norm_real, Complex.norm_I,
          abs_of_pos Real.pi_pos]
      _ = ‖∮ z in C(c, r), (1 / (z - c) ^ 2) • f z‖ := by
        rw [(hf.differentiableOn).deriv_eq_smul_circleIntegral hr
          (c := c) (R := r)]
      _ ≤ ∫ θ in (0 : ℝ)..2 * Real.pi,
          ‖deriv (circleMap c r) θ •
            ((1 / (circleMap c r θ - c) ^ 2) •
              f (circleMap c r θ))‖ := by
        unfold circleIntegral
        exact intervalIntegral.norm_integral_le_integral_norm
          Real.two_pi_pos.le
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        dsimp only [g]
        simp [deriv_circleMap, circleMap_sub_center,
          norm_pow, norm_circleMap_zero, abs_of_pos hr]
        field_simp [hr.ne']
  have hbound : ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r ≤
      2 * Real.pi * (M / r) := by
    calc
      ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r ≤
          ∫ θ in (0 : ℝ)..2 * Real.pi, M / r := by
        apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
        · exact (((hf.continuous.norm.comp
            (continuous_circleMap c r)).intervalIntegrable
              0 (2 * Real.pi)).div_const r)
        · exact intervalIntegrable_const
        · intro θ hθ
          exact div_le_div_of_nonneg_right (hM θ) hr.le
      _ = 2 * Real.pi * (M / r) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  exact le_of_mul_le_mul_left (hnorm.trans hbound) h2pi

/-- Polynomial growth of `L'` on the strip `1/2 ≤ re s ≤ 2` for a primitive
character of modulus at least two.  The explicit constant is immaterial for
Lemma 6; only the linear growth in `‖s‖` matters. -/
theorem norm_deriv_LFunction_le_of_mem_strip {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    {s : ℂ} (h1 : (1 : ℝ) / 2 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤
      144 * Real.sqrt q * Real.log (2 * q) * ‖s‖ := by
  have hχne : χ ≠ 1 := by
    intro hχone
    have hcondOne : χ.conductor = 1 :=
      DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  set B : ℝ := 3 * Real.sqrt q * Real.log (2 * q) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have h1q : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (show 1 ≤ q by omega)
    have h2q : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  set r : ℝ := s.re / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hs0 : 0 < s.re := by linarith
  set M : ℝ := B * (‖s‖ + r) / (s.re / 2) with hM
  have hMbound : ∀ θ : ℝ,
      ‖DirichletCharacter.LFunction χ (circleMap s r θ)‖ ≤ M := by
    intro θ
    have hdist : ‖circleMap s r θ - s‖ = r := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hrpos]
    have hwre : s.re / 2 ≤ (circleMap s r θ).re := by
      have hre : |(circleMap s r θ - s).re| ≤ ‖circleMap s r θ - s‖ :=
        Complex.abs_re_le_norm _
      rw [hdist] at hre
      rcases abs_le.mp hre with ⟨h3, _⟩
      have h4 : (circleMap s r θ - s).re = (circleMap s r θ).re - s.re :=
        Complex.sub_re _ _
      rw [h4] at h3
      linarith
    have hwnorm : ‖circleMap s r θ‖ ≤ ‖s‖ + r := by
      calc
        ‖circleMap s r θ‖ = ‖s + (circleMap s r θ - s)‖ := by ring_nf
        _ ≤ ‖s‖ + ‖circleMap s r θ - s‖ := norm_add_le _ _
        _ = ‖s‖ + r := by rw [hdist]
    have hL := norm_LFunction_le_of_re_pos hχ hq
      (show 0 < (circleMap s r θ).re by linarith)
    rw [← hB] at hL
    have hdpos : (0 : ℝ) < s.re / 2 := by linarith
    calc
      ‖DirichletCharacter.LFunction χ (circleMap s r θ)‖ ≤
          B * ‖circleMap s r θ‖ / (circleMap s r θ).re := hL
      _ ≤ B * ‖circleMap s r θ‖ / (s.re / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hB0 (norm_nonneg _))
          hdpos hwre
      _ ≤ M := by
        apply div_le_div_of_nonneg_right _ hdpos.le
        exact mul_le_mul_of_nonneg_left hwnorm hB0
  have hmain := norm_deriv_le_div_of_circle_bound
    (DirichletCharacter.differentiable_LFunction hχne) hrpos hMbound
  have hsnorm : (1 : ℝ) / 2 ≤ ‖s‖ :=
    h1.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have hsq : (1 : ℝ) / 4 ≤ s.re ^ 2 := by
    calc
      (1 : ℝ) / 4 = (1 / 2) ^ 2 := by norm_num
      _ ≤ s.re ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  have hnum : ‖s‖ + r ≤ 3 * ‖s‖ := by
    rw [hrdef]
    linarith
  calc
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ M / r := hmain
    _ = 4 * B * (‖s‖ + r) / s.re ^ 2 := by
      rw [hM, hrdef]
      field_simp [hs0.ne']
      ring
    _ ≤ 4 * B * (3 * ‖s‖) / s.re ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnum (mul_nonneg (by norm_num) hB0))
        (sq_nonneg (s.re))
    _ ≤ 4 * B * (3 * ‖s‖) / (1 / 4) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) hB0)
          (mul_nonneg (by norm_num) (norm_nonneg _)))
        (by norm_num) hsq
    _ = 144 * Real.sqrt q * Real.log (2 * q) * ‖s‖ := by
      rw [hB]
      ring

end Chen
