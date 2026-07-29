import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter MeasureTheory Real
open scoped Interval

namespace Chen

private theorem log_le_sub_inv_half {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let z := (x - 1) / (x + 1)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxplus : x + 1 ≠ 0 := by positivity
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hz1 : z < 1 := by
    dsimp only [z]
    rw [div_lt_one (by positivity : 0 < x + 1)]
    linarith
  have h :=
    Real.log_div_le_sum_range_add hz0 hz1 0
  have hratio : (1 + z) / (1 - z) = x := by
    dsimp only [z]
    field_simp
    ring
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hrat :
      2 * (z / (1 - z ^ 2)) = (x - x⁻¹) / 2 := by
    dsimp only [z]
    rw [inv_eq_one_div]
    have hdenz :
        (x + 1) ^ 2 - (x - 1) ^ 2 ≠ 0 := by
      nlinarith
    field_simp [hxpos.ne', hxplus, hdenz]
    ring
  linarith

/-! ## Equation (24) -/

/-- The one-dimensional integral occurring in equation (24). -/
noncomputable def equation24Integral : ℝ :=
  ∫ α : ℝ in (1 / 10)..(1 / 3),
    Real.log (2 - 3 * α) / (α * (1 - α))

private noncomputable def equation24RationalMajorant (α : ℝ) : ℝ :=
  (227 / 324) / α - (4 / 81) / (1 - α) +
    (104 / 81) / (1 - α) ^ 2 -
      (112 / 81) / (1 - α) ^ 3 +
        (32 / 81) / (1 - α) ^ 4 -
          (9 / 4) / (2 - 3 * α)

private noncomputable def equation24Antiderivative (α : ℝ) : ℝ :=
  (227 / 324) * Real.log α +
    (4 / 81) * Real.log (1 - α) +
      (104 / 81) / (1 - α) -
        (56 / 81) / (1 - α) ^ 2 +
          (32 / 243) / (1 - α) ^ 3 +
            (3 / 4) * Real.log (2 - 3 * α)

private theorem equation24_log_le_majorant
    {α : ℝ} (hαlo : 1 / 10 ≤ α) (hαhi : α ≤ 1 / 3) :
    Real.log (2 - 3 * α) / (α * (1 - α)) ≤
      equation24RationalMajorant α := by
  let z := (1 - 3 * α) / (3 * (1 - α))
  have hα0 : 0 < α := by linarith
  have h1α : 0 < 1 - α := by linarith
  have h23α : 0 < 2 - 3 * α := by linarith
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    have hnum : 0 ≤ 1 - 3 * α := by linarith
    have hdenom : 0 ≤ 3 * (1 - α) := by positivity
    exact div_nonneg hnum hdenom
  have hz1 : z < 1 := by
    dsimp only [z]
    rw [div_lt_one (by positivity : 0 < 3 * (1 - α))]
    linarith
  have hlog := Real.log_div_le_sum_range_add hz0 hz1 2
  have hratio : (1 + z) / (1 - z) = 2 - 3 * α := by
    dsimp only [z]
    field_simp [h1α.ne', h23α.ne']
    ring
  rw [hratio] at hlog
  norm_num [Finset.sum_range_succ] at hlog
  have hden : 0 < α * (1 - α) := mul_pos hα0 h1α
  apply (div_le_iff₀ hden).2
  calc
    Real.log (2 - 3 * α) ≤
        2 * (z + z ^ 3 / 3 + z ^ 5 / (1 - z ^ 2)) := by
      linarith
    _ = equation24RationalMajorant α * (α * (1 - α)) := by
      unfold equation24RationalMajorant
      have hzsq :
          1 - z ^ 2 =
            4 * (2 - 3 * α) / (9 * (1 - α) ^ 2) := by
        dsimp only [z]
        field_simp [h1α.ne']
        ring
      rw [hzsq]
      dsimp only [z]
      field_simp [hα0.ne', h1α.ne', h23α.ne']
      ring

private theorem equation24RationalMajorant_hasDerivAt
    {α : ℝ} (hαlo : 1 / 10 ≤ α) (hαhi : α ≤ 1 / 3) :
    HasDerivAt equation24Antiderivative
      (equation24RationalMajorant α) α := by
  have hα0 : α ≠ 0 := by linarith
  have h1α : 1 - α ≠ 0 := by linarith
  have h23α : 2 - 3 * α ≠ 0 := by linarith
  unfold equation24Antiderivative equation24RationalMajorant
  have hone : HasDerivAt (fun t : ℝ => 1 - t) (-1) α :=
    (hasDerivAt_id α).const_sub 1
  have htwo : HasDerivAt (fun t : ℝ => 2 - 3 * t) (-3) α := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id α).const_mul (3 : ℝ)).const_sub (2 : ℝ)
  have hA := (Real.hasDerivAt_log hα0).const_mul (227 / 324)
  have hB := (hone.log h1α).const_mul (4 / 81)
  have hC := (hasDerivAt_const α (104 / 81)).div hone h1α
  have hD :=
    (hasDerivAt_const α (56 / 81)).div (hone.pow 2)
      (pow_ne_zero 2 h1α)
  have hE :=
    (hasDerivAt_const α (32 / 243)).div (hone.pow 3)
      (pow_ne_zero 3 h1α)
  have hF := (htwo.log h23α).const_mul (3 / 4)
  have hraw := ((((hA.add hB).add hC).sub hD).add hE).add hF
  change HasDerivAt
    (fun t : ℝ =>
      (227 / 324) * Real.log t +
        (4 / 81) * Real.log (1 - t) +
          (104 / 81) / (1 - t) -
            (56 / 81) / (1 - t) ^ 2 +
              (32 / 243) / (1 - t) ^ 3 +
                (3 / 4) * Real.log (2 - 3 * t))
    _ α at hraw
  apply hraw.congr_deriv
  simp only [Pi.pow_apply, Nat.cast_ofNat, zero_mul]
  field_simp [hα0, h1α, h23α]
  ring

private theorem equation24RationalMajorant_integral :
    (∫ α : ℝ in (1 / 10)..(1 / 3),
      equation24RationalMajorant α) =
        (227 / 324) * Real.log (10 / 3) -
          (4 / 81) * Real.log (27 / 20) -
            (3 / 4) * Real.log (17 / 10) +
              10822 / 177147 := by
  have hFTC :
      (∫ α : ℝ in (1 / 10)..(1 / 3),
        equation24RationalMajorant α) =
          equation24Antiderivative (1 / 3) -
            equation24Antiderivative (1 / 10) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro α hα
      rw [Set.uIcc_of_le (by norm_num :
        (1 / 10 : ℝ) ≤ 1 / 3)] at hα
      exact equation24RationalMajorant_hasDerivAt hα.1 hα.2
    · apply ContinuousOn.intervalIntegrable
      apply continuousOn_of_forall_continuousAt
      intro α hα
      rw [Set.uIcc_of_le (by norm_num :
        (1 / 10 : ℝ) ≤ 1 / 3)] at hα
      have hα0 : α ≠ 0 := by linarith [hα.1]
      have h1α : 1 - α ≠ 0 := by linarith [hα.2]
      have h23α : 2 - 3 * α ≠ 0 := by linarith [hα.2]
      have h1α2 : (1 - α) ^ 2 ≠ 0 := pow_ne_zero 2 h1α
      have h1α3 : (1 - α) ^ 3 ≠ 0 := pow_ne_zero 3 h1α
      have h1α4 : (1 - α) ^ 4 ≠ 0 := pow_ne_zero 4 h1α
      unfold equation24RationalMajorant
      fun_prop
  rw [hFTC]
  unfold equation24Antiderivative
  norm_num only [one_div, sub_self, Real.log_one, mul_zero]
  have hlog103 :
      Real.log (10 / 3 : ℝ) =
        Real.log (1 / 3 : ℝ) - Real.log (1 / 10 : ℝ) := by
    rw [← Real.log_div (by norm_num : (1 / 3 : ℝ) ≠ 0)
      (by norm_num : (1 / 10 : ℝ) ≠ 0)]
    norm_num
  have hlog2720 :
      Real.log (27 / 20 : ℝ) =
        Real.log (9 / 10 : ℝ) - Real.log (2 / 3 : ℝ) := by
    rw [← Real.log_div (by norm_num : (9 / 10 : ℝ) ≠ 0)
      (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    norm_num
  rw [hlog103, hlog2720]
  norm_num
  ring

private theorem equation24_logarithmic_bound :
    (227 / 324 : ℝ) * Real.log (10 / 3) -
          (4 / 81) * Real.log (27 / 20) -
            (3 / 4) * Real.log (17 / 10) +
              10822 / 177147 ≤ 0.49254 := by
  have h103 := Real.log_div_le_sum_range_add
    (x := (7 / 13 : ℝ)) (by norm_num) (by norm_num) 6
  have h2720 := Real.sum_range_le_log_div
    (x := (7 / 47 : ℝ)) (by norm_num) (by norm_num) 3
  have h1710 := Real.sum_range_le_log_div
    (x := (7 / 27 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h103 h2720 h1710 ⊢
  linarith

/-- Equation **(24)** exactly as displayed in the paper.  Instead of copying
the scan's seven-subinterval table of rounded logarithms, we bound the same
integrand by a rational function using the hyperbolic-arctangent expansion of
`log`, and retain exact rational remainders throughout. -/
theorem equation24_integral_bound :
    equation24Integral ≤ 0.49254 := by
  calc
    equation24Integral ≤
        ∫ α : ℝ in (1 / 10)..(1 / 3),
          equation24RationalMajorant α := by
      unfold equation24Integral
      apply intervalIntegral.integral_mono_on
        (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)
      · apply ContinuousOn.intervalIntegrable
        apply continuousOn_of_forall_continuousAt
        intro α hα
        rw [Set.uIcc_of_le (by norm_num :
          (1 / 10 : ℝ) ≤ 1 / 3)] at hα
        have hα0 : α ≠ 0 := by linarith [hα.1]
        have h1α : 1 - α ≠ 0 := by linarith [hα.2]
        have h23α : 2 - 3 * α ≠ 0 := by linarith [hα.2]
        have hden : α * (1 - α) ≠ 0 := mul_ne_zero hα0 h1α
        fun_prop
      · apply ContinuousOn.intervalIntegrable
        apply continuousOn_of_forall_continuousAt
        intro α hα
        rw [Set.uIcc_of_le (by norm_num :
          (1 / 10 : ℝ) ≤ 1 / 3)] at hα
        have hα0 : α ≠ 0 := by linarith [hα.1]
        have h1α : 1 - α ≠ 0 := by linarith [hα.2]
        have h23α : 2 - 3 * α ≠ 0 := by linarith [hα.2]
        have h1α2 : (1 - α) ^ 2 ≠ 0 := pow_ne_zero 2 h1α
        have h1α3 : (1 - α) ^ 3 ≠ 0 := pow_ne_zero 3 h1α
        have h1α4 : (1 - α) ^ 4 ≠ 0 := pow_ne_zero 4 h1α
        unfold equation24RationalMajorant
        fun_prop
      · intro α hα
        exact equation24_log_le_majorant hα.1 hα.2
    _ = (227 / 324 : ℝ) * Real.log (10 / 3) -
          (4 / 81) * Real.log (27 / 20) -
            (3 / 4) * Real.log (17 / 10) +
              10822 / 177147 :=
      equation24RationalMajorant_integral
    _ ≤ 0.49254 := equation24_logarithmic_bound

/-! ## Equation (27) -/

private noncomputable def equation27Inner (u : ℝ) : ℝ :=
  ∫ t : ℝ in 2..u - 1, Real.log (t - 1) / t

private noncomputable def equation27InnerAntiderivative (t : ℝ) : ℝ :=
  (t - Real.log (t - 1)) / 2

private theorem equation27InnerAntiderivative_hasDerivAt
    {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt equation27InnerAntiderivative
      ((t - 2) / (2 * (t - 1))) t := by
  have ht1 : t - 1 ≠ 0 := by linarith
  unfold equation27InnerAntiderivative
  have hsub : HasDerivAt (fun v : ℝ => v - 1) 1 t :=
    (hasDerivAt_id t).sub_const 1
  have hraw :=
    ((hasDerivAt_id t).sub (hsub.log ht1)).div_const 2
  change HasDerivAt
    (fun v : ℝ => (v - Real.log (v - 1)) / 2) _ t at hraw
  apply hraw.congr_deriv
  field_simp [ht1]
  ring

private theorem equation27Inner_rational_integral
    {u : ℝ} (hu : 3 ≤ u) :
    (∫ t : ℝ in 2..u - 1, (t - 2) / (2 * (t - 1))) =
      ((u - 3) - Real.log (u - 2)) / 2 := by
  have hFTC :
      (∫ t : ℝ in 2..u - 1, (t - 2) / (2 * (t - 1))) =
        equation27InnerAntiderivative (u - 1) -
          equation27InnerAntiderivative 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ u - 1)] at ht
      exact equation27InnerAntiderivative_hasDerivAt ht.1
    · apply ContinuousOn.intervalIntegrable
      apply continuousOn_of_forall_continuousAt
      intro t ht
      rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ u - 1)] at ht
      have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
      have hden : (2 : ℝ) * (t - 1) ≠ 0 := by positivity
      fun_prop
  rw [hFTC]
  unfold equation27InnerAntiderivative
  norm_num [Real.log_one]
  ring_nf

private theorem equation27Inner_le_preliminary
    {u : ℝ} (hu3 : 3 ≤ u) (_hu4 : u ≤ 4) :
    equation27Inner u ≤
      ((u - 3) - Real.log (u - 2)) / 2 := by
  unfold equation27Inner
  calc
    (∫ t : ℝ in 2..u - 1, Real.log (t - 1) / t) ≤
        ∫ t : ℝ in 2..u - 1, (t - 2) / (2 * (t - 1)) := by
      have hab : (2 : ℝ) ≤ u - 1 := by linarith
      apply intervalIntegral.integral_mono_on hab
      · apply ContinuousOn.intervalIntegrable
        apply continuousOn_of_forall_continuousAt
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        have ht2 : 2 ≤ t := ht.1
        have ht0 : t ≠ 0 := by linarith
        have ht1 : t - 1 ≠ 0 := by linarith
        fun_prop
      · apply ContinuousOn.intervalIntegrable
        apply continuousOn_of_forall_continuousAt
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
        have hden : (2 : ℝ) * (t - 1) ≠ 0 := by positivity
        fun_prop
      · intro t ht
        have ht2 : 2 ≤ t := ht.1
        have htpos : 0 < t := by linarith
        have ht1pos : 0 < t - 1 := by linarith
        have hlog := log_le_sub_inv_half (x := t - 1) (by linarith)
        apply (div_le_iff₀ htpos).2
        calc
          Real.log (t - 1) ≤
              ((t - 1) - (t - 1)⁻¹) / 2 := hlog
          _ = t * ((t - 2) / (2 * (t - 1))) := by
            field_simp [ht1pos.ne']
            ring
          _ = ((t - 2) / (2 * (t - 1))) * t := by
            rw [mul_comm]
    _ = ((u - 3) - Real.log (u - 2)) / 2 :=
      equation27Inner_rational_integral hu3

private theorem equation27_log_lower
    {u : ℝ} (hu3 : 3 ≤ u) (_hu4 : u ≤ 4) :
    2 * ((u - 3) / (u - 1) +
      ((u - 3) / (u - 1)) ^ 3 / 3) ≤ Real.log (u - 2) := by
  let z := (u - 3) / (u - 1)
  have hu1 : 0 < u - 1 := by linarith
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    positivity
  have hz1 : z < 1 := by
    dsimp only [z]
    rw [div_lt_one hu1]
    linarith
  have h :=
    Real.sum_range_le_log_div hz0 hz1 2
  have hratio : (1 + z) / (1 - z) = u - 2 := by
    dsimp only [z]
    field_simp
    ring
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem equation27Inner_le_majorant
    {u : ℝ} (hu3 : 3 ≤ u) (hu4 : u ≤ 4) :
    equation27Inner u ≤
      (u - 3) / 2 - (u - 3) / (u - 1) -
        ((u - 3) / (u - 1)) ^ 3 / 3 := by
  have hpre := equation27Inner_le_preliminary hu3 hu4
  have hlog := equation27_log_lower hu3 hu4
  linarith

private theorem equation27Inner_continuousAt
    {u : ℝ} (hu3 : 3 ≤ u) (_hu4 : u ≤ 4) :
    ContinuousAt equation27Inner u := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hfi : IntervalIntegrable f volume 2 (u - 1) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ u - 1)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
    dsimp only [f]
    fun_prop
  have hfcont :
      ∀ t ∈ Set.Ioi (1 : ℝ), ContinuousAt f t := by
    intro t ht
    change 1 < t at ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t - 1 ≠ 0 := by linarith
    dsimp only [f]
    fun_prop
  have hmeas :
      StronglyMeasurableAtFilter f (nhds (u - 1)) volume :=
    ContinuousAt.stronglyMeasurableAtFilter
      isOpen_Ioi hfcont (u - 1) (by
        change 1 < u - 1
        linarith)
  have hprimitive :
      ContinuousAt (fun v => ∫ t : ℝ in 2..v, f t) (u - 1) :=
    (intervalIntegral.integral_hasDerivAt_right hfi hmeas
      (hfcont (u - 1) (by
        change 1 < u - 1
        linarith))).continuousAt
  have hshift :
      ContinuousAt (fun v : ℝ => v - 1) u :=
    ((hasDerivAt_id u).sub_const 1).continuousAt
  have hcomp :=
    ContinuousAt.comp' (f := fun v : ℝ => v - 1) (x := u)
      hprimitive hshift
  change ContinuousAt
    (fun v : ℝ => ∫ t : ℝ in 2..v - 1,
      Real.log (t - 1) / t) u
  exact hcomp

private noncomputable def equation27ReducedIntegral : ℝ :=
  ∫ u : ℝ in 3..4,
    ((5 / 2 - u) / (u * (5 - u))) * equation27Inner u

/-- The left-hand side of equation (27), in the notation of the scan. -/
noncomputable def equation27Integral : ℝ :=
  (∫ u : ℝ in 3..4, (1 / u) * equation27Inner u) -
    (1 / 4) *
      ∫ α : ℝ in (1 / 10)..(1 / 5),
        (1 / (α * (1 / 2 - α))) *
          equation27Inner (5 - 10 * α)

private noncomputable def equation27SubstitutionKernel (u : ℝ) : ℝ :=
  (100 / (u * (5 - u))) * equation27Inner u

private theorem equation27_substitution :
    (1 / 4 : ℝ) *
        (∫ α : ℝ in (1 / 10)..(1 / 5),
          (1 / (α * (1 / 2 - α))) *
            equation27Inner (5 - 10 * α)) =
      ∫ u : ℝ in 3..4,
        ((5 / 2) / (u * (5 - u))) * equation27Inner u := by
  have hcongr :
      (∫ α : ℝ in (1 / 10)..(1 / 5),
        (1 / (α * (1 / 2 - α))) *
          equation27Inner (5 - 10 * α)) =
        ∫ α : ℝ in (1 / 10)..(1 / 5),
          equation27SubstitutionKernel (5 - 10 * α) := by
    apply intervalIntegral.integral_congr
    intro α hα
    rw [Set.uIcc_of_le (by norm_num :
      (1 / 10 : ℝ) ≤ 1 / 5)] at hα
    rcases hα with ⟨hαlo, hαhi⟩
    have hα0 : α ≠ 0 := by linarith
    have hhalf : 1 / 2 - α ≠ 0 := by linarith
    have hfive : 5 - 10 * α ≠ 0 := by linarith
    unfold equation27SubstitutionKernel
    change
      (1 / (α * (1 / 2 - α))) *
          equation27Inner (5 - 10 * α) =
        (100 / ((5 - 10 * α) * (5 - (5 - 10 * α)))) *
          equation27Inner (5 - 10 * α)
    rw [show 5 - (5 - 10 * α) = 10 * α by ring]
    have hcoeff :
        (1 / (α * (1 / 2 - α)) : ℝ) =
          100 / ((5 - 10 * α) * (10 * α)) := by
      rw [show (1 / 2 - α : ℝ) =
        (5 - 10 * α) / 10 by ring]
      field_simp [hα0, hhalf, hfive]
      ring
    rw [hcoeff]
  have hchange :
      (∫ α : ℝ in (1 / 10)..(1 / 5),
        equation27SubstitutionKernel (5 - 10 * α)) =
        (10 : ℝ)⁻¹ *
          ∫ u : ℝ in 3..4, equation27SubstitutionKernel u := by
    simpa only [smul_eq_mul,
      show (5 : ℝ) - 10 * (1 / 5) = 3 by norm_num,
      show (5 : ℝ) - 10 * (1 / 10) = 4 by norm_num] using
      (intervalIntegral.integral_comp_sub_mul
        (f := equation27SubstitutionKernel)
        (a := (1 / 10 : ℝ)) (b := (1 / 5 : ℝ))
        (c := (10 : ℝ)) (d := (5 : ℝ))
        (by norm_num : (10 : ℝ) ≠ 0))
  rw [hcongr, hchange]
  calc
    (1 / 4 : ℝ) *
        ((10 : ℝ)⁻¹ *
          ∫ u : ℝ in 3..4, equation27SubstitutionKernel u) =
      (1 / 40 : ℝ) *
        ∫ u : ℝ in 3..4, equation27SubstitutionKernel u := by ring
    _ = ∫ u : ℝ in 3..4,
        (1 / 40 : ℝ) * equation27SubstitutionKernel u := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u : ℝ in 3..4,
        ((5 / 2) / (u * (5 - u))) *
          equation27Inner u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
      rcases hu with ⟨hu3, hu4⟩
      have hu0 : u ≠ 0 := by linarith
      have h5u : 5 - u ≠ 0 := by linarith
      unfold equation27SubstitutionKernel
      field_simp [hu0, h5u]
      ring

private theorem equation27Integral_eq_reduced :
    equation27Integral = equation27ReducedIntegral := by
  rw [equation27Integral, equation27_substitution]
  unfold equation27ReducedIntegral
  have hfirst :
      IntervalIntegrable
        (fun u : ℝ => (1 / u) * equation27Inner u)
        volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
    rcases hu with ⟨hu3, hu4⟩
    have hu0 : u ≠ 0 := by linarith
    exact
      (by fun_prop : ContinuousAt (fun v : ℝ => 1 / v) u).mul
        (equation27Inner_continuousAt hu3 hu4)
  have hsecond :
      IntervalIntegrable
        (fun u : ℝ =>
          ((5 / 2) / (u * (5 - u))) * equation27Inner u)
        volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
    rcases hu with ⟨hu3, hu4⟩
    have hu0 : u ≠ 0 := by linarith
    have h5u : 5 - u ≠ 0 := by linarith
    have hden : u * (5 - u) ≠ 0 :=
      mul_ne_zero hu0 h5u
    exact
      (by fun_prop :
        ContinuousAt
          (fun v : ℝ => (5 / 2) / (v * (5 - v))) u).mul
        (equation27Inner_continuousAt hu3 hu4)
  rw [← intervalIntegral.integral_sub hfirst hsecond]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
  rcases hu with ⟨hu3, hu4⟩
  have hu0 : u ≠ 0 := by linarith
  have h5u : 5 - u ≠ 0 := by linarith
  field_simp [hu0, h5u]
  ring

private noncomputable def equation27RationalMajorant (u : ℝ) : ℝ :=
  ((5 / 2 - u) / (u * (5 - u))) *
    ((u - 3) / 2 - (u - 3) / (u - 1) -
      ((u - 3) / (u - 1)) ^ 3 / 3)

private noncomputable def equation27Antiderivative (u : ℝ) : ℝ :=
  u / 2 - (27 / 4) * Real.log u +
    (11 / 48) * Real.log (5 - u) +
      (79 / 16) * Real.log (u - 1) +
        (35 / 12) / (u - 1) -
          1 / (2 * (u - 1) ^ 2)

private theorem equation27RationalMajorant_hasDerivAt
    {u : ℝ} (hu3 : 3 ≤ u) (hu4 : u ≤ 4) :
    HasDerivAt equation27Antiderivative
      (equation27RationalMajorant u) u := by
  have hu0 : u ≠ 0 := by linarith
  have hu1 : u - 1 ≠ 0 := by linarith
  have h5u : 5 - u ≠ 0 := by linarith
  unfold equation27Antiderivative equation27RationalMajorant
  have hsub : HasDerivAt (fun v : ℝ => v - 1) 1 u :=
    (hasDerivAt_id u).sub_const 1
  have hfive : HasDerivAt (fun v : ℝ => 5 - v) (-1) u :=
    (hasDerivAt_id u).const_sub 5
  have hA := (hasDerivAt_id u).div_const 2
  have hB := (Real.hasDerivAt_log hu0).const_mul (27 / 4)
  have hC := (hfive.log h5u).const_mul (11 / 48)
  have hD := (hsub.log hu1).const_mul (79 / 16)
  have hE := (hasDerivAt_const u (35 / 12)).div hsub hu1
  have hden :
      (2 : ℝ) * (u - 1) ^ 2 ≠ 0 := by positivity
  have hF :=
    (hasDerivAt_const u 1).div
      ((hasDerivAt_const u 2).mul (hsub.pow 2)) hden
  have hraw := ((((hA.sub hB).add hC).add hD).add hE).sub hF
  change HasDerivAt
    (fun v : ℝ =>
      v / 2 - (27 / 4) * Real.log v +
        (11 / 48) * Real.log (5 - v) +
          (79 / 16) * Real.log (v - 1) +
            (35 / 12) / (v - 1) -
              1 / (2 * (v - 1) ^ 2))
    _ u at hraw
  apply hraw.congr_deriv
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat,
    zero_mul, one_mul, mul_one, Nat.reduceSub]
  field_simp [hu0, hu1, h5u]
  ring

private theorem equation27RationalMajorant_integral :
    (∫ u : ℝ in 3..4, equation27RationalMajorant u) =
      1 / 12 - (27 / 4) * Real.log (4 / 3) -
        (11 / 48) * Real.log 2 +
          (79 / 16) * Real.log (3 / 2) := by
  have hFTC :
      (∫ u : ℝ in 3..4, equation27RationalMajorant u) =
        equation27Antiderivative 4 -
          equation27Antiderivative 3 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
      exact equation27RationalMajorant_hasDerivAt hu.1 hu.2
    · exact
        (ContinuousOn.intervalIntegrable
          (continuousOn_of_forall_continuousAt fun u hu =>
            by
              rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
              rcases hu with ⟨hu3, hu4⟩
              have hu0 : u ≠ 0 := by linarith
              have hu1 : u - 1 ≠ 0 := by linarith
              have h5u : 5 - u ≠ 0 := by linarith
              have hden : u * (5 - u) ≠ 0 :=
                mul_ne_zero hu0 h5u
              unfold equation27RationalMajorant
              fun_prop))
  rw [hFTC]
  unfold equation27Antiderivative
  norm_num only [sub_self, sub_eq_add_neg, one_pow, mul_one,
    div_one, one_div]
  have hlog43 : Real.log (4 / 3 : ℝ) =
      Real.log 4 - Real.log 3 := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0)]
  have hlog32 : Real.log (3 / 2 : ℝ) =
      Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hlog43, hlog32]
  norm_num
  ring

private theorem log_four_thirds_upper :
    Real.log (4 / 3 : ℝ) ≤
      2 * ((1 / 7 : ℝ) + (1 / 7 : ℝ) ^ 3 / 3 +
        (1 / 7 : ℝ) ^ 5 / (1 - (1 / 7 : ℝ) ^ 2)) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 7 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem log_two_upper :
    Real.log 2 ≤
      2 * ((1 / 3 : ℝ) + (1 / 3 : ℝ) ^ 3 / 3 +
        (1 / 3 : ℝ) ^ 5 / 5 +
        (1 / 3 : ℝ) ^ 7 / (1 - (1 / 3 : ℝ) ^ 2)) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem log_three_halves_lower :
    2 * ((1 / 5 : ℝ) + (1 / 5 : ℝ) ^ 3 / 3 +
      (1 / 5 : ℝ) ^ 5 / 5) ≤ Real.log (3 / 2 : ℝ) := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- A rigorous replacement for the rounded final decimal line in the paper's
calculation (27).  The displayed decimal calculation in the scan loses about
`1.3e-7` to rounding; using one more term of the logarithm series gives ample
room for the stated constant. -/
theorem equation27_logarithmic_bound :
    (-0.0164725 : ℝ) ≤
      1 / 12 - (27 / 4) * Real.log (4 / 3) -
        (11 / 48) * Real.log 2 +
          (79 / 16) * Real.log (3 / 2) := by
  have h43 := log_four_thirds_upper
  have h2 := log_two_upper
  have h32 := log_three_halves_lower
  norm_num at h43 h2 h32 ⊢
  linarith

/-- The one-dimensional integral inequality obtained after the substitution
`u = 5 - 10α` in equation (27).  Unlike the paper's final rounded decimal
line, this proof keeps rigorous logarithm bounds throughout. -/
theorem equation27_reduced_integral_bound :
    (-0.0164725 : ℝ) ≤ equation27ReducedIntegral := by
  calc
    (-0.0164725 : ℝ) ≤
        1 / 12 - (27 / 4) * Real.log (4 / 3) -
          (11 / 48) * Real.log 2 +
            (79 / 16) * Real.log (3 / 2) :=
      equation27_logarithmic_bound
    _ = ∫ u : ℝ in 3..4, equation27RationalMajorant u :=
      equation27RationalMajorant_integral.symm
    _ ≤ equation27ReducedIntegral := by
      unfold equation27ReducedIntegral
      apply intervalIntegral.integral_mono_on
        (by norm_num : (3 : ℝ) ≤ 4)
      · apply ContinuousOn.intervalIntegrable
        apply continuousOn_of_forall_continuousAt
        intro u hu
        rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
        rcases hu with ⟨hu3, hu4⟩
        have hu0 : u ≠ 0 := by linarith
        have hu1 : u - 1 ≠ 0 := by linarith
        have h5u : 5 - u ≠ 0 := by linarith
        have hden : u * (5 - u) ≠ 0 :=
          mul_ne_zero hu0 h5u
        unfold equation27RationalMajorant
        fun_prop
      · apply ContinuousOn.intervalIntegrable
        apply continuousOn_of_forall_continuousAt
        intro u hu
        rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
        rcases hu with ⟨hu3, hu4⟩
        have hu0 : u ≠ 0 := by linarith
        have h5u : 5 - u ≠ 0 := by linarith
        have hden : u * (5 - u) ≠ 0 :=
          mul_ne_zero hu0 h5u
        exact
          (by fun_prop :
            ContinuousAt
              (fun v : ℝ => (5 / 2 - v) / (v * (5 - v))) u).mul
            (equation27Inner_continuousAt hu3 hu4)
      · intro u hu
        rcases hu with ⟨hu3, hu4⟩
        have hu0 : 0 < u := by linarith
        have h5u : 0 < 5 - u := by linarith
        have hc :
            (5 / 2 - u) / (u * (5 - u)) ≤ 0 := by
          exact div_nonpos_of_nonpos_of_nonneg
            (by linarith) (mul_nonneg hu0.le h5u.le)
        have hinner :=
          equation27Inner_le_majorant hu3 hu4
        unfold equation27RationalMajorant
        exact mul_le_mul_of_nonpos_left hinner hc

/-- Equation **(27)** exactly as displayed in the paper. -/
theorem equation27_integral_bound :
    (-0.0164725 : ℝ) ≤ equation27Integral := by
  rw [equation27Integral_eq_reduced]
  exact equation27_reduced_integral_bound

end Chen
