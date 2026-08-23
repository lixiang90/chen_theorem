/-
Mellin-transform preparation for the smoothing function in Lemma 6.

Chen's contour kernel is the Mellin transform of `y ↦ Φ(1/y)`.  This
module puts the incomplete-gamma definition of `chenPhi` into the exact
shape required by Mathlib's Mellin inversion theorem.  The transform
calculation itself is split into small analytic steps below.
-/
import ChenTheorem.SieveLemmas
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Filter Real MeasureTheory Set
open scoped Interval FourierTransform

namespace Chen

/-- The scale `a = (log x)^1.1` in Chen's smoothing kernel. -/
noncomputable def lemma6SmoothingScale (x : ℝ) : ℝ :=
  (Real.log x) ^ (1.1 : ℝ)

/-- The integer order `[лog x]` in Chen's smoothing kernel. -/
noncomputable def lemma6SmoothingOrder (x : ℝ) : ℕ :=
  ⌊Real.log x⌋₊

/-- The reciprocal-variable form to which Mellin inversion is applied. -/
noncomputable def lemma6PhiReciprocal (x u : ℝ) : ℂ :=
  (chenPhi x u⁻¹ : ℝ)

/-- Chen's rational Mellin kernel
`s⁻¹ (1 + s/a)^{-([log x]+1)}`.  The negative integer power is
written as the inverse of an ordinary natural power. -/
noncomputable def lemma6SmoothingMellinKernel (x : ℝ) (s : ℂ) : ℂ :=
  s⁻¹ *
    ((1 + s / (lemma6SmoothingScale x : ℂ)) ^
      (lemma6SmoothingOrder x + 1))⁻¹

/-- The smoothing kernel is holomorphic in the open right half-plane.
Its only possible poles are at `0` and at the negative real point `-a`, so
neither occurs in the strip used to move equation (17) from `α` to `β`. -/
theorem differentiableOn_lemma6SmoothingMellinKernel
    {x : ℝ} (hx : 1 < x) :
    DifferentiableOn ℂ (lemma6SmoothingMellinKernel x)
      {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  unfold lemma6SmoothingMellinKernel
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have ha : 0 < lemma6SmoothingScale x := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hbase : 1 + s / (lemma6SmoothingScale x : ℂ) ≠ 0 := by
    intro h
    have ha0 : (lemma6SmoothingScale x : ℂ) ≠ 0 := by
      exact_mod_cast ha.ne'
    have hdiv : s / (lemma6SmoothingScale x : ℂ) = -1 := by
      linear_combination h
    have hsEq : s = -(lemma6SmoothingScale x : ℂ) := by
      apply (div_eq_iff ha0).mp at hdiv
      simpa using hdiv
    have hre := congrArg Complex.re hsEq
    change s.re = -lemma6SmoothingScale x at hre
    nlinarith
  have hleft : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) s :=
    differentiableAt_inv hs0
  have hinner : DifferentiableAt ℂ
      (fun z : ℂ => 1 + z / (lemma6SmoothingScale x : ℂ)) s := by
    fun_prop
  have hright : DifferentiableAt ℂ
      (fun z : ℂ => ((1 + z / (lemma6SmoothingScale x : ℂ)) ^
        (lemma6SmoothingOrder x + 1))⁻¹) s :=
    (hinner.pow _).inv (pow_ne_zero _ hbase)
  exact (hleft.mul hright).differentiableWithinAt

private noncomputable def lemma6GammaIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t) * t ^ n

private theorem continuous_lemma6GammaIntegrand (n : ℕ) :
    Continuous (lemma6GammaIntegrand n) := by
  unfold lemma6GammaIntegrand
  fun_prop

private theorem setIntegral_Ioc_zero_eq_intervalIntegral_max
    (n : ℕ) (b : ℝ) :
    (∫ t in Ioc (0 : ℝ) b, lemma6GammaIntegrand n t) =
      ∫ t in (0 : ℝ)..max 0 b, lemma6GammaIntegrand n t := by
  by_cases hb : 0 ≤ b
  · rw [max_eq_right hb, intervalIntegral.integral_of_le hb]
  · have hb' : b < 0 := lt_of_not_ge hb
    have hempty : Ioc (0 : ℝ) b = ∅ := by
      exact Set.Ioc_eq_empty (not_lt.mpr hb'.le)
    rw [hempty, setIntegral_empty, max_eq_left hb'.le, intervalIntegral.integral_same]

/-- The incomplete-gamma definition is an ordinary interval integral with
a continuously varying upper endpoint.  The `max` also covers `y ≤ 1`,
where the original `Ioc` is empty. -/
theorem chenPhi_eq_intervalIntegral_max (x y : ℝ) :
    chenPhi x y =
      ((lemma6SmoothingOrder x).factorial : ℝ)⁻¹ *
        ∫ t in (0 : ℝ)..max 0
          (lemma6SmoothingScale x * Real.log y),
          lemma6GammaIntegrand (lemma6SmoothingOrder x) t := by
  unfold chenPhi lemma6SmoothingOrder lemma6SmoothingScale
  change ((⌊Real.log x⌋₊.factorial : ℝ))⁻¹ *
      (∫ t in Ioc (0 : ℝ) ((Real.log x) ^ (1.1 : ℝ) * Real.log y),
        lemma6GammaIntegrand ⌊Real.log x⌋₊ t) = _
  rw [setIntegral_Ioc_zero_eq_intervalIntegral_max]

/-- On logarithmic coordinates to the right of the origin, the `max` in
the incomplete-gamma endpoint disappears. -/
theorem chenPhi_exp_eq_intervalIntegral
    {x r : ℝ} (hx : 1 < x) (hr : 0 < r) :
    chenPhi x (Real.exp r) =
      (((lemma6SmoothingOrder x).factorial : ℝ))⁻¹ *
        ∫ t in (0 : ℝ)..lemma6SmoothingScale x * r,
          lemma6GammaIntegrand (lemma6SmoothingOrder x) t := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have ha : 0 < lemma6SmoothingScale x := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlog _
  rw [chenPhi_eq_intervalIntegral_max, Real.log_exp,
    max_eq_right (mul_nonneg ha.le hr.le)]

/-- Derivative of the incomplete-gamma smoothing function in logarithmic
coordinates. -/
theorem hasDerivAt_chenPhi_exp
    {x r : ℝ} (hx : 1 < x) (hr : 0 < r) :
    HasDerivAt (fun z : ℝ => chenPhi x (Real.exp z))
      ((((lemma6SmoothingOrder x).factorial : ℝ))⁻¹ *
        (lemma6GammaIntegrand (lemma6SmoothingOrder x)
          (lemma6SmoothingScale x * r) * lemma6SmoothingScale x)) r := by
  let n := lemma6SmoothingOrder x
  let a := lemma6SmoothingScale x
  have hFTC : HasDerivAt
      (fun b : ℝ => ∫ t in (0 : ℝ)..b, lemma6GammaIntegrand n t)
      (lemma6GammaIntegrand n (a * r)) (a * r) :=
    intervalIntegral.integral_hasDerivAt_right
      ((continuous_lemma6GammaIntegrand n).intervalIntegrable 0 (a * r))
      (continuous_lemma6GammaIntegrand n).aestronglyMeasurable.stronglyMeasurableAtFilter
      (continuous_lemma6GammaIntegrand n).continuousAt
  have hupper : HasDerivAt (fun z : ℝ => a * z) a r := by
    simpa using (hasDerivAt_id r).const_mul a
  have hcalc : HasDerivAt
      (fun z : ℝ => ((n.factorial : ℝ))⁻¹ *
        ∫ t in (0 : ℝ)..a * z, lemma6GammaIntegrand n t)
      (((n.factorial : ℝ))⁻¹ * (lemma6GammaIntegrand n (a * r) * a)) r := by
    simpa only [Function.comp_apply, mul_assoc] using
      (hFTC.comp r hupper).const_mul ((n.factorial : ℝ))⁻¹
  apply hcalc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with z hz
  simpa only [n, a] using chenPhi_exp_eq_intervalIntegral hx hz

/-- `chenPhi x` is continuous at every positive argument. -/
theorem continuousAt_chenPhi_of_pos (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (chenPhi x) y := by
  let n := lemma6SmoothingOrder x
  let a := lemma6SmoothingScale x
  let F : ℝ → ℝ := fun b =>
    ∫ t in (0 : ℝ)..b, lemma6GammaIntegrand n t
  have hF : Continuous F :=
    (intervalIntegral.differentiable_integral_of_continuous
      (continuous_lemma6GammaIntegrand n)).continuous
  have hlog : ContinuousAt Real.log y := Real.continuousAt_log hy.ne'
  have hupper : ContinuousAt (fun z : ℝ => max 0 (a * Real.log z)) y := by
    fun_prop
  have hright : ContinuousAt
      (fun z : ℝ => ((n.factorial : ℝ))⁻¹ * F (max 0 (a * Real.log z))) y :=
    continuousAt_const.mul (hF.continuousAt.comp hupper)
  apply hright.congr_of_eventuallyEq
  filter_upwards with z
  rw [chenPhi_eq_intervalIntegral_max]

/-- On positive inputs, the reciprocal form is the gamma CDF with upper
endpoint `-a log u`. -/
theorem lemma6PhiReciprocal_eq_gamma
    (x : ℝ) {u : ℝ} (_hu : 0 < u) :
    lemma6PhiReciprocal x u =
      (((lemma6SmoothingOrder x).factorial : ℝ)⁻¹ *
        ∫ t in Ioc (0 : ℝ)
          (-(lemma6SmoothingScale x * Real.log u)),
          lemma6GammaIntegrand (lemma6SmoothingOrder x) t : ℝ) := by
  unfold lemma6PhiReciprocal chenPhi lemma6SmoothingScale lemma6SmoothingOrder
  norm_cast
  change ((⌊Real.log x⌋₊.factorial : ℝ)⁻¹ *
      (∫ t in Ioc (0 : ℝ) ((Real.log x) ^ (1.1 : ℝ) * Real.log u⁻¹),
        lemma6GammaIntegrand ⌊Real.log x⌋₊ t)) = _
  rw [Real.log_inv]
  congr 2
  ring_nf

/-- The reciprocal smoothing function vanishes on `[1,∞)`. -/
theorem lemma6PhiReciprocal_eq_zero_of_one_le
    {x u : ℝ} (hx : 1 < x) (hu : 1 ≤ u) :
    lemma6PhiReciprocal x u = 0 := by
  have hupos : 0 < u := zero_lt_one.trans_le hu
  have hu0 : 0 ≤ u⁻¹ := inv_nonneg.mpr (zero_le_one.trans hu)
  have hu1 : u⁻¹ ≤ 1 := (inv_le_one₀ hupos).2 hu
  unfold lemma6PhiReciprocal
  exact_mod_cast chenPhi_eq_zero hx hu0 hu1

/-- The reciprocal smoothing function is continuous at positive inputs,
as required by Mellin inversion. -/
theorem continuousAt_lemma6PhiReciprocal_of_pos
    (x : ℝ) {u : ℝ} (hu : 0 < u) :
    ContinuousAt (lemma6PhiReciprocal x) u := by
  unfold lemma6PhiReciprocal
  exact Complex.continuous_ofReal.continuousAt.comp
    ((continuousAt_chenPhi_of_pos x (inv_pos.mpr hu)).comp
      (continuousAt_inv₀ hu.ne'))

/-- The reciprocal smoothing function has norm at most one on the positive
axis. -/
theorem norm_lemma6PhiReciprocal_le_one
    {x u : ℝ} (hx : 1 < x) (hu : 0 < u) :
    ‖lemma6PhiReciprocal x u‖ ≤ 1 := by
  have hnonneg : 0 ≤ chenPhi x u⁻¹ :=
    chenPhi_nonneg x hx (inv_nonneg.mpr hu.le)
  have hle : chenPhi x u⁻¹ ≤ 1 :=
    chenPhi_le_one x hx (inv_nonneg.mpr hu.le)
  rw [lemma6PhiReciprocal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnonneg]
  exact hle

/-- Continuity of the reciprocal smoothing function on the positive axis. -/
theorem continuousOn_lemma6PhiReciprocal_Ioi (x : ℝ) :
    ContinuousOn (lemma6PhiReciprocal x) (Ioi 0) := by
  intro u hu
  exact (continuousAt_lemma6PhiReciprocal_of_pos x hu).continuousWithinAt

/-- The Mellin integral of `u ↦ Φ(1/u)` converges on every vertical
line of positive real part. -/
theorem mellinConvergent_lemma6PhiReciprocal
    {x σ : ℝ} (hx : 1 < x) (hσ : 0 < σ) :
    MellinConvergent (lemma6PhiReciprocal x) (σ : ℂ) := by
  have hbase : MellinConvergent
      (indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℂ))) (σ : ℂ) :=
    (hasMellin_one_Ioc (by simpa using hσ)).1
  rw [MellinConvergent] at hbase ⊢
  rw [IntegrableOn] at hbase ⊢
  apply hbase.mono
  · have hcont : ContinuousOn
        (fun u : ℝ => (u : ℂ) ^ ((σ : ℂ) - 1) •
          lemma6PhiReciprocal x u) (Ioi 0) := by
      intro u hu
      have hpow : ContinuousAt
          (fun v : ℝ => (v : ℂ) ^ ((σ : ℂ) - 1)) u := by
        exact Complex.continuousAt_ofReal_cpow_const u ((σ : ℂ) - 1)
          (Or.inr hu.ne')
      exact (hpow.smul (continuousAt_lemma6PhiReciprocal_of_pos x hu)).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards with u hu
    have hu0 : 0 < u := hu
    by_cases hu1 : u < 1
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨hu0, hu1.le⟩)]
      simp only [norm_smul, norm_one, mul_one]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left
          (norm_lemma6PhiReciprocal_le_one hx hu0) (norm_nonneg
            ((u : ℂ) ^ ((σ : ℂ) - 1))))
    · have hzero := lemma6PhiReciprocal_eq_zero_of_one_le hx (le_of_not_gt hu1)
      rw [hzero, smul_zero, norm_zero]
      exact norm_nonneg _

/-- On a positive vertical line, Chen's rational Mellin kernel is dominated
by a scaled Cauchy kernel as soon as its gamma order is at least one. -/
theorem norm_lemma6SmoothingMellinKernel_le_cauchy
    {x σ : ℝ} (ha : 0 < lemma6SmoothingScale x)
    (hn : 1 ≤ lemma6SmoothingOrder x) (hσ : 0 < σ) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel x
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      σ⁻¹ * (1 + (ν / lemma6SmoothingScale x) ^ 2)⁻¹ := by
  let a : ℝ := lemma6SmoothingScale x
  let n : ℕ := lemma6SmoothingOrder x
  let s : ℂ := (σ : ℂ) + (ν : ℂ) * Complex.I
  let z : ℂ := 1 + s / (a : ℂ)
  have ha' : 0 < a := ha
  have hsre : s.re = σ := by
    dsimp only [s]
    simp
  have hsim : s.im = ν := by
    dsimp only [s]
    simp
  have hsNorm : σ ≤ ‖s‖ := by
    rw [← hsre]
    exact Complex.abs_re_le_norm s |>.trans' (le_abs_self _)
  have hsNormPos : 0 < ‖s‖ := hσ.trans_le hsNorm
  have hzre : z.re = 1 + σ / a := by
    dsimp only [z]
    rw [Complex.add_re, Complex.one_re, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hsre, hsim,
      Complex.normSq_ofReal]
    field_simp
    ring
  have hzim : z.im = ν / a := by
    dsimp only [z]
    rw [Complex.add_im, Complex.one_im, Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hsre, hsim, mul_zero,
      zero_add, Complex.normSq_ofReal]
    field_simp
    ring
  have hzsq : ‖z‖ ^ 2 = (1 + σ / a) ^ 2 + (ν / a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hzreOne : 1 ≤ 1 + σ / a := by
    have : 0 ≤ σ / a := (div_pos hσ ha').le
    linarith
  have hzOne : 1 ≤ ‖z‖ := by
    have hz0 := norm_nonneg z
    nlinarith [sq_nonneg (ν / a), sq_nonneg (1 + σ / a)]
  have hbase : 1 + (ν / a) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hzsq]
    nlinarith [sq_nonneg (1 + σ / a - 1)]
  have hpow : ‖z‖ ^ 2 ≤ ‖z‖ ^ (n + 1) := by
    exact pow_le_pow_right₀ hzOne (by dsimp only [n]; omega)
  have hden : 1 + (ν / a) ^ 2 ≤ ‖z‖ ^ (n + 1) :=
    hbase.trans hpow
  have hdenPos : 0 < 1 + (ν / a) ^ 2 := by positivity
  have hzpowPos : 0 < ‖z‖ ^ (n + 1) :=
    pow_pos (zero_lt_one.trans_le hzOne) _
  have hsInv : ‖s‖⁻¹ ≤ σ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hσ hsNorm
  have hzInv : (‖z‖ ^ (n + 1))⁻¹ ≤
      (1 + (ν / a) ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hdenPos hden
  change ‖s⁻¹ * (z ^ (n + 1))⁻¹‖ ≤
    σ⁻¹ * (1 + (ν / a) ^ 2)⁻¹
  rw [norm_mul, norm_inv, norm_inv, norm_pow]
  exact mul_le_mul hsInv hzInv
    (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))
    (inv_nonneg.mpr hσ.le)

/-- A stronger, uniform quartic-tail bound for Chen's exact rational
Mellin kernel.  This avoids replacing `|1+s/a|` by `1+|ν|/a` with an
exponentiated comparison constant, which would not be uniform in the
smoothing order. -/
theorem norm_lemma6SmoothingMellinKernel_le_quartic
    {x σ : ℝ} (ha : 0 < lemma6SmoothingScale x)
    (hn : 3 ≤ lemma6SmoothingOrder x) (hσ : 0 < σ) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel x
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      σ⁻¹ * ((1 + (ν / lemma6SmoothingScale x) ^ 2) ^ 2)⁻¹ := by
  let a : ℝ := lemma6SmoothingScale x
  let n : ℕ := lemma6SmoothingOrder x
  let s : ℂ := (σ : ℂ) + (ν : ℂ) * Complex.I
  let z : ℂ := 1 + s / (a : ℂ)
  have ha' : 0 < a := ha
  have hsre : s.re = σ := by
    dsimp only [s]
    simp
  have hsim : s.im = ν := by
    dsimp only [s]
    simp
  have hsNorm : σ ≤ ‖s‖ := by
    rw [← hsre]
    exact Complex.abs_re_le_norm s |>.trans' (le_abs_self _)
  have hzre : z.re = 1 + σ / a := by
    dsimp only [z]
    rw [Complex.add_re, Complex.one_re, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hsre, hsim,
      Complex.normSq_ofReal]
    field_simp
    ring
  have hzim : z.im = ν / a := by
    dsimp only [z]
    rw [Complex.add_im, Complex.one_im, Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hsre, hsim, mul_zero,
      zero_add, Complex.normSq_ofReal]
    field_simp
    ring
  have hzsq : ‖z‖ ^ 2 = (1 + σ / a) ^ 2 + (ν / a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hzOne : 1 ≤ ‖z‖ := by
    have hz0 := norm_nonneg z
    have hσa : 0 ≤ σ / a := (div_pos hσ ha').le
    rw [← sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1) hz0, hzsq]
    nlinarith [sq_nonneg (ν / a)]
  have hbase : 1 + (ν / a) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hzsq]
    have hσa : 0 ≤ σ / a := (div_pos hσ ha').le
    nlinarith [sq_nonneg (1 + σ / a - 1)]
  have hbase0 : 0 ≤ 1 + (ν / a) ^ 2 := by positivity
  have hfour : (1 + (ν / a) ^ 2) ^ 2 ≤ ‖z‖ ^ 4 := by
    calc
      (1 + (ν / a) ^ 2) ^ 2 ≤ (‖z‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ hbase0 hbase 2
      _ = ‖z‖ ^ 4 := by ring
  have hpow : ‖z‖ ^ 4 ≤ ‖z‖ ^ (n + 1) := by
    exact pow_le_pow_right₀ hzOne (by dsimp only [n]; omega)
  have hden : (1 + (ν / a) ^ 2) ^ 2 ≤ ‖z‖ ^ (n + 1) :=
    hfour.trans hpow
  have hdenPos : 0 < (1 + (ν / a) ^ 2) ^ 2 := by positivity
  have hzpowPos : 0 < ‖z‖ ^ (n + 1) :=
    pow_pos (zero_lt_one.trans_le hzOne) _
  have hsInv : ‖s‖⁻¹ ≤ σ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hσ hsNorm
  have hzInv : (‖z‖ ^ (n + 1))⁻¹ ≤
      ((1 + (ν / a) ^ 2) ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hdenPos hden
  change ‖s⁻¹ * (z ^ (n + 1))⁻¹‖ ≤
    σ⁻¹ * ((1 + (ν / a) ^ 2) ^ 2)⁻¹
  rw [norm_mul, norm_inv, norm_inv, norm_pow]
  exact mul_le_mul hsInv hzInv
    (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))
    (inv_nonneg.mpr hσ.le)

/-- The smoothing kernel is vertically integrable on every positive line
once `[лog x] ≥ 1`. -/
theorem verticalIntegrable_lemma6SmoothingMellinKernel
    {x σ : ℝ} (ha : 0 < lemma6SmoothingScale x)
    (hn : 1 ≤ lemma6SmoothingOrder x) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (lemma6SmoothingMellinKernel x) σ := by
  let a : ℝ := lemma6SmoothingScale x
  have ha' : a ≠ 0 := (show 0 < a from ha).ne'
  have hcauchy : Integrable (fun ν : ℝ =>
      σ⁻¹ * (1 + (ν / a) ^ 2)⁻¹) := by
    have hcomp := integrable_inv_one_add_sq.comp_mul_left'
      (R := a⁻¹) (inv_ne_zero ha')
    have heq : (fun ν : ℝ => (1 + (a⁻¹ * ν) ^ 2)⁻¹) =
        (fun ν : ℝ => (1 + (ν / a) ^ 2)⁻¹) := by
      funext ν
      congr 2
      field_simp
    rw [heq] at hcomp
    exact hcomp.const_mul σ⁻¹
  apply hcauchy.mono
  · unfold lemma6SmoothingMellinKernel
    fun_prop
  · apply ae_of_all
    intro ν
    have hbound := norm_lemma6SmoothingMellinKernel_le_cauchy ha hn hσ ν
    have hnonneg : 0 ≤
        σ⁻¹ * (1 + (ν / a) ^ 2)⁻¹ := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound

/-- Multiplying the vertical smoothing kernel by a positive real base to a
complex power preserves integrability.  The norm of the power is constant
along a vertical line, so this is the exact interface needed to move the
finite `(p₁,p₂,n)` sums through the Mellin integral. -/
theorem integrable_cpow_mul_lemma6SmoothingMellinKernel
    {x y σ : ℝ} (hy : 0 < y)
    (ha : 0 < lemma6SmoothingScale x)
    (hn : 1 ≤ lemma6SmoothingOrder x) (hσ : 0 < σ) :
    Integrable (fun ν : ℝ =>
      (y : ℂ) ^ ((σ : ℂ) + (ν : ℂ) * Complex.I) *
        lemma6SmoothingMellinKernel x
          ((σ : ℂ) + (ν : ℂ) * Complex.I)) := by
  letI : NeZero (y : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hy.ne'⟩
  have hk := verticalIntegrable_lemma6SmoothingMellinKernel ha hn hσ
  rw [Complex.VerticalIntegrable] at hk
  apply hk.bdd_mul (c := y ^ σ)
  · exact ((continuous_const_cpow (y : ℂ)).comp
      (by fun_prop)).aestronglyMeasurable
  · apply ae_of_all
    intro ν
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    exact le_rfl

/-! ### Logarithmic-coordinate form of the Mellin transform -/

/-- The Mellin transform becomes a bilateral Laplace integral after the
substitution `u = exp (-r)`.  This is extracted from Mathlib's
`mellin_eq_fourier`, whose proof uses precisely that substitution. -/
theorem mellin_eq_integral_exp_neg_mul (f : ℝ → ℂ) (s : ℂ) :
    mellin f s =
      ∫ r : ℝ, Complex.exp (-s * (r : ℂ)) * f (Real.exp (-r)) := by
  rw [mellin_eq_fourier, fourier_eq']
  apply integral_congr_ae
  filter_upwards with r
  have hsource :
      Complex.exp (-s * (r : ℂ)) • f (Real.exp (-r)) =
        Complex.exp
            (((-(2 : ℝ) * Real.pi *
              inner ℝ r (s.im / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) •
          (Real.exp (-s.re * r) • f (Real.exp (-r))) := by
    trans Complex.exp (-s.im * r * Complex.I) •
        (Real.exp (-s.re * r) • f (Real.exp (-r)))
    · conv => lhs; rw [← Complex.re_add_im s]
      rw [neg_add, add_mul, Complex.exp_add, mul_comm, ← smul_eq_mul,
        smul_assoc]
      norm_cast
      push_cast
      ring_nf
    · congr
      simp [field]
  simpa only [smul_eq_mul, RCLike.real_smul_eq_coe_mul] using hsource.symm

/-- Since `Φ(1/u)` vanishes for `u ≥ 1`, its logarithmic-coordinate
Mellin integral is supported on `r > 0`. -/
theorem mellin_lemma6PhiReciprocal_eq_integral_Ioi
    {x : ℝ} (hx : 1 < x) (s : ℂ) :
    mellin (lemma6PhiReciprocal x) s =
      ∫ r : ℝ in Ioi 0,
        Complex.exp (-s * (r : ℂ)) * (chenPhi x (Real.exp r) : ℝ) := by
  rw [mellin_eq_integral_exp_neg_mul]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : 0 < r
  · rw [indicator_of_mem (mem_Ioi.mpr hr)]
    unfold lemma6PhiReciprocal
    rw [← Real.exp_neg, neg_neg]
  · have hrmem : r ∉ Ioi (0 : ℝ) := by
      simpa only [mem_Ioi, not_lt] using le_of_not_gt hr
    rw [indicator_of_notMem hrmem]
    have hexp : 1 ≤ Real.exp (-r) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonneg.mpr (le_of_not_gt hr))
    rw [lemma6PhiReciprocal_eq_zero_of_one_le hx hexp, mul_zero]

/-! ### Complex exponential moments on the positive half-line -/

/-- Absolute convergence of the complex exponential moments used in the
Laplace transform of the incomplete-gamma cutoff. -/
private theorem integrableOn_complex_exp_moment
    {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    IntegrableOn
      (fun r : ℝ => Complex.exp (-c * (r : ℂ)) * (r : ℂ) ^ n)
      (Ioi 0) := by
  let f : ℝ → ℂ := fun r =>
    Complex.exp (-c * (r : ℂ)) * (r : ℂ) ^ n
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  rw [IntegrableOn]
  apply (integrable_norm_iff hf.aestronglyMeasurable.restrict).mp
  have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := c.re)
    (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
    (by norm_num) hc
  rw [IntegrableOn] at hreal
  apply hreal.congr
  apply ae_restrict_iff' measurableSet_Ioi |>.2
  filter_upwards with r hr
  have hrpos : 0 < r := hr
  dsimp only [f]
  rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hrpos]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_natCast,
    Real.rpow_one]
  ring_nf

/-- A polynomial times a complex exponential with positive decay tends to
zero at `+∞`. -/
private theorem tendsto_complex_exp_moment_atTop
    {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    Tendsto
      (fun r : ℝ => Complex.exp (-c * (r : ℂ)) * (r : ℂ) ^ n)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hreal := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (n : ℝ) c.re hc
  apply hreal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_natCast]
  ring_nf

/-- The elementary complex Gamma integral at a natural exponent.  Mathlib's
standard scaling theorem assumes a real scale; this induction supplies the
right-half-plane complex scale needed by Chen's kernel. -/
private theorem integral_complex_exp_moment_Ioi
    {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    (∫ r : ℝ in Ioi 0,
        Complex.exp (-c * (r : ℂ)) * (r : ℂ) ^ n) =
      (n.factorial : ℂ) / c ^ (n + 1) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  induction n with
  | zero =>
      simpa [hc0, div_eq_mul_inv] using
        (integral_exp_mul_complex_Ioi (a := -c) (by simpa using hc) 0)
  | succ n ih =>
      let u : ℝ → ℂ := fun r => (r : ℂ) ^ (n + 1)
      let u' : ℝ → ℂ := fun r =>
        ((n + 1 : ℕ) : ℂ) * (r : ℂ) ^ n
      let v : ℝ → ℂ := fun r =>
        (-c)⁻¹ * Complex.exp (-c * (r : ℂ))
      let v' : ℝ → ℂ := fun r =>
        Complex.exp (-c * (r : ℂ))
      have hu : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt u (u' r) r := by
        intro r _
        have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r :=
          Complex.ofRealCLM.hasDerivAt
        have hp := hbase.pow (n + 1)
        change HasDerivAt u _ r at hp
        apply hp.congr_deriv
        simp [u', Nat.cast_add]
      have hv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt v (v' r) r := by
        intro r _
        have hexp : HasDerivAt
            (fun t : ℝ => Complex.exp (-c * (t : ℂ)))
            (-c * Complex.exp (-c * (r : ℂ))) r := by
          have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r :=
            Complex.ofRealCLM.hasDerivAt
          have hlin : HasDerivAt (fun t : ℝ => -c * (t : ℂ)) (-c) r := by
            simpa only [mul_one] using hbase.const_mul (-c)
          have hcomp : HasDerivAt
              (Complex.exp ∘ (fun t : ℝ => -c * (t : ℂ)))
              (Complex.exp (-c * (r : ℂ)) * (-c)) r :=
            (Complex.hasDerivAt_exp (-c * (r : ℂ))).comp r hlin
          convert hcomp using 1
          · funext t
            rfl
          · ring
        dsimp only [v, v']
        have hnc : -c ≠ 0 := neg_ne_zero.mpr hc0
        simpa only [inv_mul_cancel_left₀ hnc] using hexp.const_mul (-c)⁻¹
      have huv' : IntegrableOn (u * v') (Ioi (0 : ℝ)) := by
        have hm := integrableOn_complex_exp_moment hc (n + 1)
        apply IntegrableOn.congr_fun hm
        · intro r hr
          dsimp only [u, v', Pi.mul_apply]
          ring
        · exact measurableSet_Ioi
      have hu'v : IntegrableOn (u' * v) (Ioi (0 : ℝ)) := by
        have hm := (integrableOn_complex_exp_moment hc n).const_mul
          (((n + 1 : ℕ) : ℂ) * (-c)⁻¹)
        apply IntegrableOn.congr_fun hm
        · intro r hr
          dsimp only [u', v, Pi.mul_apply]
          ring
        · exact measurableSet_Ioi
      have hzero : Tendsto (u * v) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        have hcont : ContinuousAt (u * v) 0 := by
          dsimp only [u, v, Pi.mul_apply]
          fun_prop
        have ht : Tendsto (u * v) (nhdsWithin 0 (Ioi 0))
            (nhds ((u * v) 0)) :=
          hcont.tendsto.mono_left inf_le_left
        have hval : (u * v) 0 = 0 := by simp [u]
        rw [hval] at ht
        exact ht
      have hinfty : Tendsto (u * v) atTop (nhds 0) := by
        have hm := tendsto_complex_exp_moment_atTop hc (n + 1)
        have hconst : Tendsto (fun _ : ℝ => (-c)⁻¹) atTop (nhds (-c)⁻¹) :=
          tendsto_const_nhds
        have hmul := hconst.mul hm
        have hmul0 : Tendsto
            (fun r : ℝ => (-c)⁻¹ *
              (Complex.exp (-c * (r : ℂ)) * (r : ℂ) ^ (n + 1)))
            atTop (nhds 0) := by
          simpa only [mul_zero] using hmul
        apply hmul0.congr'
        filter_upwards with r
        dsimp only [u, v, Pi.mul_apply]
        ring
      have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
        hu hv huv' hu'v hzero hinfty
      dsimp only [u, u', v, v', Pi.mul_apply] at hibp
      rw [show (fun r : ℝ =>
          ((n + 1 : ℕ) : ℂ) * (r : ℂ) ^ n *
            ((-c)⁻¹ * Complex.exp (-c * (r : ℂ)))) =
          fun r : ℝ =>
            (((n + 1 : ℕ) : ℂ) * (-c)⁻¹) *
              (Complex.exp (-c * (r : ℂ)) * (r : ℂ) ^ n) by
            funext r
            ring] at hibp
      rw [integral_const_mul, ih] at hibp
      rw [show (fun r : ℝ =>
          (r : ℂ) ^ (n + 1) * Complex.exp (-c * (r : ℂ))) =
          fun r : ℝ =>
            Complex.exp (-c * (r : ℂ)) * (r : ℂ) ^ (n + 1) by
            funext r
            ring] at hibp
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      apply hibp.trans
      field_simp [hc0]
      push_cast
      ring

/-! ### Exact Mellin transform of Chen's smoothing kernel -/

/-- The incomplete-gamma cutoff has exactly Chen's rational Mellin
transform on the right half-plane. -/
theorem mellin_lemma6PhiReciprocal_eq_kernel
    {x : ℝ} (hx : 1 < x) {s : ℂ} (hs : 0 < s.re) :
    mellin (lemma6PhiReciprocal x) s =
      lemma6SmoothingMellinKernel x s := by
  let n : ℕ := lemma6SmoothingOrder x
  let a : ℝ := lemma6SmoothingScale x
  let u : ℝ → ℂ := fun r => (chenPhi x (Real.exp r) : ℝ)
  let u' : ℝ → ℂ := fun r =>
    (n.factorial : ℂ)⁻¹ * (a : ℂ) ^ (n + 1) *
      Complex.exp (-(a : ℂ) * (r : ℂ)) * (r : ℂ) ^ n
  let v : ℝ → ℂ := fun r =>
    (-s)⁻¹ * Complex.exp (-s * (r : ℂ))
  let v' : ℝ → ℂ := fun r =>
    Complex.exp (-s * (r : ℂ))
  have hlog : 0 < Real.log x := Real.log_pos hx
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hlog _
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hu : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt u (u' r) r := by
    intro r hr
    have hreal := hasDerivAt_chenPhi_exp hx hr
    have hof := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hreal
    change HasDerivAt u
      (((((n.factorial : ℝ))⁻¹ *
        (lemma6GammaIntegrand n (a * r) * a) : ℝ) : ℂ)) r at hof
    apply hof.congr_deriv
    dsimp only [u']
    push_cast
    unfold lemma6GammaIntegrand
    push_cast
    rw [mul_pow]
    ring_nf
  have hv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt v (v' r) r := by
    intro r _
    have hexp : HasDerivAt
        (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
        (-s * Complex.exp (-s * (r : ℂ))) r := by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r :=
        Complex.ofRealCLM.hasDerivAt
      have hlin : HasDerivAt (fun t : ℝ => -s * (t : ℂ)) (-s) r := by
        simpa only [mul_one] using hbase.const_mul (-s)
      have hcomp : HasDerivAt
          (Complex.exp ∘ (fun t : ℝ => -s * (t : ℂ)))
          (Complex.exp (-s * (r : ℂ)) * (-s)) r :=
        (Complex.hasDerivAt_exp (-s * (r : ℂ))).comp r hlin
      convert hcomp using 1
      · funext t
        rfl
      · ring
    dsimp only [v, v']
    have hns : -s ≠ 0 := neg_ne_zero.mpr hs0
    simpa only [inv_mul_cancel_left₀ hns] using hexp.const_mul (-s)⁻¹
  have hu_cont : ContinuousOn u (Ioi (0 : ℝ)) := by
    intro r hr
    exact (hu r hr).continuousAt.continuousWithinAt
  have huv' : IntegrableOn (u * v') (Ioi (0 : ℝ)) := by
    have hbase := integrableOn_exp_mul_complex_Ioi
      (a := -s) (by simpa using hs) 0
    rw [IntegrableOn] at hbase ⊢
    apply hbase.mono
    · exact (hu_cont.mul (by fun_prop : ContinuousOn v' (Ioi (0 : ℝ)))).aestronglyMeasurable
        measurableSet_Ioi
    · apply ae_restrict_iff' measurableSet_Ioi |>.2
      filter_upwards with r hr
      have hnonneg : 0 ≤ chenPhi x (Real.exp r) :=
        chenPhi_nonneg x hx (Real.exp_pos r).le
      have hle : chenPhi x (Real.exp r) ≤ 1 :=
        chenPhi_le_one x hx (Real.exp_pos r).le
      dsimp only [u, v', Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnonneg]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hsu : 0 < (s + (a : ℂ)).re := by
    simpa using add_pos hs ha
  have hu'v : IntegrableOn (u' * v) (Ioi (0 : ℝ)) := by
    let K : ℂ :=
      (((n.factorial : ℝ)⁻¹ : ℝ) : ℂ) * (a : ℂ) ^ (n + 1) * (-s)⁻¹
    have hm := (integrableOn_complex_exp_moment hsu n).const_mul K
    apply IntegrableOn.congr_fun hm
    · intro r hr
      dsimp only [u', v, K, Pi.mul_apply]
      rw [show -(s + (a : ℂ)) * (r : ℂ) =
          (-(a : ℂ) * (r : ℂ)) + (-s * (r : ℂ)) by ring,
        Complex.exp_add]
      push_cast
      ring
    · exact measurableSet_Ioi
  have hzero : Tendsto (u * v) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hu0value : u 0 = 0 := by
      dsimp only [u]
      rw [Real.exp_zero, chenPhi_eq_zero hx zero_le_one le_rfl]
      norm_num
    have hu0 : Tendsto u (nhds (0 : ℝ)) (nhds 0) := by
      have hcont : ContinuousAt u 0 := by
        have hexp : ContinuousAt Real.exp 0 := Real.continuous_exp.continuousAt
        have hcphi : ContinuousAt (chenPhi x) (Real.exp 0) :=
          continuousAt_chenPhi_of_pos x (Real.exp_pos 0)
        have hrealcont := hcphi.comp hexp
        dsimp only [u]
        exact Complex.continuous_ofReal.continuousAt.comp hrealcont
      simpa only [hu0value] using hcont.tendsto
    have hv0 : Tendsto v (nhds (0 : ℝ)) (nhds (v 0)) := by
      exact (by fun_prop : ContinuousAt v 0).tendsto
    have hmul := hu0.mul hv0
    change Tendsto (fun r => u r * v r)
      (nhds 0 ⊓ principal (Ioi 0)) (nhds 0)
    simpa only [zero_mul] using hmul.mono_left inf_le_left
  have hinfty : Tendsto (u * v) atTop (nhds 0) := by
    have hubound : IsBoundedUnder (· ≤ ·) atTop (norm ∘ u) := by
      apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      have hnonneg : 0 ≤ chenPhi x (Real.exp r) :=
        chenPhi_nonneg x hx (Real.exp_pos r).le
      have hle : chenPhi x (Real.exp r) ≤ 1 :=
        chenPhi_le_one x hx (Real.exp_pos r).le
      dsimp only [Function.comp_apply, u]
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have hexp := tendsto_complex_exp_moment_atTop hs 0
    have hvzero : Tendsto v atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℝ => (-s)⁻¹) atTop (nhds (-s)⁻¹) :=
        tendsto_const_nhds
      have hmul := hconst.mul hexp
      have hmul0 : Tendsto
          (fun r : ℝ => (-s)⁻¹ *
            (Complex.exp (-s * (r : ℂ)) * (r : ℂ) ^ 0))
          atTop (nhds 0) := by
        simpa only [mul_zero] using hmul
      apply hmul0.congr'
      filter_upwards with r
      dsimp only [v]
      simp only [pow_zero, mul_one]
    exact isBoundedUnder_le_mul_tendsto_zero hubound hvzero
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    hu hv huv' hu'v hzero hinfty
  dsimp only [u, u', v, v', Pi.mul_apply] at hibp
  rw [show (fun r : ℝ =>
      (chenPhi x (Real.exp r) : ℝ) * Complex.exp (-s * (r : ℂ))) =
      fun r : ℝ =>
        Complex.exp (-s * (r : ℂ)) * (chenPhi x (Real.exp r) : ℝ) by
        funext r
        ring] at hibp
  rw [mellin_lemma6PhiReciprocal_eq_integral_Ioi hx]
  rw [hibp]
  simp only [zero_sub, neg_zero]
  let K : ℂ :=
    (n.factorial : ℂ)⁻¹ * (a : ℂ) ^ (n + 1) * (-s)⁻¹
  have hK : (fun r : ℝ =>
      ((n.factorial : ℂ)⁻¹ * (a : ℂ) ^ (n + 1) *
          Complex.exp (-(a : ℂ) * (r : ℂ)) * (r : ℂ) ^ n) *
        ((-s)⁻¹ * Complex.exp (-s * (r : ℂ)))) =
      fun r : ℝ => K *
        (Complex.exp (-(s + (a : ℂ)) * (r : ℂ)) * (r : ℂ) ^ n) := by
    funext r
    dsimp only [K]
    rw [show -(s + (a : ℂ)) * (r : ℂ) =
        (-(a : ℂ) * (r : ℂ)) + (-s * (r : ℂ)) by ring,
      Complex.exp_add]
    ring
  rw [hK]
  rw [integral_const_mul, integral_complex_exp_moment_Ioi hsu n]
  change -(K * ((n.factorial : ℂ) /
      (s + (a : ℂ)) ^ (n + 1))) =
    s⁻¹ * ((1 + s / (a : ℂ)) ^ (n + 1))⁻¹
  dsimp only [K]
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hsa0 : s + (a : ℂ) ≠ 0 := by
    intro h
    rw [h] at hsu
    norm_num at hsu
  have hbase : 1 + s / (a : ℂ) =
      (s + (a : ℂ)) / (a : ℂ) := by
    field_simp [ha0]
    ring
  rw [hbase, div_pow]
  have hfact : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hs0, ha0, hsa0, hfact]

/-- Mellin inversion for the exact rational kernel. -/
theorem mellinInv_lemma6SmoothingMellinKernel
    {x σ u : ℝ} (hx : 1 < x)
    (ha : 0 < lemma6SmoothingScale x)
    (hn : 1 ≤ lemma6SmoothingOrder x)
    (hσ : 0 < σ) (hu : 0 < u) :
    mellinInv σ (lemma6SmoothingMellinKernel x) u =
      lemma6PhiReciprocal x u := by
  calc
    mellinInv σ (lemma6SmoothingMellinKernel x) u =
        mellinInv σ (mellin (lemma6PhiReciprocal x)) u := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards with ν
      rw [mellin_lemma6PhiReciprocal_eq_kernel hx]
      simpa using hσ
    _ = lemma6PhiReciprocal x u := by
      exact mellinInv_mellin_eq σ (lemma6PhiReciprocal x) hu
        (mellinConvergent_lemma6PhiReciprocal hx hσ)
        (by
          have hk := verticalIntegrable_lemma6SmoothingMellinKernel ha hn hσ
          rw [Complex.VerticalIntegrable] at hk ⊢
          apply Integrable.congr hk
          filter_upwards with ν
          exact mellin_lemma6PhiReciprocal_eq_kernel hx
            (by simpa using hσ) |>.symm)
        (continuousAt_lemma6PhiReciprocal_of_pos x hu)

/-- Chen's smoothing function as the vertical integral used in Lemma 6.
The variable `ν` parametrizes the line `Re s = σ`; hence the usual
`1 / (2π i)` contour factor becomes `1 / (2π)`. -/
theorem chenPhi_eq_smoothing_verticalIntegral
    {x y σ : ℝ} (hx : 1 < x)
    (ha : 0 < lemma6SmoothingScale x)
    (hn : 1 ≤ lemma6SmoothingOrder x)
    (hσ : 0 < σ) (hy : 0 < y) :
    (chenPhi x y : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          (y : ℂ) ^ ((σ : ℂ) + (ν : ℂ) * Complex.I) *
            lemma6SmoothingMellinKernel x
              ((σ : ℂ) + (ν : ℂ) * Complex.I) := by
  have hinv := mellinInv_lemma6SmoothingMellinKernel
    hx ha hn hσ (inv_pos.mpr hy)
  have hphi : lemma6PhiReciprocal x y⁻¹ = (chenPhi x y : ℂ) := by
    unfold lemma6PhiReciprocal
    rw [inv_inv]
  rw [hphi] at hinv
  rw [mellinInv] at hinv
  rw [← hinv]
  congr 1
  apply integral_congr_ae
  filter_upwards with ν
  have hyarg : Complex.arg (y : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact Real.pi_ne_zero.symm
  rw [show ((y⁻¹ : ℝ) : ℂ) = (y : ℂ)⁻¹ by norm_cast,
    Complex.inv_cpow _ _ hyarg, Complex.cpow_neg, inv_inv]
  simp only [smul_eq_mul]

end Chen
