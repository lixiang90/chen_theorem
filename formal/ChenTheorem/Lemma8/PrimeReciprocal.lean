import ChenTheorem.Lemma7.PrimeNumberTheorem
import ChenTheorem.Main.NumericalBounds
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Filter Real
open scoped Classical Interval

namespace Chen

/-!
# Lemma 8: prime-reciprocal partial summation

Between equations (23) and (24), Chen twice replaces a sum over primes by a
Stieltjes integral.  The required analytic fact is the Mertens theorem for
prime reciprocals, uniformly on fixed power intervals.  Mathlib 4.32.2 does
not yet provide this theorem, so the precise multiplicative-error statement
used by the paper is isolated below as a named trust-boundary input.

The PNT-based Mertens theorem is imported from `PrimeNumberTheoremAnd` and
repackaged below in the fixed-power-interval form used by both partial
summations.  The complete numerical estimate (24) is proved independently in
Lean.
-/

/-- The prime harmonic sum with a real cutoff. -/
noncomputable def primeReciprocalSum (y : ℝ) : ℝ :=
  ∑ p ∈ Finset.Iic ⌊y⌋₊ with p.Prime, (p : ℝ)⁻¹

/-- Mertens' theorem for prime reciprocals, in the strong form where the
constant term has a limit.  This is the form needed when subtracting the
values at two endpoints of a fixed power interval. -/
theorem primeReciprocal_mertens :
    Tendsto (fun y : ℝ =>
      primeReciprocalSum y - Real.log (Real.log y)) atTop
      (nhds meisselMertensConstant) := by
  simpa only [primeReciprocalSum, one_div] using
    RS_prime.mertens_second_theorem

/-- The vanishing error in the prime-reciprocal Mertens theorem. -/
noncomputable def primeReciprocalError (y : ℝ) : ℝ :=
  primeReciprocalSum y - Real.log (Real.log y) -
    meisselMertensConstant

theorem primeReciprocalError_tendsto_zero :
    Tendsto primeReciprocalError atTop (nhds 0) := by
  have hconst : Tendsto (fun _ : ℝ => meisselMertensConstant) atTop
      (nhds meisselMertensConstant) := tendsto_const_nhds
  change Tendsto (fun y : ℝ =>
    primeReciprocalSum y - Real.log (Real.log y) -
      meisselMertensConstant) atTop (nhds 0)
  simpa using primeReciprocal_mertens.sub hconst

theorem eventually_abs_primeReciprocalError_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |primeReciprocalError y| < ε := by
  have hball := primeReciprocalError_tendsto_zero.eventually
    (Metric.ball_mem_nhds (0 : ℝ) hε)
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hball

/-- The coefficient sequence whose cumulative sum is
`primeReciprocalSum`. -/
noncomputable def primeReciprocalIndicator (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ)⁻¹ else 0

theorem sum_primeReciprocalIndicator_Icc (y : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, primeReciprocalIndicator n =
      primeReciprocalSum y := by
  unfold primeReciprocalIndicator primeReciprocalSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp
  · intro n _hn
    rfl

/-- Finite Abel summation for a prime-reciprocal weighted sum. -/
theorem primeReciprocal_abel
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime,
        f p * (p : ℝ)⁻¹ =
      f b * primeReciprocalSum b - f a * primeReciprocalSum a -
        ∫ t in Set.Ioc a b, deriv f t * primeReciprocalSum t := by
  have h := sum_mul_eq_sub_sub_integral_mul
    (c := primeReciprocalIndicator) (f := f) ha hab hf_diff hf_int
  simp_rw [sum_primeReciprocalIndicator_Icc] at h
  rw [← h, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [primeReciprocalIndicator]
  split_ifs <;> ring

/-- Integration by parts for the main term `log log t + B` in Mertens'
theorem. -/
theorem mertens_main_integration_by_parts
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    ∫ t in Set.Ioc a b, f t / (t * Real.log t) =
      f b * (Real.log (Real.log b) + meisselMertensConstant) -
        f a * (Real.log (Real.log a) + meisselMertensConstant) -
          ∫ t in Set.Ioc a b,
            deriv f t *
              (Real.log (Real.log t) + meisselMertensConstant) := by
  let v : ℝ → ℝ := fun t =>
    Real.log (Real.log t) + meisselMertensConstant
  let v' : ℝ → ℝ := fun t => 1 / (t * Real.log t)
  have hv_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt v (v' t) t := by
    intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht1).ne'
    have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    simpa [v, v', one_div, div_eq_mul_inv, mul_comm] using
      ((Real.hasDerivAt_log ht0).log hlog0).add_const
        meisselMertensConstant
  have hf_cont : ContinuousOn f [[a, b]] := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact (hf_diff t ht).continuousAt.continuousWithinAt
  have hv_cont : ContinuousOn v [[a, b]] := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact (hv_deriv t ht).continuousAt.continuousWithinAt
  have hf_interval : IntervalIntegrable (deriv f)
      MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hf_int
  have hv_interval : IntervalIntegrable v' MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    apply ContinuousOn.integrableOn_Icc
    dsimp only [v']
    apply ContinuousOn.div continuousOn_const
      (continuousOn_id.mul (Real.continuousOn_log.mono ?_))
    · intro t ht
      have ht1 : 1 < t := ha.trans_le ht.1
      exact mul_ne_zero (zero_lt_one.trans ht1).ne'
        (Real.log_pos ht1).ne'
    · intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [ht.1]
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hf_cont hv_cont
      (fun t ht => (hf_diff t (by
        simp only [min_eq_left hab, max_eq_right hab] at ht
        exact ⟨ht.1.le, ht.2.le⟩)).hasDerivAt)
      (fun t ht => hv_deriv t (by
        simp only [min_eq_left hab, max_eq_right hab] at ht
        exact ⟨ht.1.le, ht.2.le⟩))
      hf_interval hv_interval
  simp only [intervalIntegral.integral_of_le hab] at hparts
  simpa only [v, v', div_eq_mul_inv, one_mul] using hparts

/-- Abel summation with the Mertens main term separated from its vanishing
error.  This is the common exact identity behind both partial summations in
the proof of Lemma 8. -/
theorem primeReciprocal_abel_decomposition
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain_int : MeasureTheory.IntegrableOn (fun t =>
      deriv f t *
        (Real.log (Real.log t) + meisselMertensConstant))
      (Set.Ioc a b))
    (herror_int : MeasureTheory.IntegrableOn (fun t =>
      deriv f t * primeReciprocalError t) (Set.Ioc a b)) :
    ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime,
        f p * (p : ℝ)⁻¹ =
      (∫ t in Set.Ioc a b, f t / (t * Real.log t)) +
        f b * primeReciprocalError b -
          f a * primeReciprocalError a -
            ∫ t in Set.Ioc a b,
              deriv f t * primeReciprocalError t := by
  rw [primeReciprocal_abel (zero_le_one.trans ha.le) hab f hf_diff hf_int]
  have hint :
      (∫ t in Set.Ioc a b, deriv f t * primeReciprocalSum t) =
        (∫ t in Set.Ioc a b,
          deriv f t *
            (Real.log (Real.log t) + meisselMertensConstant)) +
        ∫ t in Set.Ioc a b,
          deriv f t * primeReciprocalError t := by
    rw [← MeasureTheory.integral_add hmain_int herror_int]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [primeReciprocalError]
    ring
  rw [hint, mertens_main_integration_by_parts ha hab f hf_diff hf_int]
  rw [primeReciprocalError, primeReciprocalError]
  ring

/-- Abel summation with the Mertens error separated, with all integrability
conditions discharged from the differentiability and integrability of the
weight.  This is the interface used by both summations in Lemma 8. -/
theorem primeReciprocal_abel_decomposition_auto
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime,
        f p * (p : ℝ)⁻¹ =
      (∫ t in Set.Ioc a b, f t / (t * Real.log t)) +
        f b * primeReciprocalError b -
          f a * primeReciprocalError a -
            ∫ t in Set.Ioc a b,
              deriv f t * primeReciprocalError t := by
  have hmain_cont : ContinuousOn (fun t : ℝ =>
      Real.log (Real.log t) + meisselMertensConstant) (Set.Icc a b) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc a b) :=
      continuousOn_id.log (by
        intro t ht
        exact (zero_lt_one.trans (ha.trans_le ht.1)).ne')
    exact hlog.log (by
      intro t ht
      exact (Real.log_pos (ha.trans_le ht.1)).ne') |>.add continuousOn_const
  have hmain_int : MeasureTheory.IntegrableOn (fun t =>
      deriv f t *
        (Real.log (Real.log t) + meisselMertensConstant))
      (Set.Ioc a b) :=
    (hf_int.mul_continuousOn hmain_cont isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hcum_int : MeasureTheory.IntegrableOn (fun t =>
      deriv f t * primeReciprocalSum t) (Set.Icc a b) := by
    have h := integrableOn_mul_sum_Icc
      (c := primeReciprocalIndicator) (m := 0)
      (a := a) (b := b) (zero_le_one.trans ha.le) hf_int
    simpa only [sum_primeReciprocalIndicator_Icc] using h
  have herror_int : MeasureTheory.IntegrableOn (fun t =>
      deriv f t * primeReciprocalError t) (Set.Ioc a b) := by
    have hsub := hcum_int.sub
      (hf_int.mul_continuousOn hmain_cont isCompact_Icc)
    apply (hsub.mono_set Set.Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
    intro t _ht
    change deriv f t * primeReciprocalSum t -
        deriv f t * (Real.log (Real.log t) + meisselMertensConstant) =
      deriv f t * primeReciprocalError t
    unfold primeReciprocalError
    ring
  exact primeReciprocal_abel_decomposition ha hab f hf_diff hf_int
    hmain_int herror_int

/-- Uniform control of the error terms in Abel summation for a nonnegative
increasing weight. -/
theorem abel_error_le_of_nonneg_deriv
    {a b ε : ℝ} {f f' E : ℝ → ℝ}
    (hab : a ≤ b) (_hε : 0 ≤ ε)
    (hE : ∀ t ∈ Set.Icc a b, |E t| ≤ ε)
    (hfa : 0 ≤ f a) (hfb : 0 ≤ f b)
    (hf' : ∀ t ∈ Set.Ioc a b, 0 ≤ f' t)
    (hf'_int : MeasureTheory.IntegrableOn f' (Set.Ioc a b))
    (hprod_int : MeasureTheory.IntegrableOn (fun t => f' t * E t)
      (Set.Ioc a b))
    (hFTC : (∫ t in Set.Ioc a b, f' t) = f b - f a) :
    f b * E b - f a * E a -
        ∫ t in Set.Ioc a b, f' t * E t ≤
      2 * ε * f b := by
  have hEb : E b ≤ ε :=
    (le_abs_self (E b)).trans (hE b ⟨hab, le_rfl⟩)
  have hEa : -ε ≤ E a := neg_le_of_abs_le (hE a ⟨le_rfl, hab⟩)
  have hleft : f b * E b ≤ f b * ε :=
    mul_le_mul_of_nonneg_left hEb hfb
  have hright : -(f a * E a) ≤ f a * ε := by
    nlinarith [mul_le_mul_of_nonneg_left hEa hfa]
  have hneg_int :
      -(∫ t in Set.Ioc a b, f' t * E t) ≤
        ∫ t in Set.Ioc a b, f' t * ε := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_mono_ae
      hprod_int.neg (hf'_int.mul_const ε)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hEt : -ε ≤ E t := neg_le_of_abs_le
      (hE t ⟨ht.1.le, ht.2⟩)
    change -(f' t * E t) ≤ f' t * ε
    calc
      -(f' t * E t) = f' t * (-E t) := by ring
      _ ≤ f' t * ε :=
        mul_le_mul_of_nonneg_left (by linarith) (hf' t ht)
  rw [MeasureTheory.integral_mul_const, hFTC] at hneg_int
  nlinarith

/-- Uniform control of the error terms in Abel summation for a nonnegative
decreasing weight. -/
theorem abel_error_le_of_nonpos_deriv
    {a b ε : ℝ} {f f' E : ℝ → ℝ}
    (hab : a ≤ b) (_hε : 0 ≤ ε)
    (hE : ∀ t ∈ Set.Icc a b, |E t| ≤ ε)
    (hfa : 0 ≤ f a) (hfb : 0 ≤ f b)
    (hf' : ∀ t ∈ Set.Ioc a b, f' t ≤ 0)
    (hf'_int : MeasureTheory.IntegrableOn f' (Set.Ioc a b))
    (hprod_int : MeasureTheory.IntegrableOn (fun t => f' t * E t)
      (Set.Ioc a b))
    (hFTC : (∫ t in Set.Ioc a b, f' t) = f b - f a) :
    f b * E b - f a * E a -
        ∫ t in Set.Ioc a b, f' t * E t ≤
      2 * ε * f a := by
  have hEb : E b ≤ ε :=
    (le_abs_self (E b)).trans (hE b ⟨hab, le_rfl⟩)
  have hEa : -ε ≤ E a := neg_le_of_abs_le (hE a ⟨le_rfl, hab⟩)
  have hleft : f b * E b ≤ f b * ε :=
    mul_le_mul_of_nonneg_left hEb hfb
  have hright : -(f a * E a) ≤ f a * ε := by
    nlinarith [mul_le_mul_of_nonneg_left hEa hfa]
  have hneg_int :
      -(∫ t in Set.Ioc a b, f' t * E t) ≤
        ∫ t in Set.Ioc a b, -(f' t * ε) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_mono_ae hprod_int.neg
      (hf'_int.mul_const ε).neg
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hEt : E t ≤ ε :=
      (le_abs_self (E t)).trans (hE t ⟨ht.1.le, ht.2⟩)
    change -(f' t * E t) ≤ -(f' t * ε)
    have hmul : f' t * ε ≤ f' t * E t :=
      mul_le_mul_of_nonpos_left hEt (hf' t ht)
    linarith
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_mul_const, hFTC]
    at hneg_int
  nlinarith

/-- Integrability of the Mertens-error term needed in either Abel step. -/
theorem integrableOn_deriv_mul_primeReciprocalError
    {a b : ℝ} (ha : 1 < a) (f : ℝ → ℝ)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun t =>
      deriv f t * primeReciprocalError t) (Set.Ioc a b) := by
  have hmain_cont : ContinuousOn (fun t : ℝ =>
      Real.log (Real.log t) + meisselMertensConstant) (Set.Icc a b) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc a b) :=
      continuousOn_id.log (by
        intro t ht
        exact (zero_lt_one.trans (ha.trans_le ht.1)).ne')
    exact hlog.log (by
      intro t ht
      exact (Real.log_pos (ha.trans_le ht.1)).ne') |>.add continuousOn_const
  have hcum_int : MeasureTheory.IntegrableOn (fun t =>
      deriv f t * primeReciprocalSum t) (Set.Icc a b) := by
    have h := integrableOn_mul_sum_Icc
      (c := primeReciprocalIndicator) (m := 0)
      (a := a) (b := b) (zero_le_one.trans ha.le) hf_int
    simpa only [sum_primeReciprocalIndicator_Icc] using h
  have hsub := hcum_int.sub
    (hf_int.mul_continuousOn hmain_cont isCompact_Icc)
  apply (hsub.mono_set Set.Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
  intro t _ht
  change deriv f t * primeReciprocalSum t -
      deriv f t * (Real.log (Real.log t) + meisselMertensConstant) =
    deriv f t * primeReciprocalError t
  unfold primeReciprocalError
  ring

/-- The outer prime range in Chen's pair sum. -/
noncomputable def chenFirstPrimes (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ (x : ℝ) ^ (10 : ℝ)⁻¹ < (p : ℝ) ∧
      (p : ℝ) ≤ (x : ℝ) ^ (3 : ℝ)⁻¹

/-- The inner prime range after fixing the first prime. -/
noncomputable def chenSecondPrimes (x p : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun q =>
    q.Prime ∧ (x : ℝ) ^ (3 : ℝ)⁻¹ < (q : ℝ) ∧
      (q : ℝ) ≤ ((x : ℝ) / p) ^ (2 : ℝ)⁻¹

/-- Rewrite a sum over `chenPairs` as the two nested prime sums to which Abel
summation is applied. -/
theorem sum_chenPairs_eq_nested (x : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ q ∈ chenPairs x, F q =
      ∑ p ∈ chenFirstPrimes x,
        ∑ q ∈ chenSecondPrimes x p, F (p, q) := by
  unfold chenPairs chenFirstPrimes chenSecondPrimes
  simp only [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · by_cases hlo : (x : ℝ) ^ (10 : ℝ)⁻¹ < (p : ℝ)
    · by_cases hhi : (p : ℝ) ≤ (x : ℝ) ^ (3 : ℝ)⁻¹
      · simp [hprime, hlo, hhi]
      · simp [hprime, hlo, hhi]
    · simp [hprime, hlo]
  · simp [hprime]

/-- The outer filtered range is exactly the natural interval between the two
real power cutoffs. -/
theorem chenFirstPrimes_eq_Ioc {x : ℕ} (hx : 1 ≤ x) :
    chenFirstPrimes x =
      (Finset.Ioc ⌊(x : ℝ) ^ (10 : ℝ)⁻¹⌋₊
        ⌊(x : ℝ) ^ (3 : ℝ)⁻¹⌋₊).filter Nat.Prime := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlo0 : 0 ≤ (x : ℝ) ^ (10 : ℝ)⁻¹ := by positivity
  have hhi0 : 0 ≤ (x : ℝ) ^ (3 : ℝ)⁻¹ := by positivity
  have hhiX : (x : ℝ) ^ (3 : ℝ)⁻¹ ≤ (x : ℝ) :=
    Real.rpow_le_self_of_one_le hxR (by norm_num)
  ext p
  simp only [chenFirstPrimes, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨_hpx, hp, hlo, hhi⟩
    exact ⟨⟨(Nat.floor_lt hlo0).2 hlo,
      (Nat.le_floor_iff hhi0).2 hhi⟩, hp⟩
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    have hloR : (x : ℝ) ^ (10 : ℝ)⁻¹ < (p : ℝ) :=
      (Nat.floor_lt hlo0).1 hlo
    have hhiR : (p : ℝ) ≤ (x : ℝ) ^ (3 : ℝ)⁻¹ :=
      (Nat.le_floor_iff hhi0).1 hhi
    have hpx : p ≤ x := by exact_mod_cast hhiR.trans hhiX
    exact ⟨Nat.lt_succ_iff.mpr hpx, hp, hloR, hhiR⟩

/-- After fixing an admissible first prime, the inner filtered range is the
natural interval used by Abel summation. -/
theorem chenSecondPrimes_eq_Ioc {x p : ℕ} (hx : 1 ≤ x)
    (hp : p ∈ chenFirstPrimes x) :
    chenSecondPrimes x p =
      (Finset.Ioc ⌊(x : ℝ) ^ (3 : ℝ)⁻¹⌋₊
        ⌊((x : ℝ) / p) ^ (2 : ℝ)⁻¹⌋₊).filter Nat.Prime := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hp' := hp
  simp only [chenFirstPrimes, Finset.mem_filter, Finset.mem_range] at hp'
  rcases hp' with ⟨_hprange, hpprime, _hplo, hphi⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hhiX : (x : ℝ) ^ (3 : ℝ)⁻¹ ≤ (x : ℝ) :=
    Real.rpow_le_self_of_one_le hxR (by norm_num)
  have hpxR : (p : ℝ) ≤ x := hphi.trans hhiX
  have hbase1 : (1 : ℝ) ≤ (x : ℝ) / p :=
    (le_div_iff₀ hpR).2 (by simpa using hpxR)
  have hupperX : ((x : ℝ) / p) ^ (2 : ℝ)⁻¹ ≤ (x : ℝ) :=
    (Real.rpow_le_self_of_one_le hbase1 (by norm_num)).trans
      (div_le_self (by positivity) (by exact_mod_cast hpprime.one_le))
  have hlo0 : 0 ≤ (x : ℝ) ^ (3 : ℝ)⁻¹ := by positivity
  have hhi0 : 0 ≤ ((x : ℝ) / p) ^ (2 : ℝ)⁻¹ := by positivity
  ext q
  simp only [chenSecondPrimes, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨_hqx, hq, hlo, hhi⟩
    exact ⟨⟨(Nat.floor_lt hlo0).2 hlo,
      (Nat.le_floor_iff hhi0).2 hhi⟩, hq⟩
  · rintro ⟨⟨hlo, hhi⟩, hq⟩
    have hloR : (x : ℝ) ^ (3 : ℝ)⁻¹ < (q : ℝ) :=
      (Nat.floor_lt hlo0).1 hlo
    have hhiR : (q : ℝ) ≤ ((x : ℝ) / p) ^ (2 : ℝ)⁻¹ :=
      (Nat.le_floor_iff hhi0).1 hhi
    have hqx : q ≤ x := by exact_mod_cast hhiR.trans hupperX
    exact ⟨Nat.lt_succ_iff.mpr hqx, hq, hloR, hhiR⟩

/-- The smooth weight in the inner Abel summation, after the first prime has
been fixed. -/
noncomputable def innerAbelWeight (X s t : ℝ) : ℝ :=
  (Real.log (X / (s * t)))⁻¹

/-- Derivative of the inner Abel weight on the non-singular region relevant
to Chen's pair sum. -/
theorem hasDerivAt_innerAbelWeight
    {X s t : ℝ} (hX : 0 < X) (hs : 0 < s) (ht : 0 < t)
    (hst : s * t < X) :
    HasDerivAt (innerAbelWeight X s)
      (1 / (t * (Real.log (X / (s * t))) ^ 2)) t := by
  have hst0 : s * t ≠ 0 := (mul_pos hs ht).ne'
  have harg : 0 < X / (s * t) := div_pos hX (mul_pos hs ht)
  have harg1 : 1 < X / (s * t) :=
    (lt_div_iff₀ (mul_pos hs ht)).2 (by simpa using hst)
  have hlog : Real.log (X / (s * t)) ≠ 0 := (Real.log_pos harg1).ne'
  have hmul : HasDerivAt (fun u : ℝ => s * u) s t :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul s
  have hdiv : HasDerivAt (fun u : ℝ => X / (s * u))
      (-(X * s) / (s * t) ^ 2) t := by
    change HasDerivAt ((fun _ : ℝ => X) / fun u : ℝ => s * u)
      (-(X * s) / (s * t) ^ 2) t
    simpa only [zero_mul, zero_sub] using
      (hasDerivAt_const t X).div hmul hst0
  have hloginv := (hdiv.log harg.ne').inv hlog
  change HasDerivAt ((fun y => Real.log (X / (s * y)))⁻¹)
    (1 / (t * (Real.log (X / (s * t))) ^ 2)) t
  have heq : 1 / (t * (Real.log (X / (s * t))) ^ 2) =
      -(-(X * s) / (s * t) ^ 2 / (X / (s * t))) /
        Real.log (X / (s * t)) ^ 2 := by
    field_simp [hX.ne', hs.ne', ht.ne', hlog]
  rw [heq]
  exact hloginv

/-- The inner Abel interval is nonempty and starts to the right of `1`. -/
theorem innerAbel_interval_bounds {X s : ℝ} (hX : 1 < X)
    (hs : 0 < s) (hshi : s ≤ X ^ (3 : ℝ)⁻¹) :
    1 < X ^ (3 : ℝ)⁻¹ ∧
      X ^ (3 : ℝ)⁻¹ ≤ (X / s) ^ (2 : ℝ)⁻¹ := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hthird : 0 < (3 : ℝ)⁻¹ := by norm_num
  constructor
  · exact Real.one_lt_rpow hX hthird
  · have hlogX : 0 < Real.log X := Real.log_pos hX
    have hlogs : Real.log s ≤ (3 : ℝ)⁻¹ * Real.log X := by
      rw [← Real.log_rpow hX0]
      exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.2 hs)
        (Set.mem_Ioi.2 (Real.rpow_pos_of_pos hX0 _)) hshi
    have hbase : 0 < X / s := div_pos hX0 hs
    apply (Real.log_le_log_iff
      (Real.rpow_pos_of_pos hX0 _) (Real.rpow_pos_of_pos hbase _)).mp
    rw [Real.log_rpow hX0, Real.log_rpow hbase,
      Real.log_div hX0.ne' hs.ne']
    nlinarith

/-- Throughout the inner Abel interval, the logarithmic kernel stays away
from its singularity. -/
theorem innerAbel_mul_lt {X s t : ℝ} (hX : 1 < X)
    (hs : 0 < s) (hshi : s ≤ X ^ (3 : ℝ)⁻¹)
    (ht : t ≤ (X / s) ^ (2 : ℝ)⁻¹) :
    s * t < X := by
  have hthird1 : X ^ (3 : ℝ)⁻¹ < X :=
    Real.rpow_lt_self_of_one_lt hX (by norm_num)
  have hsX : s < X := hshi.trans_lt hthird1
  have hbase : 1 < X / s :=
    (lt_div_iff₀ hs).2 (by simpa [mul_comm] using hsX)
  have hsqrt : (X / s) ^ (2 : ℝ)⁻¹ < X / s :=
    Real.rpow_lt_self_of_one_lt hbase (by norm_num)
  calc
    s * t ≤ s * ((X / s) ^ (2 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left ht hs.le
    _ < s * (X / s) := mul_lt_mul_of_pos_left hsqrt hs
    _ = X := by field_simp [hs.ne']

/-- The first (inner) Abel summation in Lemma 8, with its Mertens error
displayed explicitly. -/
theorem inner_primeReciprocal_abel {X s : ℝ} (hX : 1 < X)
    (hs : 0 < s) (hshi : s ≤ X ^ (3 : ℝ)⁻¹) :
    ∑ q ∈ Finset.Ioc ⌊X ^ (3 : ℝ)⁻¹⌋₊
        ⌊(X / s) ^ (2 : ℝ)⁻¹⌋₊ with Nat.Prime q,
        innerAbelWeight X s q * (q : ℝ)⁻¹ =
      (∫ t in Set.Ioc (X ^ (3 : ℝ)⁻¹) ((X / s) ^ (2 : ℝ)⁻¹),
        innerAbelWeight X s t / (t * Real.log t)) +
      innerAbelWeight X s ((X / s) ^ (2 : ℝ)⁻¹) *
        primeReciprocalError ((X / s) ^ (2 : ℝ)⁻¹) -
      innerAbelWeight X s (X ^ (3 : ℝ)⁻¹) *
        primeReciprocalError (X ^ (3 : ℝ)⁻¹) -
      ∫ t in Set.Ioc (X ^ (3 : ℝ)⁻¹) ((X / s) ^ (2 : ℝ)⁻¹),
        (1 / (t * (Real.log (X / (s * t))) ^ 2)) *
          primeReciprocalError t := by
  let a : ℝ := X ^ (3 : ℝ)⁻¹
  let b : ℝ := (X / s) ^ (2 : ℝ)⁻¹
  have hbds := innerAbel_interval_bounds hX hs hshi
  have ha : 1 < a := hbds.1
  have hab : a ≤ b := hbds.2
  have hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt (innerAbelWeight X s)
        (1 / (t * (Real.log (X / (s * t))) ^ 2)) t := by
    intro t ht
    exact hasDerivAt_innerAbelWeight (zero_lt_one.trans hX) hs
      (zero_lt_one.trans (ha.trans_le ht.1))
      (innerAbel_mul_lt hX hs hshi ht.2)
  have hformula_cont : ContinuousOn (fun t : ℝ =>
      1 / (t * (Real.log (X / (s * t))) ^ 2)) (Set.Icc a b) := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans (ha.trans_le ht.1)
    have hst : s * t < X := innerAbel_mul_lt hX hs hshi ht.2
    have harg1 : 1 < X / (s * t) :=
      (lt_div_iff₀ (mul_pos hs ht0)).2 (by simpa using hst)
    have hlog0 : Real.log (X / (s * t)) ≠ 0 :=
      (Real.log_pos harg1).ne'
    have hden : t * (Real.log (X / (s * t))) ^ 2 ≠ 0 :=
      mul_ne_zero ht0.ne' (pow_ne_zero _ hlog0)
    have hmul : ContinuousWithinAt (fun u : ℝ => s * u)
        (Set.Icc a b) t :=
      continuousWithinAt_const.mul continuousWithinAt_id
    have hquot : ContinuousWithinAt (fun u : ℝ => X / (s * u))
        (Set.Icc a b) t :=
      continuousWithinAt_const.div hmul (mul_ne_zero hs.ne' ht0.ne')
    have hlog : ContinuousWithinAt
        (fun u : ℝ => Real.log (X / (s * u))) (Set.Icc a b) t :=
      hquot.log (ne_of_gt (div_pos (zero_lt_one.trans hX) (mul_pos hs ht0)))
    exact continuousWithinAt_const.div
      (continuousWithinAt_id.mul (hlog.pow 2)) hden
  have hf_int : MeasureTheory.IntegrableOn
      (deriv (innerAbelWeight X s)) (Set.Icc a b) := by
    apply (hformula_cont.integrableOn_Icc).congr_fun _ measurableSet_Icc
    intro t ht
    exact (hderiv t ht).deriv.symm
  have h := primeReciprocal_abel_decomposition_auto ha hab
    (innerAbelWeight X s) (fun t ht => (hderiv t ht).differentiableAt) hf_int
  dsimp only [a, b] at h ⊢
  rw [h]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  rw [(hderiv t ⟨ht.1.le, ht.2⟩).deriv]

/-- The normalized inner density after the change of variables
`β = log t / log X`. -/
noncomputable def normalizedInnerKernel (α β : ℝ) : ℝ :=
  1 / (β * (1 - α - β))

private noncomputable def normalizedInnerAntideriv (α β : ℝ) : ℝ :=
  (Real.log β - Real.log (1 - α - β)) / (1 - α)

private theorem hasDerivAt_normalizedInnerAntideriv
    {α β : ℝ} (_hα : α < 1) (hβ : 0 < β)
    (hgap : 0 < 1 - α - β) :
    HasDerivAt (normalizedInnerAntideriv α)
      (normalizedInnerKernel α β) β := by
  have hc : 1 - α ≠ 0 := by linarith
  have hgap_deriv : HasDerivAt (fun u : ℝ => 1 - α - u) (-1) β := by
    convert! (hasDerivAt_id β).const_sub (1 - α) using 1
  have hnum : HasDerivAt
      (fun u : ℝ => Real.log u - Real.log (1 - α - u))
      (1 / β - (-1) / (1 - α - β)) β := by
    have h := (Real.hasDerivAt_log hβ.ne').sub
      (hgap_deriv.log hgap.ne')
    convert! h using 1
    rw [one_div]
  unfold normalizedInnerAntideriv normalizedInnerKernel
  have heq : (1 / β - (-1) / (1 - α - β)) / (1 - α) =
      1 / (β * (1 - α - β)) := by
    field_simp [hc, hβ.ne', hgap.ne']
    ring
  rw [← heq]
  simpa only using hnum.div_const (1 - α)

/-- Evaluation of the normalized inner integral. -/
theorem normalized_inner_integral
    {α : ℝ} (hαlo : 1 / 10 ≤ α) (hαhi : α ≤ 1 / 3) :
    (∫ β : ℝ in (1 / 3)..((1 - α) / 2),
      normalizedInnerKernel α β) =
      Real.log (2 - 3 * α) / (1 - α) := by
  have hab : (1 / 3 : ℝ) ≤ (1 - α) / 2 := by linarith
  have hα1 : α < 1 := by linarith
  have hderiv : ∀ β ∈ Set.uIcc (1 / 3 : ℝ) ((1 - α) / 2),
      HasDerivAt (normalizedInnerAntideriv α)
        (normalizedInnerKernel α β) β := by
    rw [Set.uIcc_of_le hab]
    intro β hβ
    apply hasDerivAt_normalizedInnerAntideriv hα1
    · linarith [hβ.1]
    · linarith [hβ.2]
  have hint : IntervalIntegrable (normalizedInnerKernel α)
      MeasureTheory.volume (1 / 3) ((1 - α) / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro β hβ
    have hβ0 : β ≠ 0 := by linarith [hβ.1]
    have hgap0 : 1 - α - β ≠ 0 := by linarith [hβ.2]
    unfold normalizedInnerKernel
    exact continuousWithinAt_const.div
      (continuousWithinAt_id.mul
        (continuousWithinAt_id.const_sub (1 - α)))
      (mul_ne_zero hβ0 hgap0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hc : 1 - α ≠ 0 := by linarith
  have harg : 0 < 2 - 3 * α := by linarith
  unfold normalizedInnerAntideriv
  have hupper : (1 - α - (1 - α) / 2) = (1 - α) / 2 := by ring
  rw [hupper, sub_self, zero_div, zero_sub]
  have hgap : 1 - α - (1 / 3 : ℝ) = (2 - 3 * α) / 3 := by ring
  rw [hgap, Real.log_div harg.ne' (by norm_num : (3 : ℝ) ≠ 0),
    show (1 / 3 : ℝ) = 1 / 3 by rfl,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_one]
  field_simp [hc]
  ring

/-- Logarithmic coordinate normalized by `log X`. -/
noncomputable def normalizedLog (X t : ℝ) : ℝ :=
  Real.log t / Real.log X

/-- The outer weight obtained by evaluating the inner main integral. -/
noncomputable def outerAbelWeight (X s : ℝ) : ℝ :=
  Real.log (2 - 3 * normalizedLog X s) /
    ((1 - normalizedLog X s) * Real.log X)

/-- Identification of the inner main integral with the closed-form outer
weight. -/
theorem inner_main_integral_eq_outerAbelWeight
    {X s : ℝ} (hX : 1 < X) (hs : 0 < s)
    (hslo : X ^ (10 : ℝ)⁻¹ ≤ s)
    (hshi : s ≤ X ^ (3 : ℝ)⁻¹) :
    (∫ t in Set.Ioc (X ^ (3 : ℝ)⁻¹) ((X / s) ^ (2 : ℝ)⁻¹),
      innerAbelWeight X s t / (t * Real.log t)) =
      outerAbelWeight X s := by
  let a : ℝ := X ^ (3 : ℝ)⁻¹
  let b : ℝ := (X / s) ^ (2 : ℝ)⁻¹
  let L : ℝ := Real.log X
  let α : ℝ := normalizedLog X s
  let φ : ℝ → ℝ := normalizedLog X
  let φ' : ℝ → ℝ := fun t => 1 / (t * L)
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < L := Real.log_pos hX
  have hlogX0 : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hbds := innerAbel_interval_bounds hX hs hshi
  have ha : 1 < a := hbds.1
  have hab : a ≤ b := hbds.2
  have hφderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans (ha.trans_le ht.1)
    dsimp only [φ, φ', normalizedLog, L]
    convert! (Real.hasDerivAt_log ht0.ne').div_const (Real.log X) using 1
    field_simp [hlogX0, ht0.ne']
  have hφcont : ContinuousOn φ [[a, b]] :=
    HasDerivAt.continuousOn hφderiv
  have hφderiv_open : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt φ (φ' t) t := by
    intro t ht
    exact hφderiv t (Set.Ioo_subset_Icc_self ht)
  have hφ'nonneg : ∀ t ∈ Set.Ioo (min a b) (max a b), 0 ≤ φ' t := by
    intro t ht
    have ht0 : 0 < t := by
      rw [min_eq_left hab] at ht
      exact zero_lt_one.trans (ha.trans ht.1)
    dsimp only [φ', L]
    positivity
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := a) (b := b) (f := φ) (f' := φ')
    (g := normalizedInnerKernel α) hφcont hφderiv_open hφ'nonneg
  have hφa : φ a = 1 / 3 := by
    dsimp only [φ, a, normalizedLog]
    rw [Real.log_rpow hX0]
    field_simp [hlogX0]
  have hφb : φ b = (1 - α) / 2 := by
    dsimp only [φ, b, α, normalizedLog]
    have hbase : 0 < X / s := div_pos hX0 hs
    rw [Real.log_rpow hbase, Real.log_div hX0.ne' hs.ne']
    field_simp [hlogX0]
  rw [hφa, hφb] at hsubst
  have hαlo : 1 / 10 ≤ α := by
    dsimp only [α, normalizedLog]
    have hlogs : (10 : ℝ)⁻¹ * Real.log X ≤ Real.log s := by
      rw [← Real.log_rpow hX0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hslo
    exact (le_div_iff₀ hL).2 (by nlinarith)
  have hαhi : α ≤ 1 / 3 := by
    dsimp only [α, normalizedLog]
    have hlogs : Real.log s ≤ (3 : ℝ)⁻¹ * Real.log X := by
      rw [← Real.log_rpow hX0]
      exact Real.log_le_log hs hshi
    exact (div_le_iff₀ hL).2 (by nlinarith)
  have hnorm := normalized_inner_integral hαlo hαhi
  have h1α : 1 - α ≠ 0 := by linarith
  have houter : outerAbelWeight X s =
      (Real.log (2 - 3 * α) / (1 - α)) / L := by
    unfold outerAbelWeight
    dsimp only [α, L]
    field_simp [hlogX0, h1α]
  rw [houter]
  rw [← intervalIntegral.integral_of_le hab]
  change (∫ t in a..b, innerAbelWeight X s t / (t * Real.log t)) =
    (Real.log (2 - 3 * α) / (1 - α)) / L
  rw [← hnorm, ← hsubst, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : 0 < t := zero_lt_one.trans (ha.trans_le ht.1)
  have hst : s * t < X := innerAbel_mul_lt hX hs hshi ht.2
  have hlogt : Real.log t ≠ 0 := (Real.log_pos (ha.trans_le ht.1)).ne'
  have hlogarg : Real.log (X / (s * t)) ≠ 0 :=
    (Real.log_pos ((lt_div_iff₀ (mul_pos hs ht0)).2 (by simpa using hst))).ne'
  simp only [Function.comp_apply]
  dsimp only [innerAbelWeight, normalizedInnerKernel, φ, φ', α,
    normalizedLog, L]
  rw [Real.log_div hX0.ne' (mul_ne_zero hs.ne' ht0.ne'),
    Real.log_mul hs.ne' ht0.ne']
  field_simp [hL.ne', hlogX0, ht0.ne', hlogt, hlogarg]
  ring

/-- The inner Abel sum is bounded by its main outer weight plus a uniform
Mertens-error term. -/
theorem inner_primeReciprocal_abel_le
    {X s ε : ℝ} (hX : 1 < X) (hs : 0 < s)
    (hslo : X ^ (10 : ℝ)⁻¹ ≤ s)
    (hshi : s ≤ X ^ (3 : ℝ)⁻¹) (hε : 0 ≤ ε)
    (hE : ∀ t ∈ Set.Icc (X ^ (3 : ℝ)⁻¹) ((X / s) ^ (2 : ℝ)⁻¹),
      |primeReciprocalError t| ≤ ε) :
    ∑ q ∈ Finset.Ioc ⌊X ^ (3 : ℝ)⁻¹⌋₊
        ⌊(X / s) ^ (2 : ℝ)⁻¹⌋₊ with Nat.Prime q,
        innerAbelWeight X s q * (q : ℝ)⁻¹ ≤
      outerAbelWeight X s +
        2 * ε * innerAbelWeight X s ((X / s) ^ (2 : ℝ)⁻¹) := by
  let a : ℝ := X ^ (3 : ℝ)⁻¹
  let b : ℝ := (X / s) ^ (2 : ℝ)⁻¹
  let f : ℝ → ℝ := innerAbelWeight X s
  let d : ℝ → ℝ := fun t =>
    1 / (t * (Real.log (X / (s * t))) ^ 2)
  have hbds := innerAbel_interval_bounds hX hs hshi
  have ha : 1 < a := hbds.1
  have hab : a ≤ b := hbds.2
  have hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t := by
    intro t ht
    exact hasDerivAt_innerAbelWeight (zero_lt_one.trans hX) hs
      (zero_lt_one.trans (ha.trans_le ht.1))
      (innerAbel_mul_lt hX hs hshi ht.2)
  have hd_cont : ContinuousOn d (Set.Icc a b) := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans (ha.trans_le ht.1)
    have hst : s * t < X := innerAbel_mul_lt hX hs hshi ht.2
    have harg1 : 1 < X / (s * t) :=
      (lt_div_iff₀ (mul_pos hs ht0)).2 (by simpa using hst)
    have hlog0 : Real.log (X / (s * t)) ≠ 0 := (Real.log_pos harg1).ne'
    have hden : t * (Real.log (X / (s * t))) ^ 2 ≠ 0 :=
      mul_ne_zero ht0.ne' (pow_ne_zero _ hlog0)
    have hmul : ContinuousWithinAt (fun u : ℝ => s * u)
        (Set.Icc a b) t := continuousWithinAt_const.mul continuousWithinAt_id
    have hquot : ContinuousWithinAt (fun u : ℝ => X / (s * u))
        (Set.Icc a b) t :=
      continuousWithinAt_const.div hmul (mul_ne_zero hs.ne' ht0.ne')
    have hlog : ContinuousWithinAt (fun u : ℝ => Real.log (X / (s * u)))
        (Set.Icc a b) t := hquot.log
      (ne_of_gt (div_pos (zero_lt_one.trans hX) (mul_pos hs ht0)))
    dsimp only [d]
    exact continuousWithinAt_const.div
      (continuousWithinAt_id.mul (hlog.pow 2)) hden
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b) := by
    apply hd_cont.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hd t ht).deriv.symm
  have hf'_int : MeasureTheory.IntegrableOn (deriv f) (Set.Ioc a b) :=
    hf_int.mono_set Set.Ioc_subset_Icc_self
  have hprod := integrableOn_deriv_mul_primeReciprocalError ha f hf_int
  have hnonneg : ∀ t ∈ Set.Ioc a b, 0 ≤ deriv f t := by
    intro t ht
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    dsimp only [d]
    exact one_div_nonneg.mpr
      (mul_nonneg (zero_lt_one.trans (ha.trans ht.1)).le (sq_nonneg _))
  have hfa : 0 ≤ f a := by
    have ha0 : 0 < a := zero_lt_one.trans ha
    have hst := innerAbel_mul_lt hX hs hshi hab
    unfold f innerAbelWeight
    exact inv_nonneg.2 (Real.log_pos
      ((lt_div_iff₀ (mul_pos hs ha0)).2 (by simpa using hst))).le
  have hfb : 0 ≤ f b := by
    have hb0 : 0 < b := zero_lt_one.trans (ha.trans_le hab)
    have hst := innerAbel_mul_lt hX hs hshi le_rfl
    unfold f innerAbelWeight
    exact inv_nonneg.2 (Real.log_pos
      ((lt_div_iff₀ (mul_pos hs hb0)).2 (by simpa using hst))).le
  have hderiv_actual : ∀ t ∈ Set.uIcc a b,
      HasDerivAt f (deriv f t) t := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have hdt := hd t ht
    rw [hdt.deriv]
    exact hdt
  have hinter : IntervalIntegrable (deriv f) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hf_int
  have hFTCinterval := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv_actual hinter
  have hFTC : (∫ t in Set.Ioc a b, deriv f t) = f b - f a := by
    rw [← intervalIntegral.integral_of_le hab]
    exact hFTCinterval
  have herr := abel_error_le_of_nonneg_deriv hab hε
    (by simpa only [a, b] using hE) hfa hfb hnonneg hf'_int hprod hFTC
  have hinter_eq :
      (∫ t in Set.Ioc a b, d t * primeReciprocalError t) =
        ∫ t in Set.Ioc a b, deriv f t * primeReciprocalError t := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
  have hexact := inner_primeReciprocal_abel hX hs hshi
  rw [inner_main_integral_eq_outerAbelWeight hX hs hslo hshi] at hexact
  dsimp only [a, b, f, d] at herr hinter_eq
  rw [hexact, hinter_eq]
  linarith

/-- The normalized outer weight in equation (24). -/
noncomputable def normalizedOuterWeight (α : ℝ) : ℝ :=
  Real.log (2 - 3 * α) / (1 - α)

noncomputable def normalizedOuterWeightDeriv (α : ℝ) : ℝ :=
  (Real.log (2 - 3 * α) - 3 * (1 - α) / (2 - 3 * α)) /
    (1 - α) ^ 2

theorem hasDerivAt_normalizedOuterWeight
    {α : ℝ} (hα : α < 1) (harg : 0 < 2 - 3 * α) :
    HasDerivAt normalizedOuterWeight (normalizedOuterWeightDeriv α) α := by
  have hden : 1 - α ≠ 0 := by linarith
  have hlin : HasDerivAt (fun u : ℝ => 2 - 3 * u) (-3) α := by
    convert! ((hasDerivAt_id α).const_mul 3).const_sub 2 using 1
    norm_num
  have hlog := hlin.log harg.ne'
  have hbot : HasDerivAt (fun u : ℝ => 1 - u) (-1) α := by
    convert! (hasDerivAt_id α).const_sub 1 using 1
  unfold normalizedOuterWeight normalizedOuterWeightDeriv
  convert! hlog.div hbot hden using 1
  field_simp [hden, harg.ne']
  ring

theorem normalizedOuterWeightDeriv_nonpos
    {α : ℝ} (hα0 : 0 ≤ α) (hαhi : α ≤ 1 / 3) :
    normalizedOuterWeightDeriv α ≤ 0 := by
  have harg : 0 < 2 - 3 * α := by linarith
  have hlog := Real.log_le_sub_one_of_pos harg
  have hquad : 0 ≤ α * (1 / 3 - α) := mul_nonneg hα0 (by linarith)
  have hrat : (2 - 3 * α) - 1 ≤ 3 * (1 - α) / (2 - 3 * α) := by
    apply (le_div_iff₀ harg).2
    nlinarith
  have hnum : Real.log (2 - 3 * α) -
      3 * (1 - α) / (2 - 3 * α) ≤ 0 := by linarith
  unfold normalizedOuterWeightDeriv
  exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)

/-- Derivative of the outer Abel weight. -/
theorem hasDerivAt_outerAbelWeight
    {X s : ℝ} (hX : 1 < X) (hs : 0 < s)
    (_hαlo : 1 / 10 ≤ normalizedLog X s)
    (hαhi : normalizedLog X s ≤ 1 / 3) :
    HasDerivAt (outerAbelWeight X)
      (normalizedOuterWeightDeriv (normalizedLog X s) /
        (s * (Real.log X) ^ 2)) s := by
  have hL : 0 < Real.log X := Real.log_pos hX
  have hα1 : normalizedLog X s < 1 := by linarith
  have harg : 0 < 2 - 3 * normalizedLog X s := by linarith
  have hφ : HasDerivAt (normalizedLog X) (1 / (s * Real.log X)) s := by
    unfold normalizedLog
    convert! (Real.hasDerivAt_log hs.ne').div_const (Real.log X) using 1
    field_simp [hs.ne', hL.ne']
  have hw := (hasDerivAt_normalizedOuterWeight hα1 harg).scomp s hφ
  have hscaled := hw.div_const (Real.log X)
  have hfun : outerAbelWeight X = fun y =>
      (normalizedOuterWeight ∘ normalizedLog X) y / Real.log X := by
    funext y
    unfold outerAbelWeight normalizedOuterWeight
    simp only [Function.comp_apply, div_eq_mul_inv, mul_inv]
    ring
  have hderiv_eq : normalizedOuterWeightDeriv (normalizedLog X s) /
        (s * (Real.log X) ^ 2) =
      (1 / (s * Real.log X)) * normalizedOuterWeightDeriv (normalizedLog X s) /
        Real.log X := by
    field_simp [hs.ne', hL.ne']
  rw [hfun, hderiv_eq]
  simpa only [smul_eq_mul] using hscaled

theorem outerAbelWeight_deriv_nonpos
    {X s : ℝ} (hX : 1 < X) (hs : 0 < s)
    (hαlo : 1 / 10 ≤ normalizedLog X s)
    (hαhi : normalizedLog X s ≤ 1 / 3) :
    deriv (outerAbelWeight X) s ≤ 0 := by
  rw [(hasDerivAt_outerAbelWeight hX hs hαlo hαhi).deriv]
  exact div_nonpos_of_nonpos_of_nonneg
    (normalizedOuterWeightDeriv_nonpos (by linarith) hαhi)
    (mul_nonneg hs.le (sq_nonneg _))

/-- The outer main integral is exactly equation (24), with the expected
factor `1 / log X`. -/
theorem outer_main_integral_eq_equation24
    {X : ℝ} (hX : 1 < X) :
    (∫ s in Set.Ioc (X ^ (10 : ℝ)⁻¹) (X ^ (3 : ℝ)⁻¹),
      outerAbelWeight X s / (s * Real.log s)) =
      equation24Integral / Real.log X := by
  let a : ℝ := X ^ (10 : ℝ)⁻¹
  let b : ℝ := X ^ (3 : ℝ)⁻¹
  let L : ℝ := Real.log X
  let φ : ℝ → ℝ := normalizedLog X
  let φ' : ℝ → ℝ := fun s => 1 / (s * L)
  let g : ℝ → ℝ := fun α =>
    Real.log (2 - 3 * α) / (α * (1 - α))
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < L := Real.log_pos hX
  have hlogX0 : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have ha1 : 1 < a := Real.one_lt_rpow hX (by norm_num)
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hφderiv : ∀ s ∈ Set.uIcc a b, HasDerivAt φ (φ' s) s := by
    rw [Set.uIcc_of_le hab]
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
    dsimp only [φ, φ', normalizedLog, L]
    convert! (Real.hasDerivAt_log hs0.ne').div_const (Real.log X) using 1
    field_simp [hs0.ne', hL.ne']
  have hφcont : ContinuousOn φ [[a, b]] := HasDerivAt.continuousOn hφderiv
  have hφopen : ∀ s ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt φ (φ' s) s := fun s hs =>
    hφderiv s (Set.Ioo_subset_Icc_self hs)
  have hφnonneg : ∀ s ∈ Set.Ioo (min a b) (max a b), 0 ≤ φ' s := by
    intro s hs
    have hs0 : 0 < s := by
      rw [min_eq_left hab] at hs
      exact zero_lt_one.trans (ha1.trans hs.1)
    dsimp only [φ', L]
    positivity
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := a) (b := b) (f := φ) (f' := φ') (g := g)
    hφcont hφopen hφnonneg
  have hφa : φ a = 1 / 10 := by
    dsimp only [φ, a, normalizedLog]
    rw [Real.log_rpow hX0]
    field_simp [hlogX0]
  have hφb : φ b = 1 / 3 := by
    dsimp only [φ, b, normalizedLog]
    rw [Real.log_rpow hX0]
    field_simp [hlogX0]
  rw [hφa, hφb] at hsubst
  rw [← intervalIntegral.integral_of_le hab]
  unfold equation24Integral
  change (∫ s in a..b, outerAbelWeight X s / (s * Real.log s)) =
    (∫ α in (1 / 10)..(1 / 3), g α) / L
  rw [← hsubst, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
  have hlogs : Real.log s ≠ 0 :=
    (Real.log_pos (ha1.trans_le hs.1)).ne'
  have hαlo : 1 / 10 ≤ normalizedLog X s := by
    have hlogslo : (10 : ℝ)⁻¹ * Real.log X ≤ Real.log s := by
      rw [← Real.log_rpow hX0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hs.1
    unfold normalizedLog
    exact (le_div_iff₀ hL).2 (by nlinarith)
  have hαhi : normalizedLog X s ≤ 1 / 3 := by
    have hlogshi : Real.log s ≤ (3 : ℝ)⁻¹ * Real.log X := by
      rw [← Real.log_rpow hX0]
      exact Real.log_le_log hs0 hs.2
    unfold normalizedLog
    exact (div_le_iff₀ hL).2 (by nlinarith)
  have hα0 : normalizedLog X s ≠ 0 := by linarith
  have h1α : 1 - normalizedLog X s ≠ 0 := by linarith
  simp only [Function.comp_apply]
  dsimp only [outerAbelWeight, normalizedLog, φ, φ', g, L]
  field_simp [hs0.ne', hL.ne', hlogs, hα0, h1α]

/-- The second (outer) Abel summation in Lemma 8, with its Mertens error
displayed explicitly and its main term identified with equation (24). -/
theorem outer_primeReciprocal_abel {X : ℝ} (hX : 1 < X) :
    ∑ p ∈ Finset.Ioc ⌊X ^ (10 : ℝ)⁻¹⌋₊
        ⌊X ^ (3 : ℝ)⁻¹⌋₊ with Nat.Prime p,
        outerAbelWeight X p * (p : ℝ)⁻¹ =
      equation24Integral / Real.log X +
      outerAbelWeight X (X ^ (3 : ℝ)⁻¹) *
        primeReciprocalError (X ^ (3 : ℝ)⁻¹) -
      outerAbelWeight X (X ^ (10 : ℝ)⁻¹) *
        primeReciprocalError (X ^ (10 : ℝ)⁻¹) -
      ∫ s in Set.Ioc (X ^ (10 : ℝ)⁻¹) (X ^ (3 : ℝ)⁻¹),
        deriv (outerAbelWeight X) s * primeReciprocalError s := by
  let a : ℝ := X ^ (10 : ℝ)⁻¹
  let b : ℝ := X ^ (3 : ℝ)⁻¹
  let d : ℝ → ℝ := fun s =>
    normalizedOuterWeightDeriv (normalizedLog X s) /
      (s * (Real.log X) ^ 2)
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have ha1 : 1 < a := Real.one_lt_rpow hX (by norm_num)
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hαbounds : ∀ s ∈ Set.Icc a b,
      1 / 10 ≤ normalizedLog X s ∧ normalizedLog X s ≤ 1 / 3 := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
    constructor
    · have hlogs : (10 : ℝ)⁻¹ * Real.log X ≤ Real.log s := by
        rw [← Real.log_rpow hX0]
        exact Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hs.1
      unfold normalizedLog
      exact (le_div_iff₀ hL).2 (by nlinarith)
    · have hlogs : Real.log s ≤ (3 : ℝ)⁻¹ * Real.log X := by
        rw [← Real.log_rpow hX0]
        exact Real.log_le_log hs0 hs.2
      unfold normalizedLog
      exact (div_le_iff₀ hL).2 (by nlinarith)
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (outerAbelWeight X) (d s) s := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
    exact hasDerivAt_outerAbelWeight hX hs0
      (hαbounds s hs).1 (hαbounds s hs).2
  have hd_cont : ContinuousOn d (Set.Icc a b) := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
    have hα := hαbounds s hs
    have harg : 0 < 2 - 3 * normalizedLog X s := by linarith
    have h1α : 1 - normalizedLog X s ≠ 0 := by linarith
    have hden : s * (Real.log X) ^ 2 ≠ 0 :=
      mul_ne_zero hs0.ne' (pow_ne_zero _ hL.ne')
    have hαcont : ContinuousWithinAt (normalizedLog X) (Set.Icc a b) s := by
      unfold normalizedLog
      exact (Real.continuousAt_log hs0.ne').continuousWithinAt.div_const
        (Real.log X)
    have hargcont : ContinuousWithinAt
        (fun u => 2 - 3 * normalizedLog X u) (Set.Icc a b) s :=
      (hαcont.const_mul 3).const_sub 2
    have honecont : ContinuousWithinAt
        (fun u => 1 - normalizedLog X u) (Set.Icc a b) s :=
      hαcont.const_sub 1
    have hnumcont : ContinuousWithinAt (fun u =>
        Real.log (2 - 3 * normalizedLog X u) -
          3 * (1 - normalizedLog X u) / (2 - 3 * normalizedLog X u))
        (Set.Icc a b) s :=
      (hargcont.log harg.ne').sub
        ((continuousWithinAt_const.mul honecont).div hargcont harg.ne')
    dsimp only [d, normalizedOuterWeightDeriv]
    exact (hnumcont.div (honecont.pow 2) (pow_ne_zero _ h1α)).div
      (continuousWithinAt_id.mul (continuousWithinAt_const.pow 2)) hden
  have hf_int : MeasureTheory.IntegrableOn
      (deriv (outerAbelWeight X)) (Set.Icc a b) := by
    apply hd_cont.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro s hs
    exact (hderiv s hs).deriv.symm
  have h := primeReciprocal_abel_decomposition_auto ha1 hab
    (outerAbelWeight X) (fun s hs => (hderiv s hs).differentiableAt) hf_int
  rw [outer_main_integral_eq_equation24 hX] at h
  dsimp only [a, b] at h ⊢
  exact h

theorem outerAbelWeight_nonneg
    {X s : ℝ} (hX : 1 < X) (_hs : 0 < s)
    (_hαlo : 1 / 10 ≤ normalizedLog X s)
    (hαhi : normalizedLog X s ≤ 1 / 3) :
    0 ≤ outerAbelWeight X s := by
  have hL : 0 < Real.log X := Real.log_pos hX
  have hlog : 0 ≤ Real.log (2 - 3 * normalizedLog X s) :=
    Real.log_nonneg (by linarith)
  unfold outerAbelWeight
  exact div_nonneg hlog (mul_nonneg (by linarith) hL.le)

/-- The outer Abel sum is bounded by equation (24) plus its uniform Mertens
error. -/
theorem outer_primeReciprocal_abel_le
    {X ε : ℝ} (hX : 1 < X) (hε : 0 ≤ ε)
    (hE : ∀ s ∈ Set.Icc (X ^ (10 : ℝ)⁻¹) (X ^ (3 : ℝ)⁻¹),
      |primeReciprocalError s| ≤ ε) :
    ∑ p ∈ Finset.Ioc ⌊X ^ (10 : ℝ)⁻¹⌋₊
        ⌊X ^ (3 : ℝ)⁻¹⌋₊ with Nat.Prime p,
        outerAbelWeight X p * (p : ℝ)⁻¹ ≤
      equation24Integral / Real.log X +
        2 * ε * outerAbelWeight X (X ^ (10 : ℝ)⁻¹) := by
  let a : ℝ := X ^ (10 : ℝ)⁻¹
  let b : ℝ := X ^ (3 : ℝ)⁻¹
  let f : ℝ → ℝ := outerAbelWeight X
  let d : ℝ → ℝ := fun s =>
    normalizedOuterWeightDeriv (normalizedLog X s) /
      (s * (Real.log X) ^ 2)
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have ha1 : 1 < a := Real.one_lt_rpow hX (by norm_num)
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hαbounds : ∀ s ∈ Set.Icc a b,
      1 / 10 ≤ normalizedLog X s ∧ normalizedLog X s ≤ 1 / 3 := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
    constructor
    · have hlogs : (10 : ℝ)⁻¹ * Real.log X ≤ Real.log s := by
        rw [← Real.log_rpow hX0]
        exact Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hs.1
      unfold normalizedLog
      exact (le_div_iff₀ hL).2 (by nlinarith)
    · have hlogs : Real.log s ≤ (3 : ℝ)⁻¹ * Real.log X := by
        rw [← Real.log_rpow hX0]
        exact Real.log_le_log hs0 hs.2
      unfold normalizedLog
      exact (div_le_iff₀ hL).2 (by nlinarith)
  have hd : ∀ s ∈ Set.Icc a b, HasDerivAt f (d s) s := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
    exact hasDerivAt_outerAbelWeight hX hs0
      (hαbounds s hs).1 (hαbounds s hs).2
  have hd_cont : ContinuousOn d (Set.Icc a b) := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans_le hs.1)
    have hα := hαbounds s hs
    have harg : 0 < 2 - 3 * normalizedLog X s := by linarith
    have h1α : 1 - normalizedLog X s ≠ 0 := by linarith
    have hden : s * (Real.log X) ^ 2 ≠ 0 :=
      mul_ne_zero hs0.ne' (pow_ne_zero _ hL.ne')
    have hαcont : ContinuousWithinAt (normalizedLog X) (Set.Icc a b) s := by
      unfold normalizedLog
      exact (Real.continuousAt_log hs0.ne').continuousWithinAt.div_const
        (Real.log X)
    have hargcont : ContinuousWithinAt
        (fun u => 2 - 3 * normalizedLog X u) (Set.Icc a b) s :=
      (hαcont.const_mul 3).const_sub 2
    have honecont : ContinuousWithinAt
        (fun u => 1 - normalizedLog X u) (Set.Icc a b) s :=
      hαcont.const_sub 1
    have hnumcont : ContinuousWithinAt (fun u =>
        Real.log (2 - 3 * normalizedLog X u) -
          3 * (1 - normalizedLog X u) / (2 - 3 * normalizedLog X u))
        (Set.Icc a b) s :=
      (hargcont.log harg.ne').sub
        ((continuousWithinAt_const.mul honecont).div hargcont harg.ne')
    dsimp only [d, normalizedOuterWeightDeriv]
    exact (hnumcont.div (honecont.pow 2) (pow_ne_zero _ h1α)).div
      (continuousWithinAt_id.mul (continuousWithinAt_const.pow 2)) hden
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b) := by
    apply hd_cont.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro s hs
    exact (hd s hs).deriv.symm
  have hf'_int : MeasureTheory.IntegrableOn (deriv f) (Set.Ioc a b) :=
    hf_int.mono_set Set.Ioc_subset_Icc_self
  have hprod := integrableOn_deriv_mul_primeReciprocalError ha1 f hf_int
  have hnonpos : ∀ s ∈ Set.Ioc a b, deriv f s ≤ 0 := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans (ha1.trans hs.1)
    unfold f
    exact outerAbelWeight_deriv_nonpos hX hs0
      (hαbounds s ⟨hs.1.le, hs.2⟩).1
      (hαbounds s ⟨hs.1.le, hs.2⟩).2
  have hfa : 0 ≤ f a := by
    unfold f
    exact outerAbelWeight_nonneg hX (zero_lt_one.trans ha1)
      (hαbounds a ⟨le_rfl, hab⟩).1 (hαbounds a ⟨le_rfl, hab⟩).2
  have hfb : 0 ≤ f b := by
    unfold f
    exact outerAbelWeight_nonneg hX
      (zero_lt_one.trans (ha1.trans_le hab))
      (hαbounds b ⟨hab, le_rfl⟩).1 (hαbounds b ⟨hab, le_rfl⟩).2
  have hderiv_actual : ∀ s ∈ Set.uIcc a b,
      HasDerivAt f (deriv f s) s := by
    rw [Set.uIcc_of_le hab]
    intro s hs
    have hds := hd s hs
    rw [hds.deriv]
    exact hds
  have hinter : IntervalIntegrable (deriv f) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hf_int
  have hFTCinterval := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv_actual hinter
  have hFTC : (∫ s in Set.Ioc a b, deriv f s) = f b - f a := by
    rw [← intervalIntegral.integral_of_le hab]
    exact hFTCinterval
  have herr := abel_error_le_of_nonpos_deriv hab hε
    (by simpa only [a, b] using hE) hfa hfb hnonpos hf'_int hprod hFTC
  have hexact := outer_primeReciprocal_abel hX
  dsimp only [a, b, f] at herr
  rw [hexact]
  linarith

/-- Mertens' error has the same limit after a positive power substitution. -/
theorem primeReciprocal_mertens_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ =>
      primeReciprocalSum (y ^ a) - Real.log (Real.log (y ^ a))) atTop
      (nhds meisselMertensConstant) :=
  primeReciprocal_mertens.comp (tendsto_rpow_atTop ha)

/-- The main terms at two positive power cutoffs differ eventually by the
constant `log b - log a`. -/
theorem eventually_log_log_rpow_sub
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ y : ℝ in atTop,
      Real.log (Real.log (y ^ b)) - Real.log (Real.log (y ^ a)) =
        Real.log b - Real.log a := by
  filter_upwards [eventually_gt_atTop 1] with y hy
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hlogy : 0 < Real.log y := Real.log_pos hy
  rw [Real.log_rpow hy0, Real.log_rpow hy0,
    Real.log_mul hb.ne' hlogy.ne', Real.log_mul ha.ne' hlogy.ne']
  ring

/-- Uniform Mertens theorem on a fixed power interval:
`∑_{y^a < p ≤ y^b} 1/p → log b - log a`.

The left side is written as a difference of cumulative sums; the exact
finite-interval form used in the Abel steps is derived below. -/
theorem primeReciprocal_mertens_power_interval
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun y : ℝ =>
      primeReciprocalSum (y ^ b) - primeReciprocalSum (y ^ a)) atTop
      (nhds (Real.log b - Real.log a)) := by
  have herr := (primeReciprocal_mertens_rpow hb).sub
    (primeReciprocal_mertens_rpow ha)
  have hmain : Tendsto (fun y : ℝ =>
      Real.log (Real.log (y ^ b)) - Real.log (Real.log (y ^ a))) atTop
      (nhds (Real.log b - Real.log a)) :=
    (tendsto_congr' (eventually_log_log_rpow_sub ha hb)).2
      tendsto_const_nhds
  convert herr.add hmain using 1 <;> ring_nf

/-- Mertens' error is uniformly small above any fixed positive power of the
main parameter. -/
theorem eventually_uniform_error_above_rpow
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ t, X ^ c ≤ t →
      |primeReciprocalError t| ≤ ε := by
  rcases (eventually_atTop.1 (eventually_abs_primeReciprocalError_lt hε)) with
    ⟨A, hA⟩
  filter_upwards [(tendsto_rpow_atTop hc).eventually
    (eventually_ge_atTop A)] with X hXA
  intro t ht
  exact (hA t (hXA.trans ht)).le

theorem primeReciprocal_interval_sum_eq
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with Nat.Prime p, (p : ℝ)⁻¹ =
      primeReciprocalSum b - primeReciprocalSum a := by
  have h := primeReciprocal_abel (zero_le_one.trans ha.le) hab (fun _ : ℝ => 1)
    (by intro; fun_prop) (by simp)
  simpa using h

theorem outer_mass_tendsto :
    Tendsto (fun X : ℝ =>
      ∑ p ∈ Finset.Ioc ⌊X ^ (10 : ℝ)⁻¹⌋₊
        ⌊X ^ (3 : ℝ)⁻¹⌋₊ with Nat.Prime p, (p : ℝ)⁻¹)
      atTop (nhds (Real.log (3 : ℝ)⁻¹ - Real.log (10 : ℝ)⁻¹)) := by
  have heq : ∀ᶠ X : ℝ in atTop,
      (∑ p ∈ Finset.Ioc ⌊X ^ (10 : ℝ)⁻¹⌋₊
        ⌊X ^ (3 : ℝ)⁻¹⌋₊ with Nat.Prime p, (p : ℝ)⁻¹) =
      primeReciprocalSum (X ^ (3 : ℝ)⁻¹) -
        primeReciprocalSum (X ^ (10 : ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop 1] with X hX
    exact primeReciprocal_interval_sum_eq
      (Real.one_lt_rpow hX (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))
  exact (tendsto_congr' heq).2
    (primeReciprocal_mertens_power_interval (by norm_num) (by norm_num))

/-- A harmless fixed upper bound for the outer prime-reciprocal mass. -/
noncomputable def outerMassBound : ℝ :=
  |Real.log (3 : ℝ)⁻¹ - Real.log (10 : ℝ)⁻¹| + 1

theorem outerMassBound_pos : 0 < outerMassBound := by
  unfold outerMassBound
  positivity

theorem eventually_outer_mass_le :
    ∀ᶠ X : ℝ in atTop,
      (∑ p ∈ Finset.Ioc ⌊X ^ (10 : ℝ)⁻¹⌋₊
        ⌊X ^ (3 : ℝ)⁻¹⌋₊ with Nat.Prime p, (p : ℝ)⁻¹) ≤
      outerMassBound := by
  have hball := outer_mass_tendsto.eventually
    (Metric.ball_mem_nhds
      (Real.log (3 : ℝ)⁻¹ - Real.log (10 : ℝ)⁻¹) zero_lt_one)
  filter_upwards [hball] with X hX
  rw [Real.dist_eq] at hX
  unfold outerMassBound
  have hlim := le_abs_self (Real.log (3 : ℝ)⁻¹ - Real.log (10 : ℝ)⁻¹)
  have hdiff := le_abs_self ((∑ p ∈ Finset.Ioc ⌊X ^ (10 : ℝ)⁻¹⌋₊
    ⌊X ^ (3 : ℝ)⁻¹⌋₊ with Nat.Prime p, (p : ℝ)⁻¹) -
      (Real.log (3 : ℝ)⁻¹ - Real.log (10 : ℝ)⁻¹))
  linarith

theorem innerAbelWeight_upper_le
    {X s : ℝ} (hX : 1 < X) (hs : 0 < s)
    (hshi : s ≤ X ^ (3 : ℝ)⁻¹) :
    innerAbelWeight X s ((X / s) ^ (2 : ℝ)⁻¹) ≤
      3 / Real.log X := by
  let b : ℝ := (X / s) ^ (2 : ℝ)⁻¹
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have hbase : 0 < X / s := div_pos hX0 hs
  have hb : 0 < b := Real.rpow_pos_of_pos hbase _
  have hlogs : Real.log s ≤ (3 : ℝ)⁻¹ * Real.log X := by
    rw [← Real.log_rpow hX0]
    exact Real.log_le_log hs hshi
  have hlogarg : Real.log (X / (s * b)) =
      (2 : ℝ)⁻¹ * (Real.log X - Real.log s) := by
    dsimp only [b]
    rw [Real.log_div hX0.ne' (mul_ne_zero hs.ne' hb.ne'),
      Real.log_mul hs.ne' hb.ne', Real.log_rpow hbase,
      Real.log_div hX0.ne' hs.ne']
    ring
  have hargpos : 0 < Real.log (X / (s * b)) := by
    rw [hlogarg]
    nlinarith
  have hcompare : Real.log X ≤ 3 * Real.log (X / (s * b)) := by
    rw [hlogarg]
    nlinarith
  unfold innerAbelWeight
  change (Real.log (X / (s * b)))⁻¹ ≤ 3 / Real.log X
  rw [inv_eq_one_div]
  exact (div_le_div_iff₀ hargpos hL).2 (by simpa using hcompare)

/-- A fixed upper bound for the normalized lower-endpoint outer weight. -/
noncomputable def outerEndpointBound : ℝ :=
  |normalizedOuterWeight (1 / 10)| + 1

theorem outerEndpointBound_pos : 0 < outerEndpointBound := by
  unfold outerEndpointBound
  positivity

theorem outerAbelWeight_lower_endpoint_le
    {X : ℝ} (hX : 1 < X) :
    outerAbelWeight X (X ^ (10 : ℝ)⁻¹) ≤
      outerEndpointBound / Real.log X := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have hα : normalizedLog X (X ^ (10 : ℝ)⁻¹) = 1 / 10 := by
    unfold normalizedLog
    rw [Real.log_rpow hX0]
    field_simp [hL.ne']
  have hval : outerAbelWeight X (X ^ (10 : ℝ)⁻¹) =
      normalizedOuterWeight (1 / 10) / Real.log X := by
    unfold outerAbelWeight normalizedOuterWeight
    rw [hα]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hval]
  apply (div_le_div_iff_of_pos_right hL).2
  unfold outerEndpointBound
  linarith [le_abs_self (normalizedOuterWeight (1 / 10))]

theorem chenPairs_kernel_eq_nested (x : ℕ) :
    ∑ q ∈ chenPairs x,
        ((q.1 : ℝ) * (q.2 : ℝ) *
          Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ =
      ∑ p ∈ chenFirstPrimes x, (p : ℝ)⁻¹ *
        ∑ q ∈ chenSecondPrimes x p,
          innerAbelWeight (x : ℝ) p q * (q : ℝ)⁻¹ := by
  rw [sum_chenPairs_eq_nested]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  unfold innerAbelWeight
  simp only [mul_inv]
  ring

/-- Deterministic form of the two Abel estimates, assuming a uniform Mertens
error and a bound for the outer prime-reciprocal mass. -/
theorem chenPairs_kernel_le_of_uniform
    {x : ℕ} (hx : 1 < x) {ε C : ℝ} (hε : 0 ≤ ε)
    (hE : ∀ t, (x : ℝ) ^ (10 : ℝ)⁻¹ ≤ t →
      |primeReciprocalError t| ≤ ε)
    (hmass : (∑ p ∈ Finset.Ioc ⌊(x : ℝ) ^ (10 : ℝ)⁻¹⌋₊
        ⌊(x : ℝ) ^ (3 : ℝ)⁻¹⌋₊ with Nat.Prime p, (p : ℝ)⁻¹) ≤ C) :
    ∑ q ∈ chenPairs x,
        ((q.1 : ℝ) * (q.2 : ℝ) *
          Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
      (equation24Integral + 2 * ε * outerEndpointBound + 6 * ε * C) /
        Real.log x := by
  let X : ℝ := x
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hx
  have hL : 0 < Real.log X := Real.log_pos hX
  have hx1 : 1 ≤ x := hx.le
  have hpow : X ^ (10 : ℝ)⁻¹ ≤ X ^ (3 : ℝ)⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hinner : ∀ p ∈ chenFirstPrimes x,
      (∑ q ∈ chenSecondPrimes x p,
        innerAbelWeight X p q * (q : ℝ)⁻¹) ≤
      outerAbelWeight X p + 2 * ε * (3 / Real.log X) := by
    intro p hp
    have hp' := hp
    simp only [chenFirstPrimes, Finset.mem_filter, Finset.mem_range] at hp'
    rcases hp' with ⟨_hprange, hpprime, hplo, hphi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    rw [chenSecondPrimes_eq_Ioc hx1 hp]
    have hEin : ∀ t ∈ Set.Icc (X ^ (3 : ℝ)⁻¹)
        ((X / p) ^ (2 : ℝ)⁻¹), |primeReciprocalError t| ≤ ε := by
      intro t ht
      exact hE t (hpow.trans ht.1)
    have hi := inner_primeReciprocal_abel_le hX hp0 hplo.le hphi hε hEin
    calc
      ∑ q ∈ Finset.Ioc ⌊X ^ (3 : ℝ)⁻¹⌋₊
          ⌊(X / p) ^ (2 : ℝ)⁻¹⌋₊ with Nat.Prime q,
          innerAbelWeight X p q * (q : ℝ)⁻¹ ≤
        outerAbelWeight X p +
          2 * ε * innerAbelWeight X p ((X / p) ^ (2 : ℝ)⁻¹) := hi
      _ ≤ outerAbelWeight X p + 2 * ε * (3 / Real.log X) := by
        gcongr
        exact innerAbelWeight_upper_le hX hp0 hphi
  rw [chenPairs_kernel_eq_nested]
  calc
    ∑ p ∈ chenFirstPrimes x, (p : ℝ)⁻¹ *
        ∑ q ∈ chenSecondPrimes x p,
          innerAbelWeight X p q * (q : ℝ)⁻¹ ≤
      ∑ p ∈ chenFirstPrimes x, (p : ℝ)⁻¹ *
        (outerAbelWeight X p + 2 * ε * (3 / Real.log X)) := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (hinner p hp)
            (inv_nonneg.2 (Nat.cast_nonneg p))
    _ = (∑ p ∈ chenFirstPrimes x,
          outerAbelWeight X p * (p : ℝ)⁻¹) +
        (6 * ε / Real.log X) *
          ∑ p ∈ chenFirstPrimes x, (p : ℝ)⁻¹ := by
      calc
        ∑ p ∈ chenFirstPrimes x, (p : ℝ)⁻¹ *
            (outerAbelWeight X p + 2 * ε * (3 / Real.log X)) =
          ∑ p ∈ chenFirstPrimes x,
            (outerAbelWeight X p * (p : ℝ)⁻¹ +
              (6 * ε / Real.log X) * (p : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
        _ = (∑ p ∈ chenFirstPrimes x,
              outerAbelWeight X p * (p : ℝ)⁻¹) +
            ∑ p ∈ chenFirstPrimes x,
              (6 * ε / Real.log X) * (p : ℝ)⁻¹ :=
          Finset.sum_add_distrib
        _ = (∑ p ∈ chenFirstPrimes x,
              outerAbelWeight X p * (p : ℝ)⁻¹) +
            (6 * ε / Real.log X) *
              ∑ p ∈ chenFirstPrimes x, (p : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    _ ≤ (equation24Integral / Real.log X +
          2 * ε * outerAbelWeight X (X ^ (10 : ℝ)⁻¹)) +
        (6 * ε / Real.log X) * C := by
      rw [chenFirstPrimes_eq_Ioc hx1]
      gcongr
      · apply outer_primeReciprocal_abel_le hX hε
        intro s hs
        exact hE s hs.1
    _ ≤ (equation24Integral / Real.log X +
          2 * ε * (outerEndpointBound / Real.log X)) +
        (6 * ε / Real.log X) * C := by
      gcongr
      exact outerAbelWeight_lower_endpoint_le hX
    _ = (equation24Integral + 2 * ε * outerEndpointBound + 6 * ε * C) /
        Real.log x := by
      dsimp only [X]
      ring

/-- The two prime-reciprocal partial-summation steps between (23) and (24).
For every positive additive error, the pair kernel is eventually bounded by
equation (24) plus that error. -/
theorem eventually_chenPairs_kernel_le_integral_add
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      ∑ q ∈ chenPairs x,
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
        (equation24Integral + δ) / Real.log x := by
  let D : ℝ := 2 * outerEndpointBound + 6 * outerMassBound + 1
  let ε : ℝ := δ / D
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [outerEndpointBound_pos, outerMassBound_pos]
  have hε : 0 < ε := div_pos hδ hD
  have herror_real := eventually_uniform_error_above_rpow
    (c := (10 : ℝ)⁻¹) (by norm_num) hε
  have hmass_real := eventually_outer_mass_le
  have hcast : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have herror := hcast.eventually herror_real
  have hmass := hcast.eventually hmass_real
  have herr : 2 * ε * outerEndpointBound + 6 * ε * outerMassBound ≤ δ := by
    have hratio :
        (2 * outerEndpointBound + 6 * outerMassBound) / D ≤ 1 := by
      apply (div_le_one hD).2
      dsimp only [D]
      linarith
    calc
      2 * ε * outerEndpointBound + 6 * ε * outerMassBound =
          δ * ((2 * outerEndpointBound + 6 * outerMassBound) / D) := by
        dsimp only [ε]
        ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hratio hδ.le
      _ = δ := by ring
  filter_upwards [herror, hmass, eventually_gt_atTop 1] with x hE hM hx
  have hbase := chenPairs_kernel_le_of_uniform hx hε.le hE hM
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  calc
    ∑ q ∈ chenPairs x,
        ((q.1 : ℝ) * (q.2 : ℝ) *
          Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
      (equation24Integral + 2 * ε * outerEndpointBound +
        6 * ε * outerMassBound) / Real.log x := hbase
    _ ≤ (equation24Integral + δ) / Real.log x := by
      exact (div_le_div_iff_of_pos_right hlog).2 (by linarith)

end Chen
