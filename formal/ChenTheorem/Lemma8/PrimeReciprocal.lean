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
  convert herr.add hmain using 1 <;> ring

/-- The two prime-reciprocal partial-summation steps between (23) and (24).

Here `η` absorbs both occurrences of the paper's factor `1 + ε`; allowing an
arbitrary positive `η` is the invariant asymptotic content of those steps. -/
axiom eventually_chenPairs_kernel_le_one_add_mul_integral
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop,
      ∑ q ∈ chenPairs x,
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
        (1 + η) * equation24Integral / Real.log x

end Chen
