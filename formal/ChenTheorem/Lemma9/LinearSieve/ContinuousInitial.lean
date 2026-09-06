import ChenTheorem.Lemma9.LinearSieve.ContinuousErrorDecay

open Set MeasureTheory

namespace Chen.LinearSieve

/-- The initial normalization obtained from the convergent error series.
Its identification with `2 exp γ` is a separate theorem still needed. -/
noncomputable def linearSieveInitialConstant : ℝ := 3 * (1 + upperContinuousError 3)

theorem linearSieveInitialConstant_ge_three : 3 ≤ linearSieveInitialConstant := by
  have h := (upperContinuousError_bounds 3 (by norm_num)).1
  unfold linearSieveInitialConstant
  linarith

theorem upperContinuousError_eq_first_add_tail (s : ℝ) (hs : 1 < s) :
    upperContinuousError s = rosserContinuousTerm 1 s +
      ∑' N, rosserContinuousTerm (2 * N + 3) s := by
  unfold upperContinuousError
  rw [(summable_odd_rosserContinuousTerm s hs).tsum_eq_zero_add]
  simp only [Nat.mul_zero, zero_add]
  congr 1

/-- The initial upper-sieve formula, with its normalization defined by
the actual convergent series. -/
theorem mul_upperContinuousError_initial (s : ℝ) (hs : 1 < s) (hs3 : s ≤ 3) :
    s * upperContinuousError s = linearSieveInitialConstant - s := by
  have hs0 : 0 < s := by linarith
  have hterm : ∀ N : ℕ, s * rosserContinuousTerm (2 * N + 3) s =
      3 * rosserContinuousTerm (2 * N + 3) 3 := by
    intro N
    have hc : rosserContinuousCutoff (2 * N + 1 + 2) = 3 := by
      simp [rosserContinuousCutoff, Nat.even_add]
    have h := mul_rosserContinuousTerm_constant_below (2 * N + 1) s hs0 (by rwa [hc])
    simpa only [hc] using h
  have htail : s * (∑' N, rosserContinuousTerm (2 * N + 3) s) =
      3 * ∑' N, rosserContinuousTerm (2 * N + 3) 3 := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr hterm
  have h3 := upperContinuousError_eq_first_add_tail 3 (by norm_num)
  rw [rosserContinuousTerm_eq_zero 1 3 (by norm_num), zero_add] at h3
  have hfirst : s * rosserContinuousTerm 1 s = 3 - s := by
    rw [rosserContinuousTerm_one s hs0, max_eq_left (sub_nonneg.mpr hs3)]
    field_simp
  rw [upperContinuousError_eq_first_add_tail s hs, mul_add, hfirst, htail, ← h3]
  unfold linearSieveInitialConstant
  ring

theorem upperContinuousError_initial (s : ℝ) (hs : 1 < s) (hs3 : s ≤ 3) :
    upperContinuousError s = linearSieveInitialConstant / s - 1 := by
  have h := mul_upperContinuousError_initial s hs hs3
  have hs0 : s ≠ 0 := by linarith
  field_simp
  nlinarith

/-- Integration of the lower delay equation over its first interval.
The endpoint value `T⁻(2)` is retained until its own proof is supplied. -/
theorem mul_lowerContinuousError_initial (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    s * lowerContinuousError s = 2 * lowerContinuousError 2 + s - 2 -
      linearSieveInitialConstant * Real.log (s - 1) := by
  let g : ℝ → ℝ := fun t => 1 - linearSieveInitialConstant / (t - 1)
  have hgcont : ContinuousOn g (Icc 2 s) :=
    continuousOn_const.sub (continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun t ht => by dsimp; linarith [ht.1]))
  have hgi : IntervalIntegrable g volume 2 s := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hs] using hgcont
  have hprod : ContinuousOn (fun t => t * lowerContinuousError t) (Icc 2 s) :=
    continuousOn_id.mul (continuousOn_lowerContinuousError.mono (fun _ ht => ht.1))
  have hdprod : ∀ t ∈ Ioo 2 s,
      HasDerivAt (fun t => t * lowerContinuousError t) (g t) t := by
    intro t ht
    have hu := upperContinuousError_initial (t - 1) (by linarith [ht.1]) (by linarith [ht.2])
    have h := hasDerivAt_mul_lowerContinuousError t ht.1
    rw [hu] at h
    convert! h using 1
    dsimp [g]
    ring
  have hprodI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hprod hdprod hgi
  have hprimitive : ∀ t ∈ uIcc 2 s,
      HasDerivAt (fun t => t - linearSieveInitialConstant * Real.log (t - 1)) (g t) t := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    have ht0 : t - 1 ≠ 0 := by linarith [ht.1]
    have hlog := (Real.hasDerivAt_log ht0).comp t ((hasDerivAt_id t).sub_const 1)
    convert! (hasDerivAt_id t).sub (hlog.const_mul linearSieveInitialConstant) using 1
    dsimp [g]
    ring
  have hprimI := intervalIntegral.integral_eq_sub_of_hasDerivAt hprimitive hgi
  norm_num only [sub_self, show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, mul_zero, sub_zero] at hprimI
  linarith

end Chen.LinearSieve
