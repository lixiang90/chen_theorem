import ChenTheorem.Lemma9.LinearSieve.ProfileContinuity
import ChenTheorem.Lemma8.PrimeReciprocal

open Set MeasureTheory

namespace Chen.LinearSieve

theorem hasDerivAt_upperLinearSieveFunction_deriv (s : ℝ) (hs : 1 < s) :
    HasDerivAt upperLinearSieveFunction (deriv upperContinuousError s) s := by
  have h := hasDerivAt_upperContinuousError_all s hs
  rw [h.deriv]
  exact h.const_add 1

theorem deriv_upperLinearSieveFunction_eq (s : ℝ) (hs : 1 < s) :
    deriv upperLinearSieveFunction s = deriv upperContinuousError s :=
  (hasDerivAt_upperLinearSieveFunction_deriv s hs).deriv

theorem continuousOn_deriv_upperLinearSieveFunction :
    ContinuousOn (deriv upperLinearSieveFunction) (Ioi 1) :=
  continuousOn_deriv_upperContinuousError_all.congr (fun s hs => deriv_upperLinearSieveFunction_eq s hs)

theorem hasDerivAt_normalizedLog_pos (X t : ℝ) (ht : 0 < t) :
    HasDerivAt (normalizedLog X) (1 / (t * Real.log X)) t := by
  convert! (Real.hasDerivAt_log ht.ne').div_const (Real.log X) using 1
  simp only [mul_inv_rev, div_eq_mul_inv, mul_comm, one_mul]

theorem normalizedLog_rpow (X r : ℝ) (hX : 1 < X) : normalizedLog X (X ^ r) = r := by
  unfold normalizedLog
  rw [Real.log_rpow (by linarith), mul_div_cancel_right₀ r (Real.log_pos hX).ne']

theorem normalizedLog_power_interval (X t : ℝ) (hX : 1 < X)
    (ht : t ∈ Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) :
    1 / 10 ≤ normalizedLog X t ∧ normalizedLog X t ≤ 1 / 3 := by
  have hX0 : 0 < X := by linarith
  have ht0 : 0 < t := (Real.rpow_pos_of_pos hX0 _).trans_le ht.1
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) ht.1
  have hhi := Real.log_le_log ht0 ht.2
  rw [Real.log_rpow hX0] at hlo hhi
  unfold normalizedLog
  exact ⟨(le_div_iff₀ (Real.log_pos hX)).mpr hlo,
    (div_le_iff₀ (Real.log_pos hX)).mpr hhi⟩

noncomputable def upperSievePrimeWeight (a X t : ℝ) : ℝ :=
  upperLinearSieveFunction (10 * a - 10 * normalizedLog X t)

theorem upperSievePrimeWeight_argument (a X t : ℝ) (ha : 29 / 60 < a) (hX : 1 < X)
    (ht : t ∈ Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) :
    3 / 2 ≤ 10 * a - 10 * normalizedLog X t := by
  have h := (normalizedLog_power_interval X t hX ht).2
  linarith

theorem upperSievePrimeWeight_bounds (a X t : ℝ) (ha : 29 / 60 < a) (hX : 1 < X)
    (ht : t ∈ Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) :
    0 ≤ upperSievePrimeWeight a X t ∧ upperSievePrimeWeight a X t ≤ 5 := by
  have hs := upperSievePrimeWeight_argument a X t ha hX ht
  exact ⟨(show (0 : ℝ) ≤ 1 by norm_num).trans
    (upperLinearSieveFunction_ge_one _ (by linarith)), upperLinearSieveFunction_le_five _ hs⟩

theorem hasDerivAt_upperSievePrimeWeight (a X t : ℝ) (ht : 0 < t)
    (hs : 1 < 10 * a - 10 * normalizedLog X t) :
    HasDerivAt (upperSievePrimeWeight a X)
      (deriv upperLinearSieveFunction (10 * a - 10 * normalizedLog X t) *
        (-10 / (t * Real.log X))) t := by
  have hF := hasDerivAt_upperLinearSieveFunction_deriv _ hs
  rw [← deriv_upperLinearSieveFunction_eq _ hs] at hF
  have hg := ((hasDerivAt_normalizedLog_pos X t ht).const_mul 10).const_sub (10 * a)
  convert! hF.comp t hg using 1
  ring

theorem deriv_upperSievePrimeWeight_nonneg (a X t : ℝ) (ha : 29 / 60 < a) (hX : 1 < X)
    (ht : t ∈ Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) :
    0 ≤ deriv (upperSievePrimeWeight a X) t := by
  have hs := upperSievePrimeWeight_argument a X t ha hX ht
  have ht0 : 0 < t := (Real.rpow_pos_of_pos (by linarith : 0 < X) _).trans_le ht.1
  rw [(hasDerivAt_upperSievePrimeWeight a X t ht0 (by linarith)).deriv,
    deriv_upperLinearSieveFunction_eq _ (by linarith)]
  exact mul_nonneg_of_nonpos_of_nonpos (deriv_upperContinuousError_nonpos_all _ (by linarith))
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_nonneg ht0.le (Real.log_pos hX).le))

theorem continuousOn_deriv_upperSievePrimeWeight (a X : ℝ) (ha : 29 / 60 < a) (hX : 1 < X) :
    ContinuousOn (deriv (upperSievePrimeWeight a X))
      (Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) := by
  have ht0 (t : ℝ) (ht : t ∈ Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) : 0 < t :=
    (Real.rpow_pos_of_pos (by linarith : 0 < X) _).trans_le ht.1
  have hg : ContinuousOn (fun t => 10 * a - 10 * normalizedLog X t)
      (Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) :=
    continuousOn_const.sub (continuousOn_const.mul (continuousOn_of_forall_continuousAt
      (fun t ht => (hasDerivAt_normalizedLog_pos X t (ht0 t ht)).continuousAt)))
  have hF := continuousOn_deriv_upperLinearSieveFunction.comp hg (fun t ht => by
    change 1 < 10 * a - 10 * normalizedLog X t
    linarith [upperSievePrimeWeight_argument a X t ha hX ht])
  have hc : ContinuousOn (fun t => deriv upperLinearSieveFunction (10 * a - 10 * normalizedLog X t) *
      (-10 / (t * Real.log X))) (Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ))) :=
    hF.mul (continuousOn_const.div (continuousOn_id.mul continuousOn_const)
      (fun t ht => mul_ne_zero (ht0 t ht).ne' (Real.log_pos hX).ne'))
  apply hc.congr
  intro t ht
  exact (hasDerivAt_upperSievePrimeWeight a X t (ht0 t ht)
    (by linarith [upperSievePrimeWeight_argument a X t ha hX ht])).deriv

end Chen.LinearSieve
