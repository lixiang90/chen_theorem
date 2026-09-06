import ChenTheorem.Lemma9.LinearSieve.BuchstabError

open Finset MeasureTheory

namespace Chen.LinearSieve

/-- The logarithmic level parameter in the linear sieve. -/
noncomputable def sieveParameter (D t : ℝ) : ℝ := Real.log D / Real.log t

theorem sieveParameter_pos {D t : ℝ} (hD : 1 < D) (ht : 1 < t) :
    0 < sieveParameter D t := div_pos (Real.log_pos hD) (Real.log_pos ht)

/-- Selecting a prime divides the level by that prime, hence subtracts
one from the logarithmic parameter at the new cutoff. -/
theorem sieveParameter_div_self (D t : ℝ) (hD : 0 < D) (ht : 1 < t) :
    sieveParameter (D / t) t = sieveParameter D t - 1 := by
  have ht0 : t ≠ 0 := by linarith
  rw [sieveParameter, Real.log_div hD.ne' ht0, sub_div,
    div_self (Real.log_pos ht).ne']
  rfl

theorem sieveParameter_antitone {D : ℝ} (hD : 1 < D) :
    AntitoneOn (sieveParameter D) (Set.Ioi 1) := by
  intro x hx y hy hxy
  exact div_le_div_of_nonneg_left (Real.log_pos hD).le (Real.log_pos hx)
    (Real.log_le_log (lt_trans zero_lt_one hx) hxy)

theorem sieveParameter_mem_Icc {D w z t : ℝ} (hD : 1 < D) (hw : 2 ≤ w)
    (ht : t ∈ Set.Icc w z) :
    sieveParameter D t ∈ Set.Icc (sieveParameter D z) (sieveParameter D w) := by
  have ha := sieveParameter_antitone hD
  have hw1 : w ∈ Set.Ioi 1 := by change 1 < w; linarith
  have ht1 : t ∈ Set.Ioi 1 := by change 1 < t; linarith [ht.1]
  have hz1 : z ∈ Set.Ioi 1 := by change 1 < z; linarith [ht.1, ht.2]
  exact ⟨ha ht1 hz1 ht.2, ha hw1 ht1 ht.1⟩

theorem hasDerivAt_sieveParameter (D t : ℝ) (ht : 1 < t) :
    HasDerivAt (sieveParameter D) (-Real.log D * logSieveKernel t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 := (Real.log_pos ht).ne'
  convert! (hasDerivAt_const t (Real.log D)).fun_div (Real.hasDerivAt_log ht0) hl0 using 1
  dsimp [logSieveKernel]
  field_simp
  ring

theorem continuousOn_sieveParameter (D w z : ℝ) (hw : 2 ≤ w) :
    ContinuousOn (sieveParameter D) (Set.Icc w z) := by
  intro t ht
  exact (hasDerivAt_sieveParameter D t (by linarith [ht.1])).continuousAt.continuousWithinAt

/-- The precise logarithmic change of variables from prime size to
the sieve parameter. The integration limits reverse because the map decreases. -/
theorem integral_sieveParameter_substitution (D w z : ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (hwz : w ≤ z) (H : ℝ → ℝ)
    (hH : ContinuousOn H (Set.Icc (sieveParameter D z) (sieveParameter D w))) :
    Real.log z * (∫ t in Set.Ioc w z, H (sieveParameter D t) * logSieveKernel t) =
      (1 / sieveParameter D z) *
        ∫ s in Set.Ioc (sieveParameter D z) (sieveParameter D w), H s := by
  have hlimits : sieveParameter D z ≤ sieveParameter D w :=
    (sieveParameter_mem_Icc hD hw (show z ∈ Set.Icc w z from ⟨hwz, le_rfl⟩)).2
  have hmaps : sieveParameter D '' Set.uIcc w z ⊆
      Set.Icc (sieveParameter D z) (sieveParameter D w) := by
    rintro s ⟨t, ht, rfl⟩
    apply sieveParameter_mem_Icc hD hw
    simpa only [Set.uIcc_of_le hwz] using ht
  have hderiv : ∀ t ∈ Set.uIcc w z,
      HasDerivAt (sieveParameter D) (-Real.log D * logSieveKernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le hwz] at ht
    exact hasDerivAt_sieveParameter D t (by linarith [ht.1])
  have hc : ContinuousOn (fun t => -Real.log D * logSieveKernel t) (Set.uIcc w z) := by
    rw [Set.uIcc_of_le hwz]
    exact continuousOn_const.mul (continuousOn_logSieveKernel w z hw)
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hc (hH.mono hmaps)
  rw [intervalIntegral.integral_of_le hwz,
    intervalIntegral.integral_symm (sieveParameter D z) (sieveParameter D w),
    intervalIntegral.integral_of_le hlimits] at hsub
  have he : (∫ t in Set.Ioc w z, (H ∘ sieveParameter D) t *
      (-Real.log D * logSieveKernel t)) =
        -Real.log D * ∫ t in Set.Ioc w z, H (sieveParameter D t) * logSieveKernel t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only [Function.comp_def]
    ring
  rw [he] at hsub
  have hL : Real.log D ≠ 0 := (Real.log_pos hD).ne'
  have hlz : Real.log z ≠ 0 := (Real.log_pos (by linarith)).ne'
  unfold sieveParameter at hsub ⊢
  field_simp
  nlinarith [hsub]

end Chen.LinearSieve
