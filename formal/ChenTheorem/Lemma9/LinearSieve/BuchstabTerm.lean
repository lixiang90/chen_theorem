import ChenTheorem.Lemma9.LinearSieve.BuchstabRight
import ChenTheorem.Lemma9.LinearSieve.BuchstabParameter
import ChenTheorem.Lemma9.LinearSieve.ContinuousTermJunction

open Finset MeasureTheory Set

namespace Chen.LinearSieve

noncomputable def rosserTermWeightSlope (n : ℕ) (D t : ℝ) : ℝ :=
  (rosserTermLeftSource n (sieveParameter D t - 1) +
    rosserContinuousTerm (n + 2) (sieveParameter D t - 1)) /
      (sieveParameter D t - 1) * (Real.log D * logSieveKernel t)

/-- Reversing the sieve parameter converts the left derivative of a
continuous term into the right derivative needed by Abel summation. -/
theorem hasDerivWithinAt_rosserTermWeight_right (n : ℕ) (D t : ℝ)
    (hD : 1 < D) (ht : 1 < t) (hs : 1 < sieveParameter D t) :
    HasDerivWithinAt (fun t => rosserContinuousTerm (n + 2) (sieveParameter D t - 1))
      (rosserTermWeightSlope n D t) (Ioi t) t := by
  have hm : MapsTo (fun x => sieveParameter D x - 1) (Ioi t)
      (Iio (sieveParameter D t - 1)) := by
    intro x hx
    change sieveParameter D x - 1 < sieveParameter D t - 1
    apply sub_lt_sub_right
    exact div_lt_div_of_pos_left (Real.log_pos hD) (Real.log_pos ht)
      (Real.log_lt_log (by linarith) hx)
  have hh := (hasDerivWithinAt_rosserContinuousTerm_left n _ (sub_pos.mpr hs)).comp t
    ((hasDerivAt_sieveParameter D t ht).sub_const 1).hasDerivWithinAt hm
  convert! hh using 1
  dsimp [rosserTermWeightSlope]
  ring

theorem integrableOn_rosserTermWeightSlope (n : ℕ) (D w z : ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (hs : 1 < sieveParameter D z) :
    IntegrableOn (rosserTermWeightSlope n D) (Icc w z) := by
  have hc : ContinuousOn (fun t => sieveParameter D t - 1) (Icc w z) :=
    (continuousOn_sieveParameter D w z hw).sub continuousOn_const
  have hpos : ∀ t ∈ Icc w z, 0 < sieveParameter D t - 1 := by
    intro t ht
    linarith [(sieveParameter_mem_Icc hD hw ht).1]
  have hfc := (continuousOn_rosserContinuousTerm (n + 2)).comp hc hpos
  have hum : Measurable (fun t => sieveParameter D t - 1) := by
    unfold sieveParameter
    fun_prop
  have hi := (integrableOn_rosserTermLeftSource_comp n w z _ hc hum).add hfc.integrableOn_Icc
  have hfactor : ContinuousOn
      (fun t => (1 / (sieveParameter D t - 1)) * (Real.log D * logSieveKernel t)) (Icc w z) :=
    (continuousOn_const.div hc (fun t ht => (hpos t ht).ne')).mul
      (continuousOn_const.mul (continuousOn_logSieveKernel w z hw))
  apply (hi.mul_continuousOn hfactor isCompact_Icc).congr_fun _ measurableSet_Icc
  intro t _
  dsimp [rosserTermWeightSlope]
  ring

theorem rosserTermWeightSlope_nonneg (n : ℕ) (D t : ℝ)
    (hD : 1 < D) (ht : 1 < t) (hs : 1 < sieveParameter D t) :
    0 ≤ rosserTermWeightSlope n D t := by
  have hsource := rosserTermLeftSource_nonneg n (sieveParameter D t - 1)
  have hf := rosserContinuousTerm_nonneg (n + 2) _ (sub_pos.mpr hs)
  have hlog := (Real.log_pos hD).le
  have ht0 : 0 < t := zero_lt_one.trans ht
  unfold rosserTermWeightSlope logSieveKernel
  positivity

/-- Each recursive continuous term is a valid Buchstab weight across its
lower junction; there is no assumption of two-sided differentiability. -/
theorem weighted_buchstab_rosserTerm_parameter_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 1 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          rosserContinuousTerm (n + 2) (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
          (1 / sieveParameter D z) * (∫ s in Ioc (sieveParameter D z) (sieveParameter D w),
            rosserContinuousTerm (n + 2) (s - 1)) +
              2 * K * rosserContinuousTerm (n + 2) (sieveParameter D z - 1) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_partial_summation_of_hasDeriv_right
  refine ⟨K, hK, ?_⟩
  intro n D w z hD hw hwz hs P hP hodd
  have hpos : ∀ t ∈ Icc w (z : ℝ), 1 < sieveParameter D t :=
    fun t ht => hs.trans_le (sieveParameter_mem_Icc hD hw ht).1
  have hHc : ContinuousOn (fun s => rosserContinuousTerm (n + 2) (s - 1))
      (Icc (sieveParameter D z) (sieveParameter D w)) :=
    (continuousOn_shift_rosserContinuousTerm (n + 2)).mono
      (fun _ ht => hs.trans_le ht.1)
  have hfc := hHc.comp (continuousOn_sieveParameter D w z hw)
    (fun t ht => sieveParameter_mem_Icc hD hw ht)
  have hshape := (antitoneOn_mul_shift_rosserContinuousTerm (n + 2)).mono
    (show Icc (sieveParameter D z) (sieveParameter D w) ⊆ Ioi 1 from
      fun _ ht => hs.trans_le ht.1)
  have h := hb w z hw hwz P hP hodd _ (rosserTermWeightSlope n D) hfc
    (fun t ht => hasDerivWithinAt_rosserTermWeight_right n D t hD
      (by linarith [ht.1]) (hpos t ⟨ht.1.le, ht.2.le⟩))
    (integrableOn_rosserTermWeightSlope n D w z hD hw hs)
    (fun t ht => rosserContinuousTerm_nonneg (n + 2) _ (sub_pos.mpr (hpos t ht)))
    (fun t ht => rosserTermWeightSlope_nonneg n D t hD (by linarith [ht.1]) (hpos t ht))
    (sieveParameter_weight_log_growth D w z hD hw hwz _ hshape)
  dsimp only [Function.comp_def] at h
  rwa [integral_sieveParameter_substitution D w z hD hw hwz _ hHc] at h

/-- The continuous recurrence integrates exactly from the lower endpoint
itself, with the nonnegative terminal tail retained. -/
theorem integral_shift_rosserContinuousTerm (n : ℕ) (s b : ℝ)
    (hs : rosserContinuousCutoff (n + 2) ≤ s) (hsb : s ≤ b) :
    (∫ t in s..b, rosserContinuousTerm (n + 1) (t - 1)) =
      s * rosserContinuousTerm (n + 2) s - b * rosserContinuousTerm (n + 2) b := by
  have hc := (rosserContinuousCutoff_bounds (n + 2)).1
  have hcont := (continuousOn_shift_rosserContinuousTerm (n + 1)).mono
    (show Icc s b ⊆ Ioi 1 from fun t ht => by change 1 < t; linarith [ht.1])
  have hi : IntervalIntegrable (fun t => rosserContinuousTerm (n + 1) (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb] using hcont
  have hf : ContinuousOn (fun t => t * rosserContinuousTerm (n + 2) t) (Icc s b) :=
    continuousOn_id.mul ((continuousOn_rosserContinuousTerm (n + 2)).mono
      (fun t ht => by change 0 < t; linarith [ht.1]))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsb hf
    (fun t ht => hasDerivAt_mul_rosserContinuousTerm n t (hs.trans_lt ht.1)) hi.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem parameter_integral_shift_rosserContinuousTerm_le (n : ℕ) (s b : ℝ)
    (hs : rosserContinuousCutoff (n + 2) ≤ s) (hsb : s ≤ b) :
    (1 / s) * (∫ t in Ioc s b, rosserContinuousTerm (n + 1) (t - 1)) ≤
      rosserContinuousTerm (n + 2) s := by
  have hc := (rosserContinuousCutoff_bounds (n + 2)).1
  have hs0 : 0 < s := by linarith
  have hb0 : 0 < b := hs0.trans_le hsb
  have hn := mul_nonneg hb0.le (rosserContinuousTerm_nonneg (n + 2) b hb0)
  rw [← intervalIntegral.integral_of_le hsb, integral_shift_rosserContinuousTerm n s b hs hsb,
    one_div, ← div_eq_inv_mul, div_le_iff₀ hs0]
  nlinarith

/-- The recursive continuous majorant and its explicit `1/log w` error.
This applies even when the child term's lower junction lies inside the sum. -/
theorem weighted_buchstab_rosserTerm_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → rosserContinuousCutoff (n + 3) ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          rosserContinuousTerm (n + 2) (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
          rosserContinuousTerm (n + 3) (sieveParameter D z) +
            2 * K * rosserContinuousTerm (n + 2) (sieveParameter D z - 1) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_rosserTerm_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro n D w z hD hw hwz hs P hP hodd
  have hs1 : 1 < sieveParameter D z := by
    linarith [(rosserContinuousCutoff_bounds (n + 3)).1]
  apply (hb n D w z hD hw hwz hs1 P hP hodd).trans
  apply _root_.add_le_add _ le_rfl
  exact parameter_integral_shift_rosserContinuousTerm_le (n + 1) _ _ hs
    (sieveParameter_mem_Icc hD hw ⟨hwz, le_rfl⟩).2

end Chen.LinearSieve
