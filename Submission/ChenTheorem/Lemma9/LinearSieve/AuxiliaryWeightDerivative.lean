import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryJunction

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

theorem hasDerivAt_childAuxiliaryWeight (δ t : ℝ) (ht : 1 < t) :
    HasDerivAt (childAuxiliaryWeight δ)
      (childAuxiliaryWeight δ t * (δ / t + (1 - δ) / (t - 1))) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hr : 0 < t / (t - 1) := div_pos (by linarith) (by linarith)
  have hd := (((hasDerivAt_id t).div ((hasDerivAt_id t).sub_const 1) ht1).rpow_const
    (p := δ) (Or.inl hr.ne')).mul ((hasDerivAt_id t).sub_const 1)
  apply hd.congr_deriv
  dsimp only [id_eq, Pi.div_apply, childAuxiliaryWeight]
  rw [Real.rpow_sub hr, Real.rpow_one]
  field_simp
  ring

theorem hasDerivWithinAt_childAuxiliaryWeight_shift_left
    (δ t S : ℝ) (H : ℝ → ℝ) (ht : 1 < t)
    (hH : HasDerivWithinAt H (-(S + 2 * H (t - 1)) / (t - 1)) (Iio (t - 1)) (t - 1)) :
    HasDerivWithinAt (fun t => childAuxiliaryWeight δ t * H (t - 1))
      (-(childAuxiliaryWeight δ t / (t - 1) *
        (S + H (t - 1) * (1 + δ / t)))) (Iio t) t := by
  have hm : MapsTo (fun x : ℝ => x - 1) (Iio t) (Iio (t - 1)) := by
    intro x hx
    change x - 1 < t - 1
    exact sub_lt_sub_right hx 1
  have hh := hH.comp t ((hasDerivAt_id t).sub_const 1).hasDerivWithinAt hm
  have hd := (hasDerivAt_childAuxiliaryWeight δ t ht).hasDerivWithinAt.mul hh
  apply hd.congr_deriv
  dsimp only [Function.comp_def, id_eq]
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  field_simp
  ring

noncomputable def auxiliaryPrimeSlope (δ : ℝ) (H S : ℝ → ℝ) (D t : ℝ) : ℝ :=
  childAuxiliaryWeight δ (sieveParameter D t) / (sieveParameter D t - 1) *
    (S (sieveParameter D t - 1) + H (sieveParameter D t - 1) *
      (1 + δ / sieveParameter D t)) * (Real.log D * logSieveKernel t)

theorem hasDerivWithinAt_auxiliaryPrimeWeight_right
    (δ D t : ℝ) (H S : ℝ → ℝ) (hD : 1 < D) (ht : 1 < t)
    (hs : 1 < sieveParameter D t)
    (hH : HasDerivWithinAt H
      (-(S (sieveParameter D t - 1) + 2 * H (sieveParameter D t - 1)) /
        (sieveParameter D t - 1)) (Iio (sieveParameter D t - 1)) (sieveParameter D t - 1)) :
    HasDerivWithinAt (fun t => childAuxiliaryWeight δ (sieveParameter D t) *
        H (sieveParameter D t - 1)) (auxiliaryPrimeSlope δ H S D t) (Ioi t) t := by
  have hm : MapsTo (sieveParameter D) (Ioi t) (Iio (sieveParameter D t)) := by
    intro x hx
    change sieveParameter D x < sieveParameter D t
    exact div_lt_div_of_pos_left (Real.log_pos hD) (Real.log_pos ht)
      (Real.log_lt_log (by linarith) hx)
  have hh := (hasDerivWithinAt_childAuxiliaryWeight_shift_left δ (sieveParameter D t)
    (S (sieveParameter D t - 1)) H hs hH).comp t
      (hasDerivAt_sieveParameter D t ht).hasDerivWithinAt hm
  convert! hh using 1
  dsimp [auxiliaryPrimeSlope]
  ring

theorem auxiliaryPrimeSlope_nonneg (δ D t : ℝ) (H S : ℝ → ℝ)
    (hδ : 0 ≤ δ) (hD : 1 < D) (ht : 1 < t) (hs : 1 < sieveParameter D t)
    (hH : 0 ≤ H (sieveParameter D t - 1)) (hS : 0 ≤ S (sieveParameter D t - 1)) :
    0 ≤ auxiliaryPrimeSlope δ H S D t := by
  have hw := childAuxiliaryWeight_nonneg δ (sieveParameter D t) hs
  have hs0 : 0 < sieveParameter D t := by linarith
  have hs1 : 0 < sieveParameter D t - 1 := by linarith
  have hl := (Real.log_pos hD).le
  have ht0 : 0 < t := by linarith
  unfold auxiliaryPrimeSlope logSieveKernel
  positivity

theorem integrableOn_auxiliaryPrimeSlope (δ D w z a : ℝ) (H S : ℝ → ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (ha : 0 ≤ a) (hs : a + 1 < sieveParameter D z)
    (hH : ContinuousOn H (Ioi a))
    (hS : IntegrableOn (fun t => S (sieveParameter D t - 1)) (Icc w z)) :
    IntegrableOn (auxiliaryPrimeSlope δ H S D) (Icc w z) := by
  have hu := continuousOn_sieveParameter D w z hw
  have hu1 : ContinuousOn (fun t => sieveParameter D t - 1) (Icc w z) :=
    hu.sub continuousOn_const
  have hpos : ∀ t ∈ Icc w z, a + 1 < sieveParameter D t :=
    fun t ht => hs.trans_le (sieveParameter_mem_Icc hD hw ht).1
  have huc : ∀ t ∈ Icc w z, 1 < sieveParameter D t := by
    intro t ht
    linarith [hpos t ht]
  have hfc := hH.comp hu1 (fun t ht => by change a < sieveParameter D t - 1; linarith [hpos t ht])
  have hscale : ContinuousOn (fun t => 1 + δ / sieveParameter D t) (Icc w z) :=
    continuousOn_const.add (continuousOn_const.div hu (fun t ht => by linarith [huc t ht]))
  have hi := hS.add (hfc.mul hscale).integrableOn_Icc
  have hfactor : ContinuousOn (fun t => childAuxiliaryWeight δ (sieveParameter D t) /
      (sieveParameter D t - 1) * (Real.log D * logSieveKernel t)) (Icc w z) :=
    (((continuousOn_childAuxiliaryWeight δ).comp hu huc).div hu1
      (fun t ht => by linarith [huc t ht])).mul
        (continuousOn_const.mul (continuousOn_logSieveKernel w z hw))
  apply (hi.mul_continuousOn hfactor isCompact_Icc).congr_fun _ measurableSet_Icc
  intro t _
  dsimp [auxiliaryPrimeSlope]
  ring

end Chen.LinearSieve
