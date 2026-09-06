import ChenTheorem.Lemma9.LinearSieve.AuxiliaryLevelError

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

noncomputable def upperAuxiliaryLeftSource (s : ℝ) : ℝ :=
  if 3 < s then lowerAuxiliaryError (s - 1) else 0

noncomputable def lowerAuxiliaryLeftSource (s : ℝ) : ℝ :=
  if 2 < s then upperAuxiliaryError (s - 1) else 0

theorem upperAuxiliaryLeftSource_nonneg (s : ℝ) : 0 ≤ upperAuxiliaryLeftSource s := by
  unfold upperAuxiliaryLeftSource
  split_ifs with hs
  · exact lowerAuxiliaryError_nonneg _ (by linarith)
  · exact le_rfl

theorem lowerAuxiliaryLeftSource_nonneg (s : ℝ) : 0 ≤ lowerAuxiliaryLeftSource s := by
  unfold lowerAuxiliaryLeftSource
  split_ifs with hs
  · exact upperAuxiliaryError_nonneg _ (by linarith)
  · exact le_rfl

theorem hasDerivWithinAt_sq_mul_upperAuxiliaryError_left (s : ℝ) (hs : 1 < s) :
    HasDerivWithinAt (fun t => t ^ 2 * upperAuxiliaryError t)
      (-s * upperAuxiliaryLeftSource s) (Iio s) s := by
  by_cases hc : 3 < s
  · simpa only [upperAuxiliaryLeftSource, if_pos hc] using
      (hasDerivAt_sq_mul_upperAuxiliaryError s hc).hasDerivWithinAt (s := Iio s)
  · simp only [upperAuxiliaryLeftSource, if_neg hc, mul_zero]
    apply (hasDerivWithinAt_const s (Iio s) linearSieveInitialConstant).congr_of_eventuallyEq
    · filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ht hts
      exact sq_mul_upperAuxiliaryError_initial t ht (hts.le.trans (le_of_not_gt hc))
    · exact sq_mul_upperAuxiliaryError_initial s hs (le_of_not_gt hc)

theorem hasDerivWithinAt_sq_mul_lowerAuxiliaryError_left (s : ℝ) (hs : 0 < s) :
    HasDerivWithinAt (fun t => t ^ 2 * lowerAuxiliaryError t)
      (-s * lowerAuxiliaryLeftSource s) (Iio s) s := by
  by_cases hc : 2 < s
  · simpa only [lowerAuxiliaryLeftSource, if_pos hc] using
      (hasDerivAt_sq_mul_lowerAuxiliaryError s hc).hasDerivWithinAt (s := Iio s)
  · simp only [lowerAuxiliaryLeftSource, if_neg hc, mul_zero]
    apply (hasDerivWithinAt_const s (Iio s) (2 * linearSieveInitialConstant)).congr_of_eventuallyEq
    · filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ht hts
      exact sq_mul_lowerAuxiliaryError_initial t ht (hts.le.trans (le_of_not_gt hc))
    · exact sq_mul_lowerAuxiliaryError_initial s hs (le_of_not_gt hc)

theorem hasDerivWithinAt_of_sq_mul_left (H : ℝ → ℝ) (s S : ℝ) (hs : 0 < s)
    (h : HasDerivWithinAt (fun t => t ^ 2 * H t) (-s * S) (Iio s) s) :
    HasDerivWithinAt H (-(S + 2 * H s) / s) (Iio s) s := by
  have hquot := h.div ((hasDerivAt_id s).pow 2).hasDerivWithinAt (pow_ne_zero 2 hs.ne')
  have heq : (fun t => t ^ 2 * H t / t ^ 2) =ᶠ[𝓝[Iio s] s] H := by
    filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds] with t ht
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 ht.ne')
  have heqs : s ^ 2 * H s / s ^ 2 = H s := mul_div_cancel_left₀ _ (pow_ne_zero 2 hs.ne')
  apply (hquot.congr_of_eventuallyEq heq.symm heqs.symm).congr_deriv
  dsimp only [id_eq, Pi.pow_apply]
  field_simp
  ring

theorem hasDerivWithinAt_upperAuxiliaryError_left (s : ℝ) (hs : 1 < s) :
    HasDerivWithinAt upperAuxiliaryError
      (-(upperAuxiliaryLeftSource s + 2 * upperAuxiliaryError s) / s) (Iio s) s :=
  hasDerivWithinAt_of_sq_mul_left _ s _ (by linarith)
    (hasDerivWithinAt_sq_mul_upperAuxiliaryError_left s hs)

theorem hasDerivWithinAt_lowerAuxiliaryError_left (s : ℝ) (hs : 0 < s) :
    HasDerivWithinAt lowerAuxiliaryError
      (-(lowerAuxiliaryLeftSource s + 2 * lowerAuxiliaryError s) / s) (Iio s) s :=
  hasDerivWithinAt_of_sq_mul_left _ s _ hs
    (hasDerivWithinAt_sq_mul_lowerAuxiliaryError_left s hs)

/-- A continuous extension avoids using the unextended upper series at one
when the lower jump source is represented by a clamped function. -/
noncomputable def upperAuxiliaryExtension (s : ℝ) : ℝ :=
  if s ≤ 2 then linearSieveInitialConstant / s ^ 2 else upperAuxiliaryError s

theorem upperAuxiliaryExtension_eq (s : ℝ) (hs : 1 < s) :
    upperAuxiliaryExtension s = upperAuxiliaryError s := by
  unfold upperAuxiliaryExtension
  split_ifs with hs2
  · exact (upperAuxiliaryError_initial s hs (by linarith)).symm
  · rfl

theorem continuousOn_upperAuxiliaryExtension : ContinuousOn upperAuxiliaryExtension (Ioi 0) := by
  apply ContinuousOn.if
  · intro s hs
    have heq : s = 2 := by
      have hm := hs.2
      change s ∈ frontier (Iic (2 : ℝ)) at hm
      simpa only [frontier_Iic, mem_singleton_iff] using hm
    subst s
    exact (upperAuxiliaryError_initial 2 (by norm_num) (by norm_num)).symm
  · apply continuousOn_const.div (continuousOn_id.pow 2)
    intro s hs
    exact pow_ne_zero 2 (ne_of_gt hs.1)
  · apply continuousOn_upperAuxiliaryError.mono
    intro s hs
    have hs2 : 2 ≤ s := by
      have hm := hs.2
      simp only [not_le] at hm
      change s ∈ closure (Ioi (2 : ℝ)) at hm
      simpa only [closure_Ioi, mem_Ici] using hm
    change 1 < s
    linarith

theorem integrableOn_upperAuxiliaryLeftSource_comp (a b : ℝ) (u : ℝ → ℝ)
    (huc : ContinuousOn u (Icc a b)) (hum : Measurable u) :
    IntegrableOn (fun t => upperAuxiliaryLeftSource (u t)) (Icc a b) := by
  have hc : ContinuousOn (fun t => lowerAuxiliaryError (max (u t) 3 - 1)) (Icc a b) :=
    continuousOn_lowerAuxiliaryError.comp ((huc.sup continuousOn_const).sub continuousOn_const)
      (fun t _ => by change 0 < max (u t) 3 - 1; linarith [le_max_right (u t) 3])
  have hi : IntegrableOn ({t | 3 < u t}.indicator
      (fun t => lowerAuxiliaryError (max (u t) 3 - 1))) (Icc a b) :=
    hc.integrableOn_Icc.indicator (measurableSet_lt measurable_const hum)
  apply hi.congr_fun _ measurableSet_Icc
  intro t _
  by_cases ht : 3 < u t
  · simp only [indicator_of_mem (show t ∈ {t | 3 < u t} from ht), max_eq_left ht.le,
      upperAuxiliaryLeftSource, if_pos ht]
  · simp only [indicator_of_notMem (show t ∉ {t | 3 < u t} from ht),
      upperAuxiliaryLeftSource, if_neg ht]

theorem integrableOn_lowerAuxiliaryLeftSource_comp (a b : ℝ) (u : ℝ → ℝ)
    (huc : ContinuousOn u (Icc a b)) (hum : Measurable u) :
    IntegrableOn (fun t => lowerAuxiliaryLeftSource (u t)) (Icc a b) := by
  have hc : ContinuousOn (fun t => upperAuxiliaryExtension (max (u t) 2 - 1)) (Icc a b) :=
    continuousOn_upperAuxiliaryExtension.comp ((huc.sup continuousOn_const).sub continuousOn_const)
      (fun t _ => by change 0 < max (u t) 2 - 1; linarith [le_max_right (u t) 2])
  have hi : IntegrableOn ({t | 2 < u t}.indicator
      (fun t => upperAuxiliaryExtension (max (u t) 2 - 1))) (Icc a b) :=
    hc.integrableOn_Icc.indicator (measurableSet_lt measurable_const hum)
  apply hi.congr_fun _ measurableSet_Icc
  intro t _
  by_cases ht : 2 < u t
  · simp only [indicator_of_mem (show t ∈ {t | 2 < u t} from ht), max_eq_left ht.le,
      lowerAuxiliaryLeftSource, if_pos ht,
      upperAuxiliaryExtension_eq (u t - 1) (by linarith)]
  · simp only [indicator_of_notMem (show t ∉ {t | 2 < u t} from ht),
      lowerAuxiliaryLeftSource, if_neg ht]

end Chen.LinearSieve
