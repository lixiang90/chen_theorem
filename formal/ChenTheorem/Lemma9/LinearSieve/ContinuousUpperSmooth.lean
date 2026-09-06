import ChenTheorem.Lemma9.LinearSieve.ContinuousErrorRegularity

open Set MeasureTheory Filter
open scoped Topology

namespace Chen.LinearSieve

theorem continuous_clamped_lowerContinuousError :
    Continuous (fun s : ℝ => lowerContinuousError (max (s - 1) 2)) :=
  continuousOn_lowerContinuousError.comp_continuous
    ((continuous_id.sub continuous_const).max continuous_const)
    (fun s => le_max_right (s - 1) 2)

/-- The left and right weighted derivatives agree at the upper sieve's
joining point, because the lower error at two equals one. -/
theorem hasDerivAt_mul_upperContinuousError_three :
    HasDerivAt (fun s => s * upperContinuousError s) (-1) 3 := by
  let H : ℝ → ℝ := fun s => lowerContinuousError (max (s - 1) 2)
  have hH : Continuous H := continuous_clamped_lowerContinuousError
  have hi : HasDerivAt (fun s => ∫ t in (3 : ℝ)..s, H t) (H 3) 3 :=
    intervalIntegral.integral_hasDerivAt_right (hH.intervalIntegrable 3 3)
      hH.stronglyMeasurable.stronglyMeasurableAtFilter hH.continuousAt
  have hright0 : HasDerivAt (fun s => 3 * upperContinuousError 3 - ∫ t in (3 : ℝ)..s, H t) (-1) 3 := by
    convert! hi.const_sub (3 * upperContinuousError 3) using 1
    norm_num [H, lowerContinuousError_two]
  have heqright : ∀ s ∈ Ici (3 : ℝ),
      s * upperContinuousError s = 3 * upperContinuousError 3 - ∫ t in (3 : ℝ)..s, H t := by
    intro s hs
    have hc : ContinuousOn (fun t => t * upperContinuousError t) (Icc 3 s) :=
      continuousOn_id.mul (continuousOn_upperContinuousError.mono
        (fun t ht => by change 1 < t; linarith [ht.1]))
    have hd : ∀ t ∈ Ioo (3 : ℝ) s,
        HasDerivAt (fun t => t * upperContinuousError t) (-H t) t := by
      intro t ht
      dsimp [H]
      rw [max_eq_left (by linarith [ht.1])]
      exact hasDerivAt_mul_upperContinuousError t ht.1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hc hd
      (hH.intervalIntegrable 3 s).neg
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hright : HasDerivWithinAt (fun s => s * upperContinuousError s) (-1) (Ici 3) 3 :=
    hright0.hasDerivWithinAt.congr heqright (heqright 3 (by norm_num))
  have hleft0 : HasDerivAt (fun s : ℝ => linearSieveInitialConstant - s) (-1) 3 := by
    convert! (hasDerivAt_id (3 : ℝ)).const_sub linearSieveInitialConstant using 1
  have heqleft : ∀ s ∈ Icc (2 : ℝ) 3, s * upperContinuousError s = linearSieveInitialConstant - s :=
    fun s hs => mul_upperContinuousError_initial s (by linarith [hs.1]) hs.2
  have hleft : HasDerivWithinAt (fun s => s * upperContinuousError s) (-1) (Icc 2 3) 3 :=
    hleft0.hasDerivWithinAt.congr heqleft (heqleft 3 (by norm_num))
  have hunion : Icc (2 : ℝ) 3 ∪ Ici 3 = Ici 2 := by
    ext s
    simp only [mem_union, mem_Icc, mem_Ici]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hs : s ≤ 3
      · exact Or.inl ⟨h, hs⟩
      · exact Or.inr (by linarith)
  have h := hleft.union hright
  rw [hunion] at h
  exact h.hasDerivAt (Ici_mem_nhds (by norm_num : (2 : ℝ) < 3))

theorem hasDerivAt_mul_upperContinuousError_all (s : ℝ) (hs : 1 < s) :
    HasDerivAt (fun t => t * upperContinuousError t)
      (-lowerContinuousError (max (s - 1) 2)) s := by
  rcases lt_trichotomy s 3 with hlt | rfl | hgt
  · have heq : (fun t => t * upperContinuousError t) =ᶠ[𝓝 s]
        (fun t => linearSieveInitialConstant - t) := by
      filter_upwards [Ioo_mem_nhds hs hlt] with t ht
      exact mul_upperContinuousError_initial t ht.1 ht.2.le
    have h := (hasDerivAt_id s).const_sub linearSieveInitialConstant
    have hd := h.congr_of_eventuallyEq heq
    simpa only [max_eq_right (show s - 1 ≤ 2 by linarith), lowerContinuousError_two] using hd
  · convert! hasDerivAt_mul_upperContinuousError_three using 1
    norm_num [lowerContinuousError_two]
  · rw [max_eq_left (by linarith)]
    exact hasDerivAt_mul_upperContinuousError s hgt

theorem hasDerivAt_upperContinuousError_all (s : ℝ) (hs : 1 < s) :
    HasDerivAt upperContinuousError
      (-(lowerContinuousError (max (s - 1) 2) + upperContinuousError s) / s) s := by
  have hs0 : s ≠ 0 := by linarith
  have h := (hasDerivAt_mul_upperContinuousError_all s hs).div (hasDerivAt_id s) hs0
  have heq : (fun t => t * upperContinuousError t / t) =ᶠ[𝓝 s] upperContinuousError := by
    filter_upwards [eventually_ne_nhds hs0] with t ht
    exact mul_div_cancel_left₀ _ ht
  apply (h.congr_of_eventuallyEq heq.symm).congr_deriv
  dsimp only [id_eq]
  field_simp
  ring

theorem continuousOn_deriv_upperContinuousError_all :
    ContinuousOn (deriv upperContinuousError) (Ioi 1) := by
  apply ((continuous_clamped_lowerContinuousError.continuousOn.add continuousOn_upperContinuousError).neg.div
    continuousOn_id (fun s hs => by change s ≠ 0; linarith [show 1 < s from hs])).congr
  intro s hs
  exact (hasDerivAt_upperContinuousError_all s hs).deriv

theorem deriv_upperContinuousError_nonpos_all (s : ℝ) (hs : 1 < s) :
    deriv upperContinuousError s ≤ 0 := by
  rw [(hasDerivAt_upperContinuousError_all s hs).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_nonneg
    (lowerContinuousError_bounds _ (le_max_right _ _)).1
    (upperContinuousError_bounds s hs).1)) (by linarith)

end Chen.LinearSieve
