import ChenTheorem.Lemma9.LinearSieve.ContinuousUpperSmooth

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The auxiliary upper error is the negative derivative of the upper error
on its analytic domain. Its weighted delay equation has weight `s²`. -/
noncomputable def upperAuxiliaryError (s : ℝ) : ℝ :=
  (lowerContinuousError (max (s - 1) 2) + upperContinuousError s) / s

/-- The lower auxiliary error extends its derivative formula across two by
the initial value `s² * error = 2 * linearSieveInitialConstant`. -/
noncomputable def lowerAuxiliaryError (s : ℝ) : ℝ :=
  if s ≤ 2 then 2 * linearSieveInitialConstant / s ^ 2
  else (upperContinuousError (s - 1) + lowerContinuousError s) / s

theorem upperAuxiliaryError_eq_neg_deriv (s : ℝ) (hs : 1 < s) :
    upperAuxiliaryError s = -deriv upperContinuousError s := by
  rw [(hasDerivAt_upperContinuousError_all s hs).deriv]
  simp only [upperAuxiliaryError]
  ring

theorem lowerAuxiliaryError_eq_neg_deriv (s : ℝ) (hs : 2 < s) :
    lowerAuxiliaryError s = -deriv lowerContinuousError s := by
  rw [(hasDerivAt_lowerContinuousError s hs).deriv]
  simp only [lowerAuxiliaryError, if_neg (not_le.mpr hs)]
  ring

theorem upperAuxiliaryError_nonneg (s : ℝ) (hs : 1 < s) :
    0 ≤ upperAuxiliaryError s := by
  rw [upperAuxiliaryError_eq_neg_deriv s hs]
  exact neg_nonneg.mpr (deriv_upperContinuousError_nonpos_all s hs)

theorem lowerAuxiliaryError_nonneg (s : ℝ) (_hs : 0 < s) :
    0 ≤ lowerAuxiliaryError s := by
  by_cases hs2 : s ≤ 2
  · simp only [lowerAuxiliaryError, if_pos hs2]
    apply div_nonneg _ (sq_nonneg s)
    have h := linearSieveInitialConstant_ge_three
    positivity
  · rw [lowerAuxiliaryError_eq_neg_deriv s (lt_of_not_ge hs2)]
    exact neg_nonneg.mpr (deriv_lowerContinuousError_nonpos s (lt_of_not_ge hs2))

theorem upperAuxiliaryError_initial (s : ℝ) (hs : 1 < s) (hs3 : s ≤ 3) :
    upperAuxiliaryError s = linearSieveInitialConstant / s ^ 2 := by
  rw [upperAuxiliaryError, max_eq_right (by linarith), lowerContinuousError_two,
    upperContinuousError_initial s hs hs3]
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

theorem lowerAuxiliaryError_initial (s : ℝ) (hs : s ≤ 2) :
    lowerAuxiliaryError s = 2 * linearSieveInitialConstant / s ^ 2 := by
  simp [lowerAuxiliaryError, hs]

theorem continuousOn_upperAuxiliaryError :
    ContinuousOn upperAuxiliaryError (Ioi 1) := by
  apply continuousOn_deriv_upperContinuousError_all.neg.congr
  intro s hs
  exact upperAuxiliaryError_eq_neg_deriv s hs

theorem continuousOn_lowerAuxiliaryError_above_two :
    ContinuousOn lowerAuxiliaryError (Ioi 2) := by
  apply continuousOn_deriv_lowerContinuousError.neg.congr
  intro s hs
  exact lowerAuxiliaryError_eq_neg_deriv s hs

theorem hasDerivAt_sq_mul_upperAuxiliaryError (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun t => t ^ 2 * upperAuxiliaryError t)
      (-s * lowerAuxiliaryError (s - 1)) s := by
  have hs0 : s ≠ 0 := by linarith
  have hshift := (hasDerivAt_lowerContinuousError (s - 1) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hd := (hasDerivAt_id s).mul
    (hshift.add (hasDerivAt_upperContinuousError s hs))
  have heq : (fun t => t ^ 2 * upperAuxiliaryError t) =ᶠ[𝓝 s]
      (fun t => t * (lowerContinuousError (t - 1) + upperContinuousError t)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    change 3 < t at ht
    dsimp [upperAuxiliaryError]
    rw [max_eq_left (by linarith : 2 ≤ t - 1)]
    have ht0 : t ≠ 0 := by linarith [show 3 < t from ht]
    field_simp
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  dsimp only [Function.comp_def, id_eq, Pi.add_apply]
  rw [lowerAuxiliaryError, if_neg (by linarith : ¬s - 1 ≤ 2)]
  field_simp
  ring

theorem hasDerivAt_sq_mul_lowerAuxiliaryError (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t => t ^ 2 * lowerAuxiliaryError t)
      (-s * upperAuxiliaryError (s - 1)) s := by
  have hs0 : s ≠ 0 := by linarith
  have hshift := (hasDerivAt_upperContinuousError_all (s - 1) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hd := (hasDerivAt_id s).mul
    (hshift.add (hasDerivAt_lowerContinuousError s hs))
  have heq : (fun t => t ^ 2 * lowerAuxiliaryError t) =ᶠ[𝓝 s]
      (fun t => t * (upperContinuousError (t - 1) + lowerContinuousError t)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    change 2 < t at ht
    dsimp [lowerAuxiliaryError]
    rw [if_neg (by linarith : ¬t ≤ 2)]
    have ht0 : t ≠ 0 := by linarith [show 2 < t from ht]
    field_simp
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  dsimp only [Function.comp_def, id_eq, Pi.add_apply, upperAuxiliaryError]
  field_simp
  ring

theorem lowerAuxiliaryError_first_interval (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    lowerAuxiliaryError s = linearSieveInitialConstant *
      (s / (s - 1) - Real.log (s - 1)) / s ^ 2 := by
  rcases eq_or_lt_of_le hs with rfl | hs2
  · norm_num [lowerAuxiliaryError]
    ring
  · rw [lowerAuxiliaryError, if_neg (not_le.mpr hs2),
      upperContinuousError_initial (s - 1) (by linarith) (by linarith),
      lowerContinuousError_initial s hs hs4]
    have hs0 : s ≠ 0 := by linarith
    have hs1 : s - 1 ≠ 0 := by linarith
    field_simp
    ring

theorem continuousAt_lowerAuxiliaryError_two : ContinuousAt lowerAuxiliaryError 2 := by
  let f : ℝ → ℝ := fun s => 2 * linearSieveInitialConstant / s ^ 2
  let g : ℝ → ℝ := fun s => linearSieveInitialConstant *
    (s / (s - 1) - Real.log (s - 1)) / s ^ 2
  have hf : ContinuousAt f 2 := by dsimp [f]; fun_prop (disch := norm_num)
  have hg : ContinuousAt g 2 := by dsimp [g]; fun_prop (disch := norm_num)
  have hl : ContinuousWithinAt lowerAuxiliaryError (Icc 1 2) 2 :=
    hf.continuousWithinAt.congr
      (fun s hs => lowerAuxiliaryError_initial s hs.2)
      (lowerAuxiliaryError_initial 2 le_rfl)
  have hr : ContinuousWithinAt lowerAuxiliaryError (Icc 2 3) 2 :=
    hg.continuousWithinAt.congr
      (fun s hs => lowerAuxiliaryError_first_interval s hs.1 (by linarith [hs.2]))
      (lowerAuxiliaryError_first_interval 2 le_rfl (by norm_num))
  have h := hl.union hr
  have hu : Icc (1 : ℝ) 2 ∪ Icc 2 3 = Icc 1 3 := by
    ext s
    simp only [mem_union, mem_Icc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
    · intro h
      by_cases hs : s ≤ 2
      · exact Or.inl ⟨h.1, hs⟩
      · exact Or.inr ⟨by linarith, h.2⟩
  rw [hu] at h
  exact h.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

theorem continuousOn_lowerAuxiliaryError : ContinuousOn lowerAuxiliaryError (Ioi 0) := by
  intro s hs
  rcases lt_trichotomy s 2 with hlt | rfl | hgt
  · have hs0 : s ≠ 0 := ne_of_gt hs
    have hc : ContinuousAt (fun t : ℝ => 2 * linearSieveInitialConstant / t ^ 2) s := by
      fun_prop (disch := simp [hs0])
    have heq : lowerAuxiliaryError =ᶠ[𝓝 s]
        (fun t : ℝ => 2 * linearSieveInitialConstant / t ^ 2) := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      exact lowerAuxiliaryError_initial t (le_of_lt ht)
    exact (hc.congr_of_eventuallyEq heq).continuousWithinAt
  · exact continuousAt_lowerAuxiliaryError_two.continuousWithinAt
  · exact ((continuousOn_lowerAuxiliaryError_above_two s hgt).continuousAt
      (Ioi_mem_nhds hgt)).continuousWithinAt

theorem antitoneOn_sq_mul_upperAuxiliaryError_above_three :
    AntitoneOn (fun s => s ^ 2 * upperAuxiliaryError s) (Ici 3) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3)
    (continuousOn_id.pow 2 |>.mul (continuousOn_upperAuxiliaryError.mono
      (fun s hs => by change 1 < s; linarith [show 3 ≤ s from hs])))
    (f' := fun s => -s * lowerAuxiliaryError (s - 1))
  · intro s hs
    rw [interior_Ici] at hs
    exact (hasDerivAt_sq_mul_upperAuxiliaryError s hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [show 3 < s from hs])
      (lowerAuxiliaryError_nonneg (s - 1) (by linarith [show 3 < s from hs]))

theorem antitoneOn_sq_mul_lowerAuxiliaryError_above_two :
    AntitoneOn (fun s => s ^ 2 * lowerAuxiliaryError s) (Ici 2) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
    (continuousOn_id.pow 2 |>.mul (continuousOn_lowerAuxiliaryError.mono
      (fun s hs => by change 0 < s; linarith [show 2 ≤ s from hs])))
    (f' := fun s => -s * upperAuxiliaryError (s - 1))
  · intro s hs
    rw [interior_Ici] at hs
    exact (hasDerivAt_sq_mul_lowerAuxiliaryError s hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [show 2 < s from hs])
      (upperAuxiliaryError_nonneg (s - 1) (by linarith [show 2 < s from hs]))

theorem sq_mul_upperAuxiliaryError_initial (s : ℝ) (hs : 1 < s) (hs3 : s ≤ 3) :
    s ^ 2 * upperAuxiliaryError s = linearSieveInitialConstant := by
  rw [upperAuxiliaryError_initial s hs hs3]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 (by linarith))

theorem sq_mul_lowerAuxiliaryError_initial (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 2) :
    s ^ 2 * lowerAuxiliaryError s = 2 * linearSieveInitialConstant := by
  rw [lowerAuxiliaryError_initial s hs2]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hs))

theorem antitoneOn_sq_mul_upperAuxiliaryError :
    AntitoneOn (fun s => s ^ 2 * upperAuxiliaryError s) (Ioi 1) := by
  intro s hs t ht hst
  dsimp only
  by_cases hs3 : 3 ≤ s
  · exact antitoneOn_sq_mul_upperAuxiliaryError_above_three hs3 (hs3.trans hst) hst
  · by_cases ht3 : t ≤ 3
    · rw [sq_mul_upperAuxiliaryError_initial s hs (le_of_not_ge hs3),
        sq_mul_upperAuxiliaryError_initial t ht ht3]
    · have h := antitoneOn_sq_mul_upperAuxiliaryError_above_three
        (show (3 : ℝ) ∈ Ici 3 by simp) (le_of_not_ge ht3) (le_of_not_ge ht3)
      dsimp only at h ⊢
      rw [sq_mul_upperAuxiliaryError_initial 3 (by norm_num) le_rfl] at h
      rwa [sq_mul_upperAuxiliaryError_initial s hs (le_of_not_ge hs3)]

theorem antitoneOn_sq_mul_lowerAuxiliaryError :
    AntitoneOn (fun s => s ^ 2 * lowerAuxiliaryError s) (Ioi 0) := by
  intro s hs t ht hst
  dsimp only
  by_cases hs2 : 2 ≤ s
  · exact antitoneOn_sq_mul_lowerAuxiliaryError_above_two hs2 (hs2.trans hst) hst
  · by_cases ht2 : t ≤ 2
    · rw [sq_mul_lowerAuxiliaryError_initial s hs (le_of_not_ge hs2),
        sq_mul_lowerAuxiliaryError_initial t ht ht2]
    · have h := antitoneOn_sq_mul_lowerAuxiliaryError_above_two
        (show (2 : ℝ) ∈ Ici 2 by simp) (le_of_not_ge ht2) (le_of_not_ge ht2)
      dsimp only at h ⊢
      rw [sq_mul_lowerAuxiliaryError_initial 2 (by norm_num) le_rfl] at h
      rwa [sq_mul_lowerAuxiliaryError_initial s hs (le_of_not_ge hs2)]

end Chen.LinearSieve
