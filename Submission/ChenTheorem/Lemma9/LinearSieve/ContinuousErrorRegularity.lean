import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousFunctions

set_option autoImplicit true
open Set

namespace Chen.LinearSieve

theorem hasDerivAt_upperContinuousError (s : ℝ) (hs : 3 < s) :
    HasDerivAt upperContinuousError
      (-(lowerContinuousError (s - 1) + upperContinuousError s) / s) s := by
  have hs0 : s ≠ 0 := by linarith
  have h := (hasDerivAt_mul_upperContinuousError s hs).div (hasDerivAt_id s) hs0
  have heq : (fun t => t * upperContinuousError t / t) =ᶠ[nhds s] upperContinuousError := by
    filter_upwards [eventually_ne_nhds hs0] with t ht
    exact mul_div_cancel_left₀ _ ht
  apply (h.congr_of_eventuallyEq heq.symm).congr_deriv
  dsimp only [id_eq]
  field_simp
  ring

theorem hasDerivAt_lowerContinuousError (s : ℝ) (hs : 2 < s) :
    HasDerivAt lowerContinuousError
      (-(upperContinuousError (s - 1) + lowerContinuousError s) / s) s := by
  have hs0 : s ≠ 0 := by linarith
  have h := (hasDerivAt_mul_lowerContinuousError s hs).div (hasDerivAt_id s) hs0
  have heq : (fun t => t * lowerContinuousError t / t) =ᶠ[nhds s] lowerContinuousError := by
    filter_upwards [eventually_ne_nhds hs0] with t ht
    exact mul_div_cancel_left₀ _ ht
  apply (h.congr_of_eventuallyEq heq.symm).congr_deriv
  dsimp only [id_eq]
  field_simp
  ring

theorem antitoneOn_upperContinuousError : AntitoneOn upperContinuousError (Ioi 1) := by
  intro s hs t ht hst
  have hw := antitoneOn_mul_upperContinuousError hs ht hst
  have ht0 := (upperContinuousError_bounds t ht).1
  have hspos : 0 < s := by linarith [show 1 < s from hs]
  dsimp only at hw
  nlinarith

theorem antitoneOn_lowerContinuousError : AntitoneOn lowerContinuousError (Ici 2) := by
  intro s hs t ht hst
  have hw := antitoneOn_mul_lowerContinuousError hs ht hst
  have ht0 := (lowerContinuousError_bounds t ht).1
  have hspos : 0 < s := by linarith [show 2 ≤ s from hs]
  dsimp only at hw
  nlinarith

theorem antitoneOn_mul_shift_upperContinuousError :
    AntitoneOn (fun s => s * upperContinuousError (s - 1)) (Ioi 2) := by
  intro s hs t ht hst
  have hs1 : s - 1 ∈ Ioi (1 : ℝ) := by change 1 < s - 1; linarith [show 2 < s from hs]
  have ht1 : t - 1 ∈ Ioi (1 : ℝ) := by change 1 < t - 1; linarith [show 2 < t from ht]
  have hw := antitoneOn_mul_upperContinuousError hs1 ht1 (sub_le_sub_right hst 1)
  have hf := antitoneOn_upperContinuousError hs1 ht1 (sub_le_sub_right hst 1)
  dsimp only at hw hf ⊢
  nlinarith

theorem antitoneOn_mul_shift_lowerContinuousError :
    AntitoneOn (fun s => s * lowerContinuousError (s - 1)) (Ici 3) := by
  intro s hs t ht hst
  have hs2 : s - 1 ∈ Ici (2 : ℝ) := by change 2 ≤ s - 1; linarith [show 3 ≤ s from hs]
  have ht2 : t - 1 ∈ Ici (2 : ℝ) := by change 2 ≤ t - 1; linarith [show 3 ≤ t from ht]
  have hw := antitoneOn_mul_lowerContinuousError hs2 ht2 (sub_le_sub_right hst 1)
  have hf := antitoneOn_lowerContinuousError hs2 ht2 (sub_le_sub_right hst 1)
  dsimp only at hw hf ⊢
  nlinarith

theorem continuousOn_deriv_upperContinuousError :
    ContinuousOn (deriv upperContinuousError) (Ioi 3) := by
  have hl : ContinuousOn (fun s => lowerContinuousError (s - 1)) (Ioi 3) :=
    continuousOn_lowerContinuousError.comp (continuousOn_id.sub continuousOn_const)
      (fun s hs => by change 2 ≤ s - 1; linarith [show 3 < s from hs])
  have hu := continuousOn_upperContinuousError.mono
    (show Ioi (3 : ℝ) ⊆ Ioi 1 from fun s hs => by change 1 < s; linarith [show 3 < s from hs])
  apply ((hl.add hu).neg.div continuousOn_id
    (fun s hs => by change s ≠ 0; linarith [show 3 < s from hs])).congr
  intro s hs
  exact (hasDerivAt_upperContinuousError s hs).deriv

theorem continuousOn_deriv_lowerContinuousError :
    ContinuousOn (deriv lowerContinuousError) (Ioi 2) := by
  have hu : ContinuousOn (fun s => upperContinuousError (s - 1)) (Ioi 2) :=
    continuousOn_upperContinuousError.comp (continuousOn_id.sub continuousOn_const)
      (fun s hs => by change 1 < s - 1; linarith [show 2 < s from hs])
  have hl := continuousOn_lowerContinuousError.mono (Ioi_subset_Ici_self)
  apply ((hu.add hl).neg.div continuousOn_id
    (fun s hs => by change s ≠ 0; linarith [show 2 < s from hs])).congr
  intro s hs
  exact (hasDerivAt_lowerContinuousError s hs).deriv

theorem deriv_upperContinuousError_nonpos (s : ℝ) (hs : 3 < s) :
    deriv upperContinuousError s ≤ 0 := by
  rw [(hasDerivAt_upperContinuousError s hs).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_nonneg
    (lowerContinuousError_bounds (s - 1) (by linarith)).1
    (upperContinuousError_bounds s (by linarith)).1)) (by linarith)

theorem deriv_lowerContinuousError_nonpos (s : ℝ) (hs : 2 < s) :
    deriv lowerContinuousError s ≤ 0 := by
  rw [(hasDerivAt_lowerContinuousError s hs).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_nonneg
    (upperContinuousError_bounds (s - 1) (by linarith)).1
    (lowerContinuousError_bounds s hs.le).1)) (by linarith)

end Chen.LinearSieve
