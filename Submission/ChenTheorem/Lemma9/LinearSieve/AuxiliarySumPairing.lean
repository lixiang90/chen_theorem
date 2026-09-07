import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryLowerStep
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit true

open Set MeasureTheory Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The positive scalar solution obtained by adding the two auxiliary errors. -/
noncomputable def auxiliaryErrorSum (s : ℝ) : ℝ :=
  upperAuxiliaryError s + lowerAuxiliaryError s

/-- The polynomial solution of the adjoint equation for parameters `(2, 1)`. -/
noncomputable def auxiliaryAdjoint (s : ℝ) : ℝ := s ^ 2 - 2 * s + 1 / 2

theorem auxiliaryErrorSum_pos (s : ℝ) (hs : 1 < s) :
    0 < auxiliaryErrorSum s :=
  add_pos (upperAuxiliaryError_pos s hs) (lowerAuxiliaryError_pos s (by linarith))

theorem continuousOn_auxiliaryErrorSum : ContinuousOn auxiliaryErrorSum (Ioi 1) :=
  continuousOn_upperAuxiliaryError.add
    (continuousOn_lowerAuxiliaryError.mono (by intro s hs; change 0 < s; linarith [show 1 < s from hs]))

theorem antitoneOn_auxiliaryErrorSum : AntitoneOn auxiliaryErrorSum (Ioi 1) := by
  intro s hs t ht hst
  exact _root_.add_le_add (antitoneOn_upperAuxiliaryError hs ht hst)
    (antitoneOn_lowerAuxiliaryError (by change 0 < s; linarith [show 1 < s from hs])
      (by change 0 < t; linarith [show 1 < t from ht]) hst)

theorem hasDerivAt_continuousErrorSum (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t => upperContinuousError t + lowerContinuousError t)
      (-auxiliaryErrorSum s) s := by
  have hu := hasDerivAt_upperContinuousError_all s (by linarith)
  have hl := hasDerivAt_lowerContinuousError s hs
  have h := hu.add hl
  rw [← hu.deriv, ← hl.deriv] at h
  rw [← neg_neg (deriv upperContinuousError s),
    ← upperAuxiliaryError_eq_neg_deriv s (by linarith),
    ← neg_neg (deriv lowerContinuousError s),
    ← lowerAuxiliaryError_eq_neg_deriv s hs] at h
  exact h.congr_deriv (by dsimp [auxiliaryErrorSum]; ring)

theorem mul_auxiliaryErrorSum (s : ℝ) (hs : 3 < s) :
    s * auxiliaryErrorSum s =
      upperContinuousError s + lowerContinuousError s +
        (upperContinuousError (s - 1) + lowerContinuousError (s - 1)) := by
  unfold auxiliaryErrorSum upperAuxiliaryError lowerAuxiliaryError
  rw [max_eq_left (by linarith), if_neg (by linarith : ¬s ≤ 2)]
  field_simp
  ring

theorem hasDerivAt_sq_mul_auxiliaryErrorSum (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun t => t ^ 2 * auxiliaryErrorSum t)
      (-s * auxiliaryErrorSum (s - 1)) s := by
  convert! (hasDerivAt_sq_mul_upperAuxiliaryError s hs).add
    (hasDerivAt_sq_mul_lowerAuxiliaryError s (by linarith)) using 1 <;>
    simp only [auxiliaryErrorSum, Pi.add_def, ← mul_add]
  ring

theorem hasDerivAt_auxiliaryErrorSum (s : ℝ) (hs : 3 < s) :
    HasDerivAt auxiliaryErrorSum
      (-(2 * auxiliaryErrorSum s + auxiliaryErrorSum (s - 1)) / s) s := by
  have hs0 : s ≠ 0 := by linarith
  have hd := (hasDerivAt_sq_mul_auxiliaryErrorSum s hs).div
    ((hasDerivAt_id s).pow 2) (pow_ne_zero 2 hs0)
  have he : (fun t => t ^ 2 * auxiliaryErrorSum t / t ^ 2) =ᶠ[𝓝 s]
      auxiliaryErrorSum := by
    filter_upwards [eventually_ne_nhds hs0] with t ht
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 ht)
  apply (hd.congr_of_eventuallyEq he.symm).congr_deriv
  dsimp
  field_simp
  ring

theorem hasDerivAt_auxiliaryAdjoint (s : ℝ) :
    HasDerivAt auxiliaryAdjoint (2 * s - 2) s := by
  apply ((((hasDerivAt_id s).pow 2).sub
    ((hasDerivAt_id s).const_mul 2)).add_const (1 / 2)).congr_deriv
  simp

theorem auxiliaryAdjoint_delay_identity (s : ℝ) :
    s * (2 * s - 2) = auxiliaryAdjoint s + auxiliaryAdjoint (s + 1) := by
  unfold auxiliaryAdjoint
  ring

theorem auxiliaryAdjoint_pos (s : ℝ) (hs : 2 ≤ s) : 0 < auxiliaryAdjoint s := by
  unfold auxiliaryAdjoint
  nlinarith

/-- Differentiating the original error solution transfers its vanishing
pairing to the auxiliary equation. The integration interval stays above two. -/
theorem auxiliaryErrorSum_pairing_zero (s : ℝ) (hs : 3 < s) :
    s * auxiliaryAdjoint s * auxiliaryErrorSum s =
      ∫ t in (s - 1)..s, auxiliaryAdjoint (t + 1) * auxiliaryErrorSum t := by
  let R : ℝ → ℝ := fun t => upperContinuousError t + lowerContinuousError t
  have hab : s - 1 ≤ s := by linarith
  have hR : ContinuousOn R (Icc (s - 1) s) :=
    (continuousOn_upperContinuousError.mono
      (by intro t ht; change 1 < t; linarith [ht.1])).add
    (continuousOn_lowerContinuousError.mono
      (by intro t ht; change 2 ≤ t; linarith [ht.1]))
  have hQ : ContinuousOn auxiliaryErrorSum (Icc (s - 1) s) :=
    continuousOn_auxiliaryErrorSum.mono
      (by intro t ht; change 1 < t; linarith [ht.1])
  have hq : Continuous (fun t : ℝ => auxiliaryAdjoint (t + 1)) := by
    unfold auxiliaryAdjoint
    fun_prop
  have hq' : ∀ t : ℝ, HasDerivAt (fun x => auxiliaryAdjoint (x + 1)) (2 * t) t := by
    intro t
    apply ((hasDerivAt_auxiliaryAdjoint (t + 1)).comp t
      ((hasDerivAt_id t).add_const 1)).congr_deriv
    ring
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := s - 1) (b := s) hq.continuousOn
    (by rwa [uIcc_of_le hab])
    (fun t _ => hq' t)
    (show ∀ t ∈ Ioo (min (s - 1) s) (max (s - 1) s),
      HasDerivAt R (-auxiliaryErrorSum t) t from by
      intro t ht
      rw [min_eq_left hab, max_eq_right hab] at ht
      exact hasDerivAt_continuousErrorSum t (by linarith [ht.1]))
    ((continuous_const.mul continuous_id).intervalIntegrable (a := s - 1) (b := s))
    (hQ.neg.intervalIntegrable_of_Icc hab)
  have hp := continuousErrorMass_pairing_zero s hs.le
  have he : (fun t => 2 * t * R t) = fun t => 2 * continuousErrorMass t := by
    funext t
    dsimp [R, continuousErrorMass]
    ring
  change (∫ t in (s - 1)..s, auxiliaryAdjoint (t + 1) * -auxiliaryErrorSum t) =
    auxiliaryAdjoint (s + 1) * R s - auxiliaryAdjoint (s - 1 + 1) * R (s - 1) -
      ∫ t in (s - 1)..s, 2 * t * R t at hi
  simp only [mul_neg, intervalIntegral.integral_neg, sub_add_cancel] at hi
  rw [he, intervalIntegral.integral_const_mul, ← hp] at hi
  have hm := mul_auxiliaryErrorSum s hs
  change s * auxiliaryErrorSum s = R s + R (s - 1) at hm
  have hmass : continuousErrorMass s = s * R s := by
    dsimp [continuousErrorMass, R]
    ring
  rw [hmass] at hi
  have ha := auxiliaryAdjoint_delay_identity s
  nlinarith [congrArg (fun x => auxiliaryAdjoint s * x) hm,
    congrArg (fun x => R s * x) ha]

end Chen.LinearSieve
