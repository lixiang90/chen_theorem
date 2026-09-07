import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierCritical
import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousFirstZero

set_option autoImplicit true
open Set Filter

namespace Chen.LinearSieve

theorem continuousOn_auxiliaryShiftRatio : ContinuousOn auxiliaryShiftRatio (Ioi 2) := by
  apply ContinuousOn.div
  · exact continuousOn_auxiliaryErrorSum.comp (continuousOn_id.sub continuousOn_const)
      (by intro s hs; change 1 < s - 1; linarith [show 2 < s from hs])
  · exact continuousOn_id.mul (continuousOn_auxiliaryErrorSum.mono
      (by intro s hs; change 1 < s; linarith [show 2 < s from hs]))
  · intro s hs
    exact (mul_pos (show 0 < s by linarith [show 2 < s from hs])
      (auxiliaryErrorSum_pos s (by linarith [show 2 < s from hs]))).ne'

theorem continuousOn_deriv_auxiliaryBarrierWeight (a C : ℝ) :
    ContinuousOn (deriv (auxiliaryBarrierWeight a C)) (Ioi 3) := by
  have hW : ContinuousOn (auxiliaryBarrierWeight a C) (Ioi 3) := by
    intro s hs
    exact (hasDerivAt_auxiliaryBarrierWeight a C s hs).continuousAt.continuousWithinAt
  have hL : ContinuousOn (auxiliaryBarrierSlope a C) (Ioi 3) := by
    intro s hs
    have hs0 : s ≠ 0 := by linarith [show 3 < s from hs]
    exact ((((Real.continuousAt_log hs0).add continuousAt_const).const_mul a).add
      continuousAt_const).continuousWithinAt
  have hI : ContinuousOn (fun s : ℝ => 2 / s) (Ioi 3) :=
    continuousOn_const.div continuousOn_id
      (by intro s hs; change s ≠ 0; linarith [show 3 < s from hs])
  have hR := continuousOn_auxiliaryShiftRatio.mono
    (show Ioi (3 : ℝ) ⊆ Ioi 2 from by intro s hs; change 2 < s; linarith [show 3 < s from hs])
  apply (hW.mul ((hL.sub hI).sub hR)).congr
  intro s hs
  exact (hasDerivAt_auxiliaryBarrierWeight a C s hs).deriv

theorem lowerAuxiliaryBarrier_deriv_neg_of_initial (C A : ℝ)
    (hC : 0 ≤ C) (hA : 4 ≤ A) (hlog : 20 ≤ Real.log A)
    (hinit : ∀ s ∈ Icc A (A + 1), deriv (auxiliaryBarrierWeight (1 / 2) (-C)) s < 0) :
    ∀ s : ℝ, A ≤ s → deriv (auxiliaryBarrierWeight (1 / 2) (-C)) s < 0 := by
  intro s hs
  by_contra hn
  have hg := (continuousOn_deriv_auxiliaryBarrierWeight (1 / 2) (-C)).mono
    (show Icc A s ⊆ Ioi 3 from by intro t ht; change 3 < t; linarith [ht.1])
  obtain ⟨m, hm, hzero, hbefore⟩ := exists_first_zero_of_nonneg
    (deriv (auxiliaryBarrierWeight (1 / 2) (-C))) A s hs hg
    (hinit A ⟨le_rfl, by linarith⟩) (le_of_not_gt hn)
  have hmA : A + 1 < m := by
    by_contra h
    have hz := hinit m ⟨hm.1.le, le_of_not_gt h⟩
    rw [hzero] at hz
    exact lt_irrefl _ hz
  have hanti : AntitoneOn (auxiliaryBarrierWeight (1 / 2) (-C)) (Icc (m - 1) m) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (m - 1) m)
    · intro t ht
      exact (hasDerivAt_auxiliaryBarrierWeight (1 / 2) (-C) t
        (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hasDerivAt_auxiliaryBarrierWeight (1 / 2) (-C) t
        (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hbefore t ⟨by linarith [ht.1], ht.2⟩).le
  have hlogm : 20 ≤ Real.log m :=
    hlog.trans (Real.log_le_log (by linarith : 0 < A) hm.1.le)
  exact lowerAuxiliaryBarrier_no_stationary C m hC (by linarith) hlogm hanti hzero

/-- A global logarithmic lower bound follows from the absence of a first
stationary point, using an explicit initial linear coefficient. -/
theorem auxiliaryShiftRatio_logarithmic_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, Real.exp 20 ≤ s →
      (1 / 2 : ℝ) * Real.log s - C < auxiliaryShiftRatio s := by
  let A : ℝ := Real.exp 20
  let C : ℝ := (Real.log (A + 1) + 1) / 2 + 1
  have hA : 21 ≤ A := by dsimp [A]; linarith [Real.add_one_le_exp (20 : ℝ)]
  have hC : 0 < C := by
    have h := Real.log_pos (show 1 < A + 1 by linarith)
    dsimp [C]
    linarith
  have hinit : ∀ s ∈ Icc A (A + 1), deriv (auxiliaryBarrierWeight (1 / 2) (-C)) s < 0 := by
    intro s hs
    have hs3 : 3 < s := by linarith [hs.1]
    rw [(hasDerivAt_auxiliaryBarrierWeight (1 / 2) (-C) s hs3).deriv]
    apply mul_neg_of_pos_of_neg (auxiliaryBarrierWeight_pos _ _ s (by linarith))
    have hl := Real.log_le_log (show 0 < s by linarith) hs.2
    have hr := auxiliaryShiftRatio_pos s (by linarith)
    have hi := div_pos (by norm_num : (0 : ℝ) < 2) (show 0 < s by linarith)
    dsimp [auxiliaryBarrierSlope, C]
    nlinarith
  have hneg := lowerAuxiliaryBarrier_deriv_neg_of_initial C A hC.le (by linarith)
    (by dsimp [A]; rw [Real.log_exp]) hinit
  refine ⟨C, hC, ?_⟩
  intro s hs
  have hsA : A ≤ s := hs
  have hs3 : 3 < s := by linarith
  have hn := hneg s hsA
  rw [(hasDerivAt_auxiliaryBarrierWeight (1 / 2) (-C) s hs3).deriv] at hn
  have hp := auxiliaryBarrierWeight_pos (1 / 2) (-C) s (by linarith)
  have hfactor : auxiliaryBarrierSlope (1 / 2) (-C) s - 2 / s - auxiliaryShiftRatio s < 0 := by
    nlinarith
  have hi : 2 / s ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ (show 0 < s by linarith)).mpr (by linarith)
  dsimp [auxiliaryBarrierSlope] at hfactor
  nlinarith

theorem eventually_auxiliaryShiftRatio_log_lower :
    ∀ᶠ s : ℝ in atTop, (1 / 4 : ℝ) * Real.log s ≤ auxiliaryShiftRatio s := by
  obtain ⟨C, _, hC⟩ := auxiliaryShiftRatio_logarithmic_lower_bound
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (4 * C)
  filter_upwards [eventually_ge_atTop (Real.exp 20), hlog] with s hs hl
  have h := hC s hs
  nlinarith

theorem eventually_auxiliaryCrossShift_log_lower :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ s : ℝ in atTop,
      k * Real.log s ≤ lowerAuxiliaryError (s - 1) / (s * upperAuxiliaryError s) ∧
      k * Real.log s ≤ upperAuxiliaryError (s - 1) / (s * lowerAuxiliaryError s) := by
  obtain ⟨c, hc, _, h⟩ := auxiliaryCrossShift_ratios_comparable
  refine ⟨c / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_auxiliaryShiftRatio_log_lower] with s hs hl
  have hb := mul_le_mul_of_nonneg_left hl hc.le
  have hu := (h s hs).1.1
  have hd := (h s hs).2.1
  constructor <;> nlinarith

end Chen.LinearSieve
