import ChenTheorem.Lemma9.LinearSieve.AuxiliaryShiftComparison

open Set

namespace Chen.LinearSieve

noncomputable def auxiliaryBarrierPhase (a C s : ℝ) : ℝ :=
  a * s * Real.log s + C * s

noncomputable def auxiliaryBarrierSlope (a C s : ℝ) : ℝ :=
  a * (Real.log s + 1) + C

noncomputable def auxiliaryBarrierWeight (a C s : ℝ) : ℝ :=
  auxiliaryErrorSum s * Real.exp (auxiliaryBarrierPhase a C s)

theorem hasDerivAt_auxiliaryBarrierPhase (a C s : ℝ) (hs : 0 < s) :
    HasDerivAt (auxiliaryBarrierPhase a C) (auxiliaryBarrierSlope a C s) s := by
  apply ((((hasDerivAt_id s).const_mul a).mul (Real.hasDerivAt_log hs.ne')).add
    ((hasDerivAt_id s).const_mul C)).congr_deriv
  dsimp [auxiliaryBarrierSlope]
  field_simp

theorem continuousOn_auxiliaryBarrierPhase (a C : ℝ) :
    ContinuousOn (auxiliaryBarrierPhase a C) (Ioi 0) := by
  intro s hs
  exact (hasDerivAt_auxiliaryBarrierPhase a C s hs).continuousAt.continuousWithinAt

theorem monotoneOn_auxiliaryBarrierSlope (a C : ℝ) (ha : 0 ≤ a) :
    MonotoneOn (auxiliaryBarrierSlope a C) (Ioi 0) := by
  intro s hs t ht hst
  have h := Real.log_le_log hs hst
  dsimp [auxiliaryBarrierSlope]
  nlinarith

theorem auxiliaryBarrierPhase_increment_bounds (a C u t : ℝ)
    (ha : 0 ≤ a) (hu : 0 < u) (hut : u ≤ t) :
    auxiliaryBarrierSlope a C u * (t - u) ≤
        auxiliaryBarrierPhase a C t - auxiliaryBarrierPhase a C u ∧
      auxiliaryBarrierPhase a C t - auxiliaryBarrierPhase a C u ≤
        auxiliaryBarrierSlope a C t * (t - u) := by
  rcases eq_or_lt_of_le hut with h | h
  · subst t
    simp
  obtain ⟨v, hv, hd⟩ := exists_hasDerivAt_eq_slope
    (auxiliaryBarrierPhase a C) (auxiliaryBarrierSlope a C) h
    ((continuousOn_auxiliaryBarrierPhase a C).mono
      (by intro x hx; change 0 < x; linarith [hx.1]))
    (fun x hx => hasDerivAt_auxiliaryBarrierPhase a C x (by linarith [hx.1]))
  have hlo := monotoneOn_auxiliaryBarrierSlope a C ha hu
    (show v ∈ Ioi 0 by change 0 < v; linarith [hv.1]) hv.1.le
  have hhi := monotoneOn_auxiliaryBarrierSlope a C ha
    (show v ∈ Ioi 0 by change 0 < v; linarith [hv.1])
    (show t ∈ Ioi 0 by change 0 < t; linarith) hv.2.le
  rw [hd] at hlo hhi
  exact ⟨(le_div_iff₀ (sub_pos.mpr h)).mp hlo,
    (div_le_iff₀ (sub_pos.mpr h)).mp hhi⟩

theorem hasDerivAt_auxiliaryBarrierWeight (a C s : ℝ) (hs : 3 < s) :
    HasDerivAt (auxiliaryBarrierWeight a C)
      (auxiliaryBarrierWeight a C s *
        (auxiliaryBarrierSlope a C s - 2 / s - auxiliaryShiftRatio s)) s := by
  apply ((hasDerivAt_auxiliaryErrorSum s hs).mul
    ((hasDerivAt_auxiliaryBarrierPhase a C s (by linarith)).exp)).congr_deriv
  dsimp [auxiliaryBarrierWeight, auxiliaryShiftRatio]
  have hQ := (auxiliaryErrorSum_pos s (by linarith)).ne'
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

theorem auxiliaryBarrierWeight_pos (a C s : ℝ) (hs : 1 < s) :
    0 < auxiliaryBarrierWeight a C s :=
  mul_pos (auxiliaryErrorSum_pos s hs) (Real.exp_pos _)

theorem auxiliaryBarrierWeight_stationary_iff (a C s : ℝ) (hs : 3 < s) :
    deriv (auxiliaryBarrierWeight a C) s = 0 ↔
      auxiliaryShiftRatio s = auxiliaryBarrierSlope a C s - 2 / s := by
  rw [(hasDerivAt_auxiliaryBarrierWeight a C s hs).deriv,
    mul_eq_zero, or_iff_right (auxiliaryBarrierWeight_pos a C s (by linarith)).ne']
  constructor <;> intro h <;> linarith

end Chen.LinearSieve
