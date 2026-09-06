import ChenTheorem.Lemma9.LinearSieve.ContinuousPositivity
import ChenTheorem.Lemma9.LinearSieve.ContinuousAuxiliaryWeights

open Set MeasureTheory

namespace Chen.LinearSieve

theorem childAuxiliaryWeight_lt (δ t : ℝ) (hδ : δ < 1) (ht : 1 < t) :
    childAuxiliaryWeight δ t < t := by
  have ht1 : 0 < t - 1 := by linarith
  have hb : 1 < t / (t - 1) := (lt_div_iff₀ ht1).2 (by linarith)
  have hp := Real.rpow_lt_rpow_of_exponent_lt hb hδ
  rw [Real.rpow_one] at hp
  calc
    childAuxiliaryWeight δ t < (t / (t - 1)) * (t - 1) :=
      mul_lt_mul_of_pos_right hp ht1
    _ = t := div_mul_cancel₀ t ht1.ne'

/-- Strictness on one fixed interval supplies a positive gap for every larger
upper endpoint. In particular this gap is not lost when that endpoint tends to infinity. -/
theorem integral_childAuxiliaryWeight_gap (δ s : ℝ) (H : ℝ → ℝ)
    (hδ : δ < 1) (hs : 1 < s)
    (hH : ContinuousOn H (Ici s)) (hpos : ∀ t ∈ Ici s, 0 < H t) :
    ∃ η > 0, ∀ b, s + 1 ≤ b →
      (∫ t in s..b, childAuxiliaryWeight δ t * H t) ≤
        (∫ t in s..b, t * H t) - η := by
  let g : ℝ → ℝ := fun t => (t - childAuxiliaryWeight δ t) * H t
  have hg : ContinuousOn g (Ici s) :=
    (continuousOn_id.sub ((continuousOn_childAuxiliaryWeight δ).mono
      (fun t ht => by change 1 < t; exact hs.trans_le ht))).mul hH
  have hgpos : ∀ t ∈ Ici s, 0 < g t := by
    intro t ht
    exact mul_pos (sub_pos.mpr (childAuxiliaryWeight_lt δ t hδ (hs.trans_le ht)))
      (hpos t ht)
  have hη : 0 < ∫ t in s..s + 1, g t := by
    apply intervalIntegral.integral_pos (by linarith)
      (hg.mono (fun _ ht => ht.1))
    · exact fun t ht => (hgpos t ht.1.le).le
    · exact ⟨s, ⟨le_rfl, by linarith⟩, hgpos s (by simp)⟩
  refine ⟨_, hη, ?_⟩
  intro b hb
  have hsb : s ≤ b := by linarith
  have hgc := hg.mono (show Icc s b ⊆ Ici s from fun _ ht => ht.1)
  have hgi : IntervalIntegrable g volume s b := hgc.intervalIntegrable_of_Icc hsb
  have hmono : (∫ t in s..s + 1, g t) ≤ ∫ t in s..b, g t :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) hb
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => (hgpos t ht.1.le).le) hgi
  have hHc := hH.mono (show Icc s b ⊆ Ici s from fun _ ht => ht.1)
  have hwc := (continuousOn_childAuxiliaryWeight δ).mono
    (show Icc s b ⊆ Ioi 1 from fun t ht => hs.trans_le ht.1)
  have hi : IntervalIntegrable (fun t => t * H t) volume s b :=
    (continuousOn_id.mul hHc).intervalIntegrable_of_Icc hsb
  have hj : IntervalIntegrable (fun t => childAuxiliaryWeight δ t * H t) volume s b :=
    (hwc.mul hHc).intervalIntegrable_of_Icc hsb
  have heq : g = fun t => t * H t - childAuxiliaryWeight δ t * H t := by
    funext t
    dsimp [g]
    ring
  rw [heq, intervalIntegral.integral_sub hi hj] at hmono
  rw [heq]
  linarith

theorem integral_childAuxiliaryWeight_lower_gap (δ s : ℝ)
    (hδ : δ < 1) (hs : 3 ≤ s) :
    ∃ η > 0, ∀ b, s + 1 ≤ b →
      (∫ t in s..b, childAuxiliaryWeight δ t * lowerAuxiliaryError (t - 1)) ≤
        s ^ 2 * upperAuxiliaryError s - b ^ 2 * upperAuxiliaryError b - η := by
  have hH : ContinuousOn (fun t => lowerAuxiliaryError (t - 1)) (Ici s) :=
    continuousOn_lowerAuxiliaryError.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 0 < t - 1; change s ≤ t at ht; linarith)
  obtain ⟨η, hη, hgap⟩ := integral_childAuxiliaryWeight_gap δ s _ hδ (by linarith) hH
    (fun t ht => lowerAuxiliaryError_pos _ (by change s ≤ t at ht; linarith))
  refine ⟨η, hη, fun b hb => ?_⟩
  simpa only [integral_mul_shift_lowerAuxiliaryError s b hs (by linarith : s ≤ b)]
    using hgap b hb

theorem integral_childAuxiliaryWeight_upper_gap (δ s : ℝ)
    (hδ : δ < 1) (hs : 2 < s) :
    ∃ η > 0, ∀ b, s + 1 ≤ b →
      (∫ t in s..b, childAuxiliaryWeight δ t * upperAuxiliaryError (t - 1)) ≤
        s ^ 2 * lowerAuxiliaryError s - b ^ 2 * lowerAuxiliaryError b - η := by
  have hH : ContinuousOn (fun t => upperAuxiliaryError (t - 1)) (Ici s) :=
    continuousOn_upperAuxiliaryError.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 1 < t - 1; change s ≤ t at ht; linarith)
  obtain ⟨η, hη, hgap⟩ := integral_childAuxiliaryWeight_gap δ s _ hδ (by linarith) hH
    (fun t ht => upperAuxiliaryError_pos _ (by change s ≤ t at ht; linarith))
  refine ⟨η, hη, fun b hb => ?_⟩
  simpa only [integral_mul_shift_upperAuxiliaryError s b hs.le (by linarith : s ≤ b)]
    using hgap b hb

end Chen.LinearSieve
