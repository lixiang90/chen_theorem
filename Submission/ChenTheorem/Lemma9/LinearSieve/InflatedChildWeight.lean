import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedLowerMonotonicity

set_option autoImplicit true
open Filter Set

namespace Chen.LinearSieve

/-- The common parent-level majorant for the auxiliary error at a child. -/
noncomputable def inflatedChildAuxiliaryWeight (d δ D t : ℝ) (H : ℝ → ℝ) : ℝ :=
  auxiliaryChildInflation d D t * childAuxiliaryWeight δ t * H (t - 1)

theorem inflatedChildAuxiliaryWeight_nonneg (d δ D t : ℝ) (H : ℝ → ℝ)
    (hD : 1 < D) (ht : 1 < t) (hH : 0 ≤ H (t - 1)) :
    0 ≤ inflatedChildAuxiliaryWeight d δ D t H := by
  apply mul_nonneg (mul_nonneg _ (childAuxiliaryWeight_nonneg δ t ht)) hH
  unfold auxiliaryChildInflation
  apply Real.rpow_nonneg
  have hp := Real.rpow_nonneg (show 0 ≤ t by linarith) d
  have hL := Real.log_pos hD
  positivity

theorem inflatedChildAuxiliaryWeight_factorization (d δ D t : ℝ) (H : ℝ → ℝ)
    (ht : 1 < t) :
    t * inflatedChildAuxiliaryWeight d δ D t H =
      (shiftedAuxiliaryInflation d D 1 (t - 1) * ((t - 1) ^ 2 * H (t - 1))) *
        (t / (t - 1)) ^ (δ + 1) := by
  have ht1 : 0 < t - 1 := by linarith
  have hr : 0 < t / (t - 1) := div_pos (by linarith) ht1
  rw [Real.rpow_add hr, Real.rpow_one]
  unfold inflatedChildAuxiliaryWeight auxiliaryChildInflation shiftedAuxiliaryInflation childAuxiliaryWeight
  simp only [sub_add_cancel]
  field_simp

theorem inflatedChildAuxiliaryWeight_antitone_of_shifted (d δ D b B : ℝ)
    (H : ℝ → ℝ) (hδ : -1 ≤ δ) (hD : 1 < D) (hb : 0 < b)
    (hH : ∀ s ∈ Icc b B, 0 ≤ H s)
    (hanti : AntitoneOn (fun s => shiftedAuxiliaryInflation d D 1 s * (s ^ 2 * H s)) (Icc b B)) :
    AntitoneOn (fun t => t * inflatedChildAuxiliaryWeight d δ D t H) (Icc (b + 1) (B + 1)) := by
  intro s hs t ht hst
  have hs1 : 1 < s := by linarith [hs.1]
  have ht1 : 1 < t := by linarith [ht.1]
  have hsm : s - 1 ∈ Icc b B := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have htm : t - 1 ∈ Icc b B := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hΛ := hanti hsm htm (by linarith)
  have hr : t / (t - 1) ≤ s / (s - 1) := by
    apply (div_le_div_iff₀ (by linarith : 0 < t - 1) (by linarith : 0 < s - 1)).mpr
    nlinarith
  have hp := Real.rpow_le_rpow (div_nonneg (by linarith : 0 ≤ t) (by linarith)) hr (by linarith : 0 ≤ δ + 1)
  have hΛs : 0 ≤ shiftedAuxiliaryInflation d D 1 (s - 1) * ((s - 1) ^ 2 * H (s - 1)) := by
    apply mul_nonneg _ (mul_nonneg (sq_nonneg _) (hH _ hsm))
    unfold shiftedAuxiliaryInflation
    apply Real.rpow_nonneg
    have hL := Real.log_pos hD
    have hr := Real.rpow_nonneg (show 0 ≤ s - 1 + 1 by linarith) d
    positivity
  have h := mul_le_mul hΛ hp (Real.rpow_nonneg (by positivity) _) hΛs
  simpa only [inflatedChildAuxiliaryWeight_factorization d δ D t H ht1,
    inflatedChildAuxiliaryWeight_factorization d δ D s H hs1] using h

/-- The lower child has the weighted monotonicity required by the upper
sieve for every parent parameter at least three. -/
theorem eventually_inflatedChildLowerWeight_antitone (d δ : ℝ) (hd : 0 < d) (hδ : -1 ≤ δ) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧
      AntitoneOn (fun t => t * inflatedChildAuxiliaryWeight d δ D t lowerAuxiliaryError)
        (Icc 3 (2 * growingSieveParameter d (Real.log D) + 1)) := by
  filter_upwards [eventually_inflatedLowerAuxiliary_antitone d hd] with D hD
  refine ⟨hD.1, ?_⟩
  convert! inflatedChildAuxiliaryWeight_antitone_of_shifted d δ D 2 _ lowerAuxiliaryError
    hδ hD.1 (by norm_num) (fun s hs => lowerAuxiliaryError_nonneg s (by linarith [hs.1]))
    (hD.2 1 (by norm_num) le_rfl) using 1
  norm_num

theorem eventually_inflatedChildUpperWeight_antitone_above_four (d δ : ℝ)
    (hd : 0 < d) (hδ : -1 ≤ δ) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧
      AntitoneOn (fun t => t * inflatedChildAuxiliaryWeight d δ D t upperAuxiliaryError)
        (Icc 4 (2 * growingSieveParameter d (Real.log D) + 1)) := by
  filter_upwards [eventually_inflatedAuxiliary_antitone d hd] with D hD
  refine ⟨hD.1, ?_⟩
  convert! inflatedChildAuxiliaryWeight_antitone_of_shifted d δ D 3 _ upperAuxiliaryError
    hδ hD.1 (by norm_num) (fun s hs => upperAuxiliaryError_nonneg s (by linarith [hs.1]))
    (hD.2 1 (by norm_num) le_rfl).1 using 1
  norm_num

end Chen.LinearSieve
