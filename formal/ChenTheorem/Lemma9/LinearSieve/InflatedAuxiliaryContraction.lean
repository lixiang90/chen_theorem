import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryIntegral

open Set MeasureTheory Filter

namespace Chen.LinearSieve

theorem integral_inflatedChildWeight_le_of_dissipation (d δ D s b B : ℝ) (H J : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 < s) (hsb : s ≤ b)
    (hqc : ContinuousOn (fun t => inflatedChildAuxiliaryWeight d δ D t J) (Icc s b))
    (hH : ContinuousOn H (Icc s b)) (hJ : ContinuousOn (fun t => J (t - 1)) (Icc s b))
    (hd : ∀ t ∈ Ioo s b, HasDerivAt (fun u => u ^ 2 * H u) (-t * J (t - 1)) t)
    (hpoint : ∀ t ∈ Icc s b, inflatedChildAuxiliaryWeight d δ D t J ≤
      (1 - (1 - δ) / (4 * B)) * inflatedAuxiliaryDissipation d D t H J) :
    (∫ t in s..b, inflatedChildAuxiliaryWeight d δ D t J) ≤
      (1 - (1 - δ) / (4 * B)) *
        (auxiliaryInflation d D s * (s ^ 2 * H s) - auxiliaryInflation d D b * (b ^ 2 * H b)) := by
  have hc := continuousOn_inflatedAuxiliaryDissipation d D s b H J hD hs hH hJ
  have hm := intervalIntegral.integral_mono_on (μ := volume) hsb
    (hqc.intervalIntegrable_of_Icc hsb)
    ((continuousOn_const.mul hc).intervalIntegrable_of_Icc hsb) hpoint
  simp only [Pi.mul_apply] at hm
  rw [intervalIntegral.integral_const_mul,
    integral_inflatedAuxiliaryDissipation d D s b H J hD hs hsb hH hJ hd] at hm
  exact hm

/-- Strict contraction for the upper sieve's actual inflated lower-child
integral, with both a quantitative gap and the terminal tail retained. -/
theorem eventually_integral_inflatedChildLower_contraction (d δ : ℝ) (hd : 0 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ s b B : ℝ, 3 ≤ s → s ≤ b → b ≤ B →
      B ≤ 2 * growingSieveParameter d (Real.log D) →
      (∫ t in s..b, inflatedChildAuxiliaryWeight d δ D t lowerAuxiliaryError) ≤
        (1 - (1 - δ) / (4 * B)) *
          (auxiliaryInflation d D s * (s ^ 2 * upperAuxiliaryError s) -
            auxiliaryInflation d D b * (b ^ 2 * upperAuxiliaryError b)) := by
  filter_upwards [eventually_inflatedChildLower_dissipation d δ hd hδ hδ1] with D hD
  refine ⟨hD.1, ?_⟩
  intro s b B hs hsb hbB hcut
  have hH := continuousOn_upperAuxiliaryError.mono
    (show Icc s b ⊆ Ioi 1 from fun t ht => by change 1 < t; linarith [ht.1])
  have hJ := continuousOn_lowerAuxiliaryError.comp (continuousOn_id.sub continuousOn_const)
    (show MapsTo (fun t : ℝ => t - 1) (Icc s b) (Ioi 0) from
      fun t ht => by change 0 < t - 1; linarith [ht.1])
  exact integral_inflatedChildWeight_le_of_dissipation d δ D s b B upperAuxiliaryError lowerAuxiliaryError
    hD.1 (by linarith) hsb
    (continuousOn_inflatedChildAuxiliaryWeight d δ D 0 s b lowerAuxiliaryError hD.1 le_rfl (by linarith)
      continuousOn_lowerAuxiliaryError) hH hJ
    (fun t ht => hasDerivAt_sq_mul_upperAuxiliaryError t (by linarith [ht.1]))
    (fun t ht => hD.2 t B (hs.trans ht.1) (ht.2.trans hbB) (ht.2.trans (hbB.trans hcut)))

/-- The lower-sieve contraction holds throughout its open domain `s>2`. -/
theorem eventually_integral_inflatedChildUpper_contraction (d δ : ℝ) (hd : 0 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ s b B : ℝ, 2 < s → s ≤ b → b ≤ B →
      B ≤ 2 * growingSieveParameter d (Real.log D) →
      (∫ t in s..b, inflatedChildAuxiliaryWeight d δ D t upperAuxiliaryError) ≤
        (1 - (1 - δ) / (4 * B)) *
          (auxiliaryInflation d D s * (s ^ 2 * lowerAuxiliaryError s) -
            auxiliaryInflation d D b * (b ^ 2 * lowerAuxiliaryError b)) := by
  filter_upwards [eventually_inflatedChildUpper_dissipation d δ hd hδ hδ1] with D hD
  refine ⟨hD.1, ?_⟩
  intro s b B hs hsb hbB hcut
  have hH := continuousOn_lowerAuxiliaryError.mono
    (show Icc s b ⊆ Ioi 0 from fun t ht => by change 0 < t; linarith [ht.1])
  have hJ := continuousOn_upperAuxiliaryError.comp (continuousOn_id.sub continuousOn_const)
    (show MapsTo (fun t : ℝ => t - 1) (Icc s b) (Ioi 1) from
      fun t ht => by change 1 < t - 1; linarith [ht.1])
  exact integral_inflatedChildWeight_le_of_dissipation d δ D s b B lowerAuxiliaryError upperAuxiliaryError
    hD.1 (by linarith) hsb
    (continuousOn_inflatedChildAuxiliaryWeight d δ D 1 s b upperAuxiliaryError hD.1 (by norm_num) (by linarith)
      continuousOn_upperAuxiliaryError) hH hJ
    (fun t ht => hasDerivAt_sq_mul_lowerAuxiliaryError t (by linarith [ht.1]))
    (fun t ht => hD.2 t B (hs.trans_le ht.1) (ht.2.trans hbB) (ht.2.trans (hbB.trans hcut)))

end Chen.LinearSieve
