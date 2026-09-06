import ChenTheorem.Lemma9.LinearSieve.InflatedChildWeight

open Filter Set
open scoped Topology

namespace Chen.LinearSieve

noncomputable def inflatedUpperInitialWeight (d δ D t : ℝ) : ℝ :=
  shiftedAuxiliaryInflation d D 1 (t - 1) * (t / (t - 1)) ^ (δ + 1) * linearSieveInitialConstant

theorem inflatedChildUpperWeight_initial (d δ D t : ℝ) (ht : 2 < t) (ht4 : t ≤ 4) :
    t * inflatedChildAuxiliaryWeight d δ D t upperAuxiliaryError = inflatedUpperInitialWeight d δ D t := by
  rw [inflatedChildAuxiliaryWeight_factorization d δ D t upperAuxiliaryError (by linarith),
    sq_mul_upperAuxiliaryError_initial (t - 1) (by linarith) (by linarith)]
  unfold inflatedUpperInitialWeight
  ring

theorem hasDerivAt_auxiliaryRatioPower (κ t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => (t / (t - 1)) ^ κ)
      ((t / (t - 1)) ^ κ * (-κ / (t * (t - 1)))) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hr : 0 < t / (t - 1) := div_pos (by linarith) (by linarith)
  apply ((((hasDerivAt_id t).div ((hasDerivAt_id t).sub_const 1) ht1).rpow_const
    (p := κ) (Or.inl hr.ne'))).congr_deriv
  dsimp only [Pi.div_apply, id_eq]
  rw [Real.rpow_sub hr, Real.rpow_one]
  field_simp
  ring

theorem hasDerivAt_inflatedUpperInitialWeight (d δ D t : ℝ) (hD : 1 < D) (ht : 1 < t) :
    HasDerivAt (inflatedUpperInitialWeight d δ D)
      (inflatedUpperInitialWeight d δ D t *
        (auxiliaryInflationSlope d D 1 (t - 1) - (δ + 1) / (t * (t - 1)))) t := by
  have hi := (hasDerivAt_shiftedAuxiliaryInflation d D 1 (t - 1) hD (by linarith)).comp t
    ((hasDerivAt_id t).sub_const 1)
  apply ((hi.mul (hasDerivAt_auxiliaryRatioPower (δ + 1) t ht)).mul_const linearSieveInitialConstant).congr_deriv
  dsimp only [Function.comp_def, id_eq, inflatedUpperInitialWeight]
  ring

theorem eventually_inflatedUpperInitialWeight_antitone (d δ : ℝ) (hd : 0 < d) (hδ : -1 < δ) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ AntitoneOn (inflatedUpperInitialWeight d δ D) (Icc 2 4) := by
  have hlim : Tendsto (fun D : ℝ => (d + 1) * (4 : ℝ) ^ d / Real.log D) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlim.eventually (gt_mem_nhds
    (show 0 < (δ + 1) / 12 by linarith))] with D hD hsmall
  refine ⟨hD, ?_⟩
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 2 4)
    (f' := fun t => inflatedUpperInitialWeight d δ D t *
      (auxiliaryInflationSlope d D 1 (t - 1) - (δ + 1) / (t * (t - 1))))
  · exact fun t ht => (hasDerivAt_inflatedUpperInitialWeight d δ D t hD
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_inflatedUpperInitialWeight d δ D t hD (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hs := auxiliaryInflationSlope_initial_bound d D 1 (t - 1) hd hD
      (by norm_num) le_rfl (by linarith) (by linarith [ht.2])
    have hfrac : (δ + 1) / 12 ≤ (δ + 1) / (t * (t - 1)) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      nlinarith [ht.1, ht.2]
    apply mul_nonpos_of_nonneg_of_nonpos _ (by linarith)
    unfold inflatedUpperInitialWeight shiftedAuxiliaryInflation
    have hA := linearSieveInitialConstant_ge_three
    have hL := Real.log_pos hD
    have hp := Real.rpow_nonneg (show 0 ≤ t - 1 + 1 by linarith) d
    have hbase : 0 ≤ 1 + (t - 1 + 1) ^ d / Real.log D := by positivity
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hbase _)
      (Real.rpow_nonneg (by positivity) _)) (by linarith)

/-- The initial explicit formula joins the large-parameter monotonicity at
four, giving the entire domain required by the lower sieve. -/
theorem eventually_inflatedChildUpperWeight_antitone (d δ : ℝ) (hd : 0 < d) (hδ : -1 < δ) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧
      AntitoneOn (fun t => t * inflatedChildAuxiliaryWeight d δ D t upperAuxiliaryError)
        (Ioc 2 (2 * growingSieveParameter d (Real.log D) + 1)) := by
  filter_upwards [eventually_inflatedUpperInitialWeight_antitone d δ hd hδ,
    eventually_inflatedChildUpperWeight_antitone_above_four d δ hd hδ.le] with D hi hg
  refine ⟨hi.1, ?_⟩
  have hinit : AntitoneOn (fun t => t * inflatedChildAuxiliaryWeight d δ D t upperAuxiliaryError) (Ioc 2 4) := by
    intro s hs t ht hst
    dsimp only
    rw [inflatedChildUpperWeight_initial d δ D s hs.1 hs.2,
      inflatedChildUpperWeight_initial d δ D t ht.1 ht.2]
    exact hi.2 ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩ hst
  intro s hs t ht hst
  by_cases hs4 : 4 ≤ s
  · exact hg.2 ⟨hs4, hs.2⟩ ⟨hs4.trans hst, ht.2⟩ hst
  · by_cases ht4 : t ≤ 4
    · exact hinit ⟨hs.1, le_of_not_ge hs4⟩ ⟨ht.1, ht4⟩ hst
    · exact (hg.2 ⟨le_rfl, (le_of_not_ge ht4).trans ht.2⟩
        ⟨le_of_not_ge ht4, ht.2⟩ (le_of_not_ge ht4)).trans
        (hinit ⟨hs.1, le_of_not_ge hs4⟩ (by norm_num) (le_of_not_ge hs4))

end Chen.LinearSieve
