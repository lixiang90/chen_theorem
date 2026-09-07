import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabTerm

set_option autoImplicit true
open Finset MeasureTheory Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The first term has a corner at three. Its left derivative at the
corner is the derivative of the branch `3/s - 1`. -/
theorem hasDerivWithinAt_firstContinuousTerm_left (s : ℝ) (hs : 0 < s) :
    HasDerivWithinAt (rosserContinuousTerm 1)
      (if s ≤ 3 then -3 / s ^ 2 else 0) (Iio s) s := by
  by_cases hs3 : s ≤ 3
  · rw [if_pos hs3]
    have hd : HasDerivAt (fun t : ℝ => 3 / t - 1) (-3 / s ^ 2) s := by
      convert! ((hasDerivAt_const s (3 : ℝ)).fun_div (hasDerivAt_id s) hs.ne').sub_const 1 using 1
      simp
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ht0 hts
      rw [rosserContinuousTerm_one t ht0, max_eq_left (by linarith [show t < s from hts])]
      field_simp
    · rw [rosserContinuousTerm_one s hs, max_eq_left (by linarith)]
      field_simp
  · rw [if_neg hs3]
    have h3s : 3 < s := lt_of_not_ge hs3
    apply (hasDerivWithinAt_const s (Iio s) (0 : ℝ)).congr_of_eventuallyEq
    · filter_upwards [(eventually_gt_nhds h3s).filter_mono nhdsWithin_le_nhds] with t ht
      exact rosserContinuousTerm_eq_zero 1 t (by norm_num; exact ht.le)
    · exact rosserContinuousTerm_eq_zero 1 s (by norm_num; exact h3s.le)

noncomputable def firstContinuousTermWeightSlope (D t : ℝ) : ℝ :=
  if sieveParameter D t - 1 ≤ 3 then
    3 / (sieveParameter D t - 1) ^ 2 * (Real.log D * logSieveKernel t) else 0

theorem hasDerivWithinAt_firstContinuousTermWeight_right (D t : ℝ)
    (hD : 1 < D) (ht : 1 < t) (hs : 1 < sieveParameter D t) :
    HasDerivWithinAt (fun t => rosserContinuousTerm 1 (sieveParameter D t - 1))
      (firstContinuousTermWeightSlope D t) (Ioi t) t := by
  have hm : MapsTo (fun x => sieveParameter D x - 1) (Ioi t)
      (Iio (sieveParameter D t - 1)) := by
    intro x hx
    change sieveParameter D x - 1 < sieveParameter D t - 1
    apply sub_lt_sub_right
    exact div_lt_div_of_pos_left (Real.log_pos hD) (Real.log_pos ht)
      (Real.log_lt_log (by linarith) hx)
  have hh := (hasDerivWithinAt_firstContinuousTerm_left _ (sub_pos.mpr hs)).comp t
    ((hasDerivAt_sieveParameter D t ht).sub_const 1).hasDerivWithinAt hm
  convert! hh using 1
  unfold firstContinuousTermWeightSlope
  split_ifs <;> ring

theorem integrableOn_firstContinuousTermWeightSlope (D w z : ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (hs : 1 < sieveParameter D z) :
    IntegrableOn (firstContinuousTermWeightSlope D) (Icc w z) := by
  have hc : ContinuousOn (fun t => sieveParameter D t - 1) (Icc w z) :=
    (continuousOn_sieveParameter D w z hw).sub continuousOn_const
  have hpos : ∀ t ∈ Icc w z, 0 < sieveParameter D t - 1 := by
    intro t ht
    linarith [(sieveParameter_mem_Icc hD hw ht).1]
  have hum : Measurable (fun t => sieveParameter D t - 1) := by
    unfold sieveParameter
    fun_prop
  have hcont : ContinuousOn (fun t => 3 / (sieveParameter D t - 1) ^ 2 *
      (Real.log D * logSieveKernel t)) (Icc w z) :=
    (continuousOn_const.div (hc.pow 2) (fun t ht => pow_ne_zero _ (hpos t ht).ne')).mul
      (continuousOn_const.mul (continuousOn_logSieveKernel w z hw))
  have hi : IntegrableOn ({t | sieveParameter D t - 1 ≤ 3}.indicator
      (fun t => 3 / (sieveParameter D t - 1) ^ 2 * (Real.log D * logSieveKernel t)))
      (Icc w z) := hcont.integrableOn_Icc.indicator (measurableSet_le hum measurable_const)
  apply hi.congr_fun _ measurableSet_Icc
  intro t _
  by_cases ht : sieveParameter D t - 1 ≤ 3
  · rw [indicator_of_mem (show t ∈ {t | sieveParameter D t - 1 ≤ 3} from ht)]
    simp only [firstContinuousTermWeightSlope, if_pos ht]
  · rw [indicator_of_notMem (show t ∉ {t | sieveParameter D t - 1 ≤ 3} from ht)]
    simp only [firstContinuousTermWeightSlope, if_neg ht]

theorem firstContinuousTermWeightSlope_nonneg (D t : ℝ) (hD : 1 < D) (ht : 1 < t) :
    0 ≤ firstContinuousTermWeightSlope D t := by
  have hlog := (Real.log_pos hD).le
  have ht0 : 0 < t := zero_lt_one.trans ht
  unfold firstContinuousTermWeightSlope logSieveKernel
  split_ifs <;> positivity

/-- The first continuous term yields the second term under the same
Buchstab operation, including intervals that cross its support endpoint. -/
theorem weighted_buchstab_firstContinuousTerm_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 2 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          rosserContinuousTerm 1 (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
          rosserContinuousTerm 2 (sieveParameter D z) +
            2 * K * rosserContinuousTerm 1 (sieveParameter D z - 1) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_partial_summation_of_hasDeriv_right
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz hs P hP hodd
  have hs1 : 1 < sieveParameter D z := by linarith
  have hpos : ∀ t ∈ Icc w (z : ℝ), 1 < sieveParameter D t :=
    fun t ht => hs1.trans_le (sieveParameter_mem_Icc hD hw ht).1
  have hHc : ContinuousOn (fun s => rosserContinuousTerm 1 (s - 1))
      (Icc (sieveParameter D z) (sieveParameter D w)) :=
    (continuousOn_shift_rosserContinuousTerm 1).mono (fun _ ht => hs1.trans_le ht.1)
  have hfc := hHc.comp (continuousOn_sieveParameter D w z hw)
    (fun t ht => sieveParameter_mem_Icc hD hw ht)
  have hshape := (antitoneOn_mul_shift_rosserContinuousTerm 1).mono
    (show Icc (sieveParameter D z) (sieveParameter D w) ⊆ Ioi 1 from
      fun _ ht => hs1.trans_le ht.1)
  have h := hb w z hw hwz P hP hodd _ (firstContinuousTermWeightSlope D) hfc
    (fun t ht => hasDerivWithinAt_firstContinuousTermWeight_right D t hD
      (by linarith [ht.1]) (hpos t ⟨ht.1.le, ht.2.le⟩))
    (integrableOn_firstContinuousTermWeightSlope D w z hD hw hs1)
    (fun t ht => rosserContinuousTerm_nonneg 1 _ (sub_pos.mpr (hpos t ht)))
    (fun t ht => firstContinuousTermWeightSlope_nonneg D t hD (by linarith [ht.1]))
    (sieveParameter_weight_log_growth D w z hD hw hwz _ hshape)
  dsimp only [Function.comp_def] at h
  rw [integral_sieveParameter_substitution D w z hD hw hwz _ hHc] at h
  apply h.trans
  apply _root_.add_le_add _ le_rfl
  apply parameter_integral_shift_rosserContinuousTerm_le 0
  · simpa [rosserContinuousCutoff] using hs
  · exact (sieveParameter_mem_Icc hD hw ⟨hwz, le_rfl⟩).2

/-- A single density constant controls every positive continuous depth,
including the exceptional first term. -/
theorem weighted_buchstab_allContinuousTerms_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → rosserContinuousCutoff (n + 2) ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          rosserContinuousTerm (n + 1) (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
          rosserContinuousTerm (n + 2) (sieveParameter D z) +
            2 * K * rosserContinuousTerm (n + 1) (sieveParameter D z - 1) / Real.log w := by
  obtain ⟨K₁, hK₁, hb₁⟩ := weighted_buchstab_firstContinuousTerm_bound
  obtain ⟨K₂, hK₂, hb₂⟩ := weighted_buchstab_rosserTerm_bound
  refine ⟨K₁ + K₂, add_pos hK₁ hK₂, ?_⟩
  intro n D w z hD hw hwz hs P hP hodd
  have hs0 : 0 < sieveParameter D z - 1 := by
    linarith [(rosserContinuousCutoff_bounds (n + 2)).1]
  have hf := rosserContinuousTerm_nonneg (n + 1) _ hs0
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  cases n with
  | zero =>
    have hs2 : 2 ≤ sieveParameter D z := by simpa [rosserContinuousCutoff] using hs
    apply (hb₁ D w z hD hw hwz hs2 P hP hodd).trans
    gcongr
    linarith
  | succ n =>
    apply (hb₂ n D w z hD hw hwz hs P hP hodd).trans
    gcongr
    linarith

end Chen.LinearSieve
