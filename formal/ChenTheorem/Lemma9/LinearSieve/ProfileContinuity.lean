import ChenTheorem.Lemma9.LinearSieve.ChenProfileIdentity

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

noncomputable def chenContinuousSieveProfile (a : ℝ) : ℝ :=
  20 * Real.exp (-Real.eulerMascheroniConstant) * lowerLinearSieveFunction (10 * a) -
    10 * Real.exp (-Real.eulerMascheroniConstant) *
      ∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α

theorem upperLinearSieveFunction_le_five (s : ℝ) (hs : 3 / 2 ≤ s) :
    upperLinearSieveFunction s ≤ 5 := by
  have h := (upperContinuousError_bounds s (by linarith)).2
  have hm : 3 / 2 ≤ min s 2 := le_min hs (by norm_num)
  have hp : 0 < min s 2 - 1 := by linarith
  have hdiv : 2 / (min s 2 - 1) ≤ 4 := (div_le_iff₀ hp).mpr (by linarith)
  unfold upperLinearSieveFunction
  linarith

theorem continuousAt_weightedSieveIntegral_half :
    ContinuousAt (fun a : ℝ => ∫ α : ℝ in (1 / 10)..(1 / 3),
      upperLinearSieveFunction (10 * a - 10 * α) / α) (1 / 2) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (1 / 2 : ℝ)) (μ := volume.restrict (Ioc (1 / 10 : ℝ) (1 / 3)))
    (F := fun a α : ℝ => upperLinearSieveFunction (10 * a - 10 * α) / α)
    (f := fun α : ℝ => upperLinearSieveFunction (10 * (1 / 2) - 10 * α) / α)
    (fun _ => (50 : ℝ)) ?_ ?_ (integrable_const 50) ?_
  · simpa only [ContinuousAt, intervalIntegral.integral_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)] using h
  · filter_upwards [Ioi_mem_nhds (by norm_num : (29 / 60 : ℝ) < 1 / 2)] with a ha
    change 29 / 60 < a at ha
    have hc : ContinuousOn (fun α : ℝ => upperLinearSieveFunction (10 * a - 10 * α) / α)
        (Ioc (1 / 10) (1 / 3)) := by
      apply (continuousOn_upperLinearSieveFunction.comp
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
        (fun α hα => by change 1 < 10 * a - 10 * α; linarith [hα.2])).div continuousOn_id
      intro α hα
      change α ≠ 0
      linarith [hα.1]
    exact hc.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Ioi_mem_nhds (by norm_num : (29 / 60 : ℝ) < 1 / 2)] with a ha
    change 29 / 60 < a at ha
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with α hα
    have hs : 3 / 2 ≤ 10 * a - 10 * α := by linarith [hα.2]
    have hF := upperLinearSieveFunction_le_five _ hs
    have hF0 := upperLinearSieveFunction_ge_one (10 * a - 10 * α) (by linarith)
    have hα0 : 0 < α := by linarith [hα.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hα0.le)]
    apply (div_le_iff₀ hα0).mpr
    linarith [hα.1]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with α hα
    have hc : ContinuousAt upperLinearSieveFunction (10 * (1 / 2) - 10 * α) :=
      continuousOn_upperLinearSieveFunction.continuousAt
        (Ioi_mem_nhds (by linarith [hα.2]))
    exact (ContinuousAt.comp' (f := fun a : ℝ => 10 * a - 10 * α) (x := (1 / 2 : ℝ)) hc
      ((continuousAt_const.mul continuousAt_id).sub continuousAt_const)).div_const α

theorem continuousAt_chenContinuousSieveProfile_half :
    ContinuousAt chenContinuousSieveProfile (1 / 2) := by
  have hf : ContinuousAt (fun a : ℝ => lowerLinearSieveFunction (10 * a)) (1 / 2) :=
    ContinuousAt.comp' (f := fun a : ℝ => 10 * a) (x := (1 / 2 : ℝ))
      (continuousOn_lowerLinearSieveFunction.continuousAt (Ici_mem_nhds (by norm_num)))
      (continuousAt_const.mul continuousAt_id)
  exact (continuousAt_const.mul hf).sub (continuousAt_const.mul continuousAt_weightedSieveIntegral_half)

theorem chenContinuousSieveProfile_half :
    chenContinuousSieveProfile (1 / 2) = 8 * (Real.log 4 - Real.log 8 / 2 + equation27Integral) := by
  unfold chenContinuousSieveProfile
  norm_num only [show (10 : ℝ) * (1 / 2) = 5 by norm_num]
  exact chen_continuous_sieve_profile_identity

theorem exists_chenContinuousSieveProfile_near_half (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 29 / 60 < a ∧ a < 1 / 2 ∧
      8 * (Real.log 4 - Real.log 8 / 2 + equation27Integral) - ε < chenContinuousSieveProfile a := by
  have h := continuousAt_chenContinuousSieveProfile_half.tendsto.eventually
    (Ioi_mem_nhds (show chenContinuousSieveProfile (1 / 2) - ε < chenContinuousSieveProfile (1 / 2) by linarith))
  have hh : ∀ᶠ a : ℝ in 𝓝[<] (1 / 2), 29 / 60 < a ∧ a < 1 / 2 ∧
      chenContinuousSieveProfile (1 / 2) - ε < chenContinuousSieveProfile a := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds h,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (29 / 60 : ℝ) < 1 / 2)),
      self_mem_nhdsWithin] with a ha hlow hhigh
    exact ⟨hlow, hhigh, ha⟩
  rw [chenContinuousSieveProfile_half] at hh
  exact hh.exists

theorem chen_equation26_bracket_pos :
    0 < Real.log 4 - Real.log 8 / 2 + equation27Integral := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 2
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 3
  rw [h4, h8]
  norm_num at h2
  linarith [equation27_integral_bound]

theorem exists_chenContinuousSieveProfile_relative_loss (δ : ℝ) (hδ : 0 < δ) :
    ∃ a : ℝ, 29 / 60 < a ∧ a < 1 / 2 ∧
      (8 - δ) * (Real.log 4 - Real.log 8 / 2 + equation27Integral) < chenContinuousSieveProfile a := by
  obtain ⟨a, ha, ha', h⟩ := exists_chenContinuousSieveProfile_near_half
    (δ * (Real.log 4 - Real.log 8 / 2 + equation27Integral))
    (mul_pos hδ chen_equation26_bracket_pos)
  exact ⟨a, ha, ha', by nlinarith [h]⟩

end Chen.LinearSieve
