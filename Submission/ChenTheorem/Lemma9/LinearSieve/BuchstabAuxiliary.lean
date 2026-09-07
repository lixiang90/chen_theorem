import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryWeightDerivative
import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabRight
import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabParameter

set_option autoImplicit true
open Finset Set MeasureTheory

namespace Chen.LinearSieve

theorem weighted_buchstab_auxiliary_parameter_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ δ a : ℝ, ∀ H S : ℝ → ℝ,
      0 ≤ δ → 0 ≤ a → ContinuousOn H (Ioi a) →
      (∀ s ∈ Ioi a, 0 ≤ H s) → (∀ s, 0 ≤ S s) →
      AntitoneOn (fun s => s ^ 2 * H s) (Ioi a) →
      (∀ s ∈ Ioi a, HasDerivWithinAt H (-(S s + 2 * H s) / s) (Iio s) s) →
      ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z → a + 1 < sieveParameter D z →
      IntegrableOn (fun t => S (sieveParameter D t - 1)) (Icc w (z : ℝ)) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, childAuxiliaryWeight δ (sieveParameter D p) *
          H (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        (1 / sieveParameter D z) * (∫ s in Ioc (sieveParameter D z) (sieveParameter D w),
          childAuxiliaryWeight δ s * H (s - 1)) +
        2 * K * (childAuxiliaryWeight δ (sieveParameter D z) * H (sieveParameter D z - 1)) /
          Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_partial_summation_of_hasDeriv_right
  refine ⟨K, hK, ?_⟩
  intro δ a H S hδ ha hHc hHn hSn hanti hleft D w z hD hw hwz hs hSi P hP hodd
  have hpos : ∀ t ∈ Icc w (z : ℝ), a + 1 < sieveParameter D t :=
    fun t ht => hs.trans_le (sieveParameter_mem_Icc hD hw ht).1
  have hparam : ∀ t ∈ Icc (sieveParameter D z) (sieveParameter D w), a + 1 < t :=
    fun t ht => hs.trans_le ht.1
  have hshift : ContinuousOn (fun t => H (t - 1))
      (Icc (sieveParameter D z) (sieveParameter D w)) :=
    hHc.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change a < t - 1; linarith [hparam t ht])
  have hweight := (continuousOn_childAuxiliaryWeight δ).mono
    (show Icc (sieveParameter D z) (sieveParameter D w) ⊆ Ioi 1 from
      fun t ht => by change 1 < t; linarith [hparam t ht])
  have hH : ContinuousOn (fun t => childAuxiliaryWeight δ t * H (t - 1))
      (Icc (sieveParameter D z) (sieveParameter D w)) := hweight.mul hshift
  have hfc := hH.comp (continuousOn_sieveParameter D w z hw)
    (fun t ht => sieveParameter_mem_Icc hD hw ht)
  have hshape := (antitoneOn_mul_childAuxiliaryWeight_shift δ a H (by linarith) ha hHn hanti).mono
    (show Icc (sieveParameter D z) (sieveParameter D w) ⊆ Ioi (a + 1) from hparam)
  have h := hb w z hw hwz P hP hodd _ (auxiliaryPrimeSlope δ H S D) hfc
    (fun t ht => hasDerivWithinAt_auxiliaryPrimeWeight_right δ D t H S hD
      (by linarith [ht.1]) (by linarith [hpos t ⟨ht.1.le, ht.2.le⟩])
      (hleft _ (by change a < sieveParameter D t - 1; linarith [hpos t ⟨ht.1.le, ht.2.le⟩])))
    (integrableOn_auxiliaryPrimeSlope δ D w z a H S hD hw ha hs hHc hSi)
    (fun t ht => mul_nonneg (childAuxiliaryWeight_nonneg δ _ (by linarith [hpos t ht]))
      (hHn _ (by change a < sieveParameter D t - 1; linarith [hpos t ht])))
    (fun t ht => auxiliaryPrimeSlope_nonneg δ D t H S hδ hD (by linarith [ht.1])
      (by linarith [hpos t ht])
      (hHn _ (by change a < sieveParameter D t - 1; linarith [hpos t ht])) (hSn _))
    (sieveParameter_weight_log_growth D w z hD hw hwz _ hshape)
  dsimp only [Function.comp_def] at h
  rwa [integral_sieveParameter_substitution D w z hD hw hwz _ hH] at h

theorem weighted_buchstab_auxiliary_lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ δ D w : ℝ, ∀ z : ℕ,
      0 ≤ δ → δ ≤ 1 → 1 < D → 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, childAuxiliaryWeight δ (sieveParameter D p) *
          lowerAuxiliaryError (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        sieveParameter D z * upperAuxiliaryError (sieveParameter D z) +
        2 * K * (childAuxiliaryWeight δ (sieveParameter D z) *
          lowerAuxiliaryError (sieveParameter D z - 1)) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_auxiliary_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro δ D w z hδ hδ1 hD hw hwz hs P hP hodd
  have hu : ContinuousOn (fun t => sieveParameter D t - 1) (Icc w (z : ℝ)) :=
    (continuousOn_sieveParameter D w z hw).sub continuousOn_const
  have hum : Measurable (fun t => sieveParameter D t - 1) := by unfold sieveParameter; fun_prop
  have h := hb δ 0 lowerAuxiliaryError lowerAuxiliaryLeftSource hδ le_rfl
    continuousOn_lowerAuxiliaryError (fun s hs => lowerAuxiliaryError_nonneg s hs)
    lowerAuxiliaryLeftSource_nonneg antitoneOn_sq_mul_lowerAuxiliaryError
    (fun s hs => hasDerivWithinAt_lowerAuxiliaryError_left s hs)
    D w z hD hw hwz (by linarith) (integrableOn_lowerAuxiliaryLeftSource_comp w z _ hu hum) P hP hodd
  have hszw : sieveParameter D z ≤ sieveParameter D w :=
    (sieveParameter_mem_Icc hD hw (show (z : ℝ) ∈ Icc w z from ⟨hwz, le_rfl⟩)).2
  have hi := parameter_integral_childAuxiliaryWeight_lower_le δ _ _ hδ1 hs hszw
  rw [intervalIntegral.integral_of_le hszw] at hi
  exact h.trans (_root_.add_le_add hi le_rfl)

theorem weighted_buchstab_auxiliary_upper_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ δ D w : ℝ, ∀ z : ℕ,
      0 ≤ δ → δ ≤ 1 → 1 < D → 2 ≤ w → w ≤ z → 2 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, childAuxiliaryWeight δ (sieveParameter D p) *
          upperAuxiliaryError (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        sieveParameter D z * lowerAuxiliaryError (sieveParameter D z) +
        2 * K * (childAuxiliaryWeight δ (sieveParameter D z) *
          upperAuxiliaryError (sieveParameter D z - 1)) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_auxiliary_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro δ D w z hδ hδ1 hD hw hwz hs P hP hodd
  have hu : ContinuousOn (fun t => sieveParameter D t - 1) (Icc w (z : ℝ)) :=
    (continuousOn_sieveParameter D w z hw).sub continuousOn_const
  have hum : Measurable (fun t => sieveParameter D t - 1) := by unfold sieveParameter; fun_prop
  have h := hb δ 1 upperAuxiliaryError upperAuxiliaryLeftSource hδ (by norm_num)
    continuousOn_upperAuxiliaryError (fun s hs => upperAuxiliaryError_nonneg s hs)
    upperAuxiliaryLeftSource_nonneg antitoneOn_sq_mul_upperAuxiliaryError
    (fun s hs => hasDerivWithinAt_upperAuxiliaryError_left s hs)
    D w z hD hw hwz (by linarith) (integrableOn_upperAuxiliaryLeftSource_comp w z _ hu hum) P hP hodd
  have hszw : sieveParameter D z ≤ sieveParameter D w :=
    (sieveParameter_mem_Icc hD hw (show (z : ℝ) ∈ Icc w z from ⟨hwz, le_rfl⟩)).2
  have hi := parameter_integral_childAuxiliaryWeight_upper_le δ _ _ hδ1 hs hszw
  rw [intervalIntegral.integral_of_le hszw] at hi
  exact h.trans (_root_.add_le_add hi le_rfl)

end Chen.LinearSieve
