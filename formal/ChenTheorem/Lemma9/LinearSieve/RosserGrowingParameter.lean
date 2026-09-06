import ChenTheorem.Lemma9.LinearSieve.GrowingEnvelopeLimit
import ChenTheorem.Lemma9.LinearSieve.DepthMassLevelBound

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem eventually_auxiliaryComparisonExponent_le_neg (K d δ : ℝ) (hK : 0 < K) (hd : 2 < d) :
    ∀ᶠ D in atTop, 1 < D ∧ 6 ≤ growingSieveParameter d (Real.log D) ∧
      Real.exp 2 ≤ growingSieveParameter d (Real.log D) ∧
      ∀ z : ℕ, 2 ≤ z → growingSieveParameter d (Real.log D) ≤ sieveParameter D (z + 1) →
        auxiliaryComparisonExponent (depthMassMajorant K z) d δ D (sieveParameter D (z + 1)) ≤
          -sieveParameter D (z + 1) := by
  let C := depthMassLevelConstant K
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (depthMassLevelConstant_ge_one K hK)
  have he := Real.tendsto_log_atTop.eventually (eventually_comparisonEnvelope_le_neg_one C d δ hC hd)
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  have hσ := hg.eventually_ge_atTop (max 6 (Real.exp 2))
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hσ, he] with D hD hL hσ he
  have hσ6 : 6 ≤ growingSieveParameter d (Real.log D) := (le_max_left _ _).trans hσ
  have hσ2 : Real.exp 2 ≤ growingSieveParameter d (Real.log D) := (le_max_right _ _).trans hσ
  refine ⟨hD, hσ6, hσ2, ?_⟩
  intro z hz hzs
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hs6 : 6 ≤ sieveParameter D (z + 1) := hσ6.trans hzs
  have hB := depthMassMajorant_gt_one K z hK hzR
  have hBM := depthMassMajorant_le_log_level K D z hK hD hzR (by linarith)
  have hσ1 : Real.exp 1 ≤ growingSieveParameter d (Real.log D) :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hσ2
  have h := auxiliaryComparisonExponent_le_split_envelope (depthMassMajorant K z)
    (C * Real.log D) d δ D (growingSieveParameter d (Real.log D)) (sieveParameter D (z + 1))
      hB.le hBM (by linarith) hL hσ1 hzs
  calc
    _ ≤ sieveParameter D (z + 1) * comparisonEnvelope (C * Real.log D) d δ
        (Real.log D) (growingSieveParameter d (Real.log D)) := h
    _ ≤ sieveParameter D (z + 1) * (-1) := mul_le_mul_of_nonneg_left he (by linarith)
    _ = _ := by ring

/-- Uniform absorption of the actual full defect in the growing
large-parameter range. No child estimate or fixed-depth threshold is
assumed: every prime set, cutoff and sieve sign uses the same eventual level. -/
theorem rosserRelativeDefect_growing_parameter (d δ : ℝ) (hd : 2 < d) :
    ∀ᶠ D in atTop, ∀ z : ℕ, 2 ≤ z →
      growingSieveParameter d (Real.log D) ≤ sieveParameter D (z + 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ upper : Bool,
      rosserRelativeDefect P (z + 1) upper D ≤ Real.exp (-sieveParameter D (z + 1)) *
        inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError ∧
      rosserRelativeDefect P (z + 1) upper D ≤ Real.exp (-sieveParameter D (z + 1)) *
        inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError := by
  obtain ⟨K, hK, hb⟩ := rosserRelativeDefect_le_inflated_auxiliary
  filter_upwards [eventually_auxiliaryComparisonExponent_le_neg K d δ hK hd] with D hD
  intro z hz hzs P hP hodd upper
  have hs6 : 6 ≤ sieveParameter D (z + 1) := hD.2.1.trans hzs
  have hs0 : 0 < sieveParameter D (z + 1) := by linarith
  have hlog : 2 ≤ Real.log (sieveParameter D (z + 1)) :=
    (Real.le_log_iff_exp_le hs0).2 (hD.2.2.1.trans hzs)
  have h := hb z hz P hP hodd upper d δ D hD.1 hs6 hlog
  have he := Real.exp_le_exp.mpr (hD.2.2.2 z hz hzs)
  have hu := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1)) upperAuxiliaryError
    hD.1 hs0.le (upperAuxiliaryError_nonneg _ (by linarith))
  have hl := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError
    hD.1 hs0.le (lowerAuxiliaryError_nonneg _ hs0)
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right he hu),
    h.2.trans (mul_le_mul_of_nonneg_right he hl)⟩

end Chen.LinearSieve
