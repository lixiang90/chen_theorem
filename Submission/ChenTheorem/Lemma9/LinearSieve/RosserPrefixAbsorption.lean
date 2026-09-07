import Submission.ChenTheorem.Lemma9.LinearSieve.RosserParentPrefix
import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedLowerMonotonicity

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The lower parent prefix estimate includes the endpoint two. -/
theorem rosserPartialPrefix_lower_parent_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d δ : ℝ, 2 < d → ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D ≤ z → 2 ≤ sieveParameter D (z + 1) →
      ∀ upper : Bool,
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        C * Real.exp (-growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError := by
  obtain ⟨K, hK, hpref⟩ := rosserPartialPrefix_growing_uniform_bound
  let C := 4 * (1 + K / Real.log 2)
  have hC : 0 < C := by
    dsimp [C]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  refine ⟨C, hC, ?_⟩
  intro d δ hd
  filter_upwards [hpref d δ hd, eventually_inflatedLowerAuxiliaryError_transport d δ (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hp htrans hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro P hP hodd N z hmz hs upper
  have hst : sieveParameter D (z + 1) ≤ sieveParameter D (growingPrefixIndex d D + 1) := by
    apply sieveParameter_antitone hD
    · change 1 < (growingPrefixIndex d D : ℝ) + 1
      exact_mod_cast (show 1 < growingPrefixIndex d D + 1 by omega)
    · change 1 < (z : ℝ) + 1
      exact_mod_cast (show 1 < z + 1 by omega)
    · exact_mod_cast Nat.add_le_add_right hmz 1
  have ht0 : 0 < sieveParameter D (growingPrefixIndex d D + 1) := by linarith
  have hσ := (growingSieveParameter_pos d (Real.log D) hL).le
  have hb := (hp P hP hodd N z hmz upper).2
  have ht := htrans.2 _ _ hs hst hhi
  exact growingPrefix_bound_transport _ _ _ _ _ _ _ _ hC.le hσ (by linarith) ht0 hlo
    (Real.exp_pos _).le
    (inflatedAuxiliaryError_nonneg d δ D _ lowerAuxiliaryError hD (by linarith)
      (lowerAuxiliaryError_nonneg _ (by linarith))) hb ht

/-- Exponential prefix decay dominates the inverse growing parameter. -/
theorem eventually_growingPrefix_coefficient_small (d C ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop,
      C * Real.exp (-growingSieveParameter d (Real.log D)) ≤ ε / growingSieveParameter d (Real.log D) := by
  have hg := (tendsto_growingSieveParameter_atTop d hd).comp Real.tendsto_log_atTop
  have he := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)).comp hg).const_mul C
  simp only [Real.rpow_one, neg_one_mul, mul_zero] at he
  filter_upwards [he.eventually (gt_mem_nhds hε), hg.eventually (eventually_gt_atTop 0)] with D he hσ
  dsimp only [Function.comp_def] at he hσ
  apply (le_div_iff₀ hσ).mpr
  convert! he.le using 1
  ring

theorem rosserPartialPrefix_parent_inverse_small (d δ ε : ℝ) (hd : 2 < d) (hε : 0 < ε) :
    ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D ≤ z → 3 ≤ sieveParameter D (z + 1) →
      ∀ upper : Bool,
      (rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (ε / growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError) ∧
      (rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (ε / growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError) := by
  obtain ⟨C, _, hb⟩ := rosserPartialPrefix_parent_bound
  filter_upwards [hb d δ hd, eventually_growingPrefix_coefficient_small d C ε (by linarith) hε,
    eventually_gt_atTop (1 : ℝ)] with D hb he hD
  intro P hP hodd N z hmz hs upper
  have h := hb P hP hodd N z hmz hs upper
  have hu := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1)) upperAuxiliaryError hD (by linarith)
    (upperAuxiliaryError_nonneg _ (by linarith))
  have hl := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError hD (by linarith)
    (lowerAuxiliaryError_nonneg _ (by linarith))
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right he hu), h.2.trans (mul_le_mul_of_nonneg_right he hl)⟩

theorem rosserPartialPrefix_lower_parent_inverse_small (d δ ε : ℝ) (hd : 2 < d) (hε : 0 < ε) :
    ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D ≤ z → 2 ≤ sieveParameter D (z + 1) →
      ∀ upper : Bool,
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (ε / growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError := by
  obtain ⟨C, _, hb⟩ := rosserPartialPrefix_lower_parent_bound
  filter_upwards [hb d δ hd, eventually_growingPrefix_coefficient_small d C ε (by linarith) hε,
    eventually_gt_atTop (1 : ℝ)] with D hb he hD
  intro P hP hodd N z hmz hs upper
  exact (hb P hP hodd N z hmz hs upper).trans (mul_le_mul_of_nonneg_right he
    (inflatedAuxiliaryError_nonneg d δ D _ lowerAuxiliaryError hD (by linarith)
      (lowerAuxiliaryError_nonneg _ (by linarith))))

end Chen.LinearSieve
