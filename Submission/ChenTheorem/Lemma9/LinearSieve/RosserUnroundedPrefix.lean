import Submission.ChenTheorem.Lemma9.LinearSieve.RosserPrefixAbsorption

set_option autoImplicit true
open Filter

namespace Chen.LinearSieve

theorem sieveParameter_adjacent_bound (D : ℝ) (hD : 1 < D) (z : ℕ) (hz : 2 ≤ z) :
    sieveParameter D z ≤ 2 * sieveParameter D (z + 1) := by
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz := Real.log_pos (by linarith : (1 : ℝ) < z)
  have hlogz1 := Real.log_pos (by linarith : (1 : ℝ) < z + 1)
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < z + 1)
    (by nlinarith : (z : ℝ) + 1 ≤ (z : ℝ) ^ 2)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  unfold sieveParameter
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hlogz hlogz1).mpr
  have h := mul_le_mul_of_nonneg_left hlog (Real.log_pos hD).le
  nlinarith

/-- The prefix can be measured at the unrounded parameter s(D,z).
This includes a cube-root cutoff whose actual parent parameter is below three. -/
theorem rosserPartialPrefix_unrounded_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d δ : ℝ, 2 < d → ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D + 1 ≤ z → 3 ≤ sieveParameter D z →
      ∀ upper : Bool,
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        C * Real.exp (-growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError := by
  obtain ⟨K, hK, hpref⟩ := rosserPartialPrefix_growing_uniform_bound
  let C := 4 * (1 + K / Real.log 2)
  have hC : 0 < C := by
    dsimp [C]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  refine ⟨2 * C, by positivity, ?_⟩
  intro d δ hd
  filter_upwards [hpref d δ hd, eventually_inflatedAuxiliaryError_transport d δ (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hp htrans hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro P hP hodd N z hmz hs upper
  have hz : 2 ≤ z := by omega
  have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hsp := sieveParameter_pos hD (show 1 < (z : ℝ) + 1 by linarith)
  have hsz : 0 < sieveParameter D z := by linarith
  have hst : sieveParameter D z ≤ sieveParameter D (growingPrefixIndex d D + 1) := by
    apply sieveParameter_antitone hD
    · change 1 < (growingPrefixIndex d D : ℝ) + 1
      exact_mod_cast (show 1 < growingPrefixIndex d D + 1 by omega)
    · exact hzR
    · exact_mod_cast hmz
  have ht0 : 0 < sieveParameter D (growingPrefixIndex d D + 1) := hsz.trans_le hst
  have hσ := (growingSieveParameter_pos d (Real.log D) hL).le
  have hb := (hp P hP hodd N z (by omega) upper).1
  have ht := (htrans.2 _ _ hs hst hhi).1
  have hratio := sieveParameter_adjacent_bound D hD z hz
  have hcoef : C * growingSieveParameter d (Real.log D) / sieveParameter D (z + 1) ≤
      (2 * C) * growingSieveParameter d (Real.log D) / sieveParameter D z := by
    apply (div_le_div_iff₀ hsp hsz).mpr
    have h := mul_le_mul_of_nonneg_left hratio (mul_nonneg hC.le hσ)
    nlinarith
  have hEt := inflatedAuxiliaryError_nonneg d δ D _ upperAuxiliaryError hD ht0.le
    (upperAuxiliaryError_nonneg _ (by linarith))
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le) hEt)
  exact growingPrefix_bound_transport _ _ _ _ _ _ _ _ (by positivity) hσ hsz ht0 hlo
    (Real.exp_pos _).le (inflatedAuxiliaryError_nonneg d δ D _ upperAuxiliaryError hD hsz.le
      (upperAuxiliaryError_nonneg _ (by linarith))) hb' ht

theorem rosserPartialPrefix_unrounded_upper_inverse_small (d δ ε : ℝ) (hd : 2 < d) (hε : 0 < ε) :
    ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D + 1 ≤ z → 3 ≤ sieveParameter D z →
      ∀ upper : Bool,
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (ε / growingSieveParameter d (Real.log D)) *
          inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError := by
  obtain ⟨C, _, hb⟩ := rosserPartialPrefix_unrounded_upper_bound
  filter_upwards [hb d δ hd, eventually_growingPrefix_coefficient_small d C ε (by linarith) hε,
    eventually_gt_atTop (1 : ℝ)] with D hb he hD
  intro P hP hodd N z hmz hs upper
  exact (hb P hP hodd N z hmz hs upper).trans (mul_le_mul_of_nonneg_right he
    (inflatedAuxiliaryError_nonneg d δ D _ upperAuxiliaryError hD (by linarith)
      (upperAuxiliaryError_nonneg _ (by linarith))))

end Chen.LinearSieve
