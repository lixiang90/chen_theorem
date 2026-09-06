import ChenTheorem.Lemma9.LinearSieve.GrowingPrefixCutoff

namespace Chen.LinearSieve

theorem growingPrefix_log_ratio_bound (d D : ℝ) (hD : 1 < D) (hL : 1 < Real.log D)
    (hw : 2 ≤ growingPrefixCutoff d D) (z : ℕ) (hmz : growingPrefixIndex d D ≤ z) :
    Real.log z / Real.log (growingPrefixIndex d D) ≤
      4 * growingSieveParameter d (Real.log D) / sieveParameter D (z + 1) := by
  have hm := (growingPrefixIndex_parameter_bounds d D hD hL hw).1
  have hmR : (2 : ℝ) ≤ growingPrefixIndex d D := by exact_mod_cast hm
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast (hm.trans hmz)
  have hfloor := Nat.lt_floor_add_one (growingPrefixCutoff d D)
  change growingPrefixCutoff d D < (growingPrefixIndex d D : ℝ) + 1 at hfloor
  have hwm : growingPrefixCutoff d D ≤ (growingPrefixIndex d D : ℝ) ^ 2 := by nlinarith
  have hlogw := Real.log_le_log (growingPrefixCutoff_pos d D) hwm
  rw [Real.log_pow] at hlogw
  norm_num only [Nat.cast_ofNat] at hlogw
  have hσ := growingSieveParameter_pos d (Real.log D) hL
  have he : (2 * growingSieveParameter d (Real.log D)) * Real.log (growingPrefixCutoff d D) =
      Real.log D := by rw [log_growingPrefixCutoff]; field_simp
  have hmass := mul_le_mul_of_nonneg_left hlogw (show 0 ≤ 2 * growingSieveParameter d (Real.log D) by positivity)
  rw [he] at hmass
  have hs := sieveParameter_pos hD (by linarith : (1 : ℝ) < (z : ℝ) + 1)
  apply (div_le_div_iff₀ (Real.log_pos (by linarith : (1 : ℝ) < growingPrefixIndex d D)) hs).2
  have hzlog := Real.log_le_log (by linarith : (0 : ℝ) < z) (by linarith : (z : ℝ) ≤ (z : ℝ) + 1)
  have hzmul := mul_le_mul_of_nonneg_right hzlog hs.le
  have hez : Real.log ((z : ℝ) + 1) * sieveParameter D (z + 1) = Real.log D := by
    unfold sieveParameter
    have hn := (Real.log_pos (by linarith : (1 : ℝ) < (z : ℝ) + 1)).ne'
    field_simp
  rw [hez] at hzmul
  nlinarith

theorem growingPrefix_product_ratio_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ d D : ℝ, 1 < D → 1 < Real.log D → 2 ≤ growingPrefixCutoff d D →
      ∀ z : ℕ, growingPrefixIndex d D ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      sieveProduct P primeDensity (growingPrefixIndex d D + 1) / sieveProduct P primeDensity (z + 1) ≤
        (4 * (1 + K / Real.log 2)) * growingSieveParameter d (Real.log D) / sieveParameter D (z + 1) := by
  obtain ⟨K, hK, hb⟩ := primeDensity_sieveProduct_dimension_one
  refine ⟨K, hK, ?_⟩
  intro d D hD hL hw z hmz P hP hodd
  have hm := (growingPrefixIndex_parameter_bounds d D hD hL hw).1
  have hmR : (2 : ℝ) ≤ growingPrefixIndex d D := by exact_mod_cast hm
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast (hm.trans hmz)
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogm := Real.log_pos (by linarith : (1 : ℝ) < growingPrefixIndex d D)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
  have hcoeff := _root_.add_le_add (le_refl (1 : ℝ))
    (div_le_div_of_nonneg_left hK.le hlog2 hlog)
  have hratio := growingPrefix_log_ratio_bound d D hD hL hw z hmz
  have hmul := _root_.mul_le_mul hcoeff hratio
    (div_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ z)) hlogm.le)
    (show 0 ≤ 1 + K / Real.log 2 by positivity)
  calc
    _ ≤ (1 + K / Real.log (growingPrefixIndex d D)) *
        (Real.log z / Real.log (growingPrefixIndex d D)) := hb _ z hm hmz P hP hodd
    _ ≤ (1 + K / Real.log 2) *
        (4 * growingSieveParameter d (Real.log D) / sieveParameter D (z + 1)) := hmul
    _ = _ := by ring

end Chen.LinearSieve
