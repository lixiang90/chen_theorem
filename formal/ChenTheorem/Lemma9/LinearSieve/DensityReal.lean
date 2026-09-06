import ChenTheorem.Lemma9.LinearSieve.DensityQuantitative

open Finset

namespace Chen.LinearSieve

/-- The floor changes a logarithmic cutoff by at most `log 2`. -/
theorem log_floor_cutoff_bounds (t : ℝ) (ht : 2 ≤ t) :
    0 < Real.log (⌊t⌋₊ : ℝ) ∧
      Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t ∧
      Real.log t ≤ Real.log (⌊t⌋₊ : ℝ) + Real.log 2 ∧
      Real.log t ≤ 2 * Real.log (⌊t⌋₊ : ℝ) := by
  have hn : 2 ≤ ⌊t⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast ht)
  have hnR : (2 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < ⌊t⌋₊ := by linarith
  have hln := Real.log_pos (show (1 : ℝ) < ⌊t⌋₊ by linarith)
  have h2n : Real.log 2 ≤ Real.log (⌊t⌋₊ : ℝ) := Real.log_le_log (by norm_num) hnR
  have hlnt := Real.log_le_log hn0 (Nat.floor_le (show 0 ≤ t by linarith))
  have ht2n : t ≤ 2 * (⌊t⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one t
    linarith
  have hupper := Real.log_le_log (show 0 < t by linarith) ht2n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne'] at hupper
  exact ⟨hln, hlnt, by linarith, by linarith⟩

/-- The dimension-one bound holds for all real endpoints as well.
The constant absorbs the floor error uniformly, including small cutoffs. -/
theorem primeDensity_sieveProduct_real_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        sieveProduct P primeDensity (⌊w⌋₊ + 1) /
          sieveProduct P primeDensity (⌊z⌋₊ + 1) ≤
            (1 + K / Real.log w) * (Real.log z / Real.log w) := by
  obtain ⟨K, hK, hbound⟩ := primeDensity_sieveProduct_dimension_one
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨6 * K + 2 * Real.log 2, by positivity, ?_⟩
  intro w z hw hwz P hP hodd
  obtain ⟨hlm, hlmw, hwm, hw2m⟩ := log_floor_cutoff_bounds w hw
  obtain ⟨hln, hlnz, _, _⟩ := log_floor_cutoff_bounds z (hw.trans hwz)
  have hlw : 0 < Real.log w := hlm.trans_le hlmw
  have hlz : 0 < Real.log z := hln.trans_le hlnz
  have hl2w : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have hKfloor : K / Real.log (⌊w⌋₊ : ℝ) ≤ 2 * K / Real.log w := by
    apply (div_le_div_iff₀ hlm hlw).mpr
    nlinarith
  have h2floor : Real.log 2 / Real.log (⌊w⌋₊ : ℝ) ≤
      2 * Real.log 2 / Real.log w := by
    apply (div_le_div_iff₀ hlm hlw).mpr
    nlinarith
  have hratio : Real.log w / Real.log (⌊w⌋₊ : ℝ) ≤
      1 + 2 * Real.log 2 / Real.log w := by
    calc
      _ ≤ (Real.log (⌊w⌋₊ : ℝ) + Real.log 2) / Real.log (⌊w⌋₊ : ℝ) :=
        div_le_div_of_nonneg_right hwm hlm.le
      _ = 1 + Real.log 2 / Real.log (⌊w⌋₊ : ℝ) := by rw [add_div, div_self hlm.ne']
      _ ≤ _ := _root_.add_le_add le_rfl h2floor
  have hcross : 4 * K * Real.log 2 / (Real.log w * Real.log w) ≤ 4 * K / Real.log w := by
    apply (div_le_div_iff₀ (mul_pos hlw hlw) hlw).mpr
    nlinarith [mul_nonneg (show 0 ≤ 4 * K * Real.log w by positivity)
      (sub_nonneg.mpr hl2w)]
  have hfactor : (1 + 2 * K / Real.log w) * (1 + 2 * Real.log 2 / Real.log w) ≤
      1 + (6 * K + 2 * Real.log 2) / Real.log w := by
    calc
      _ = 1 + (2 * K + 2 * Real.log 2) / Real.log w +
          4 * K * Real.log 2 / (Real.log w * Real.log w) := by ring
      _ ≤ 1 + (2 * K + 2 * Real.log 2) / Real.log w + 4 * K / Real.log w :=
        _root_.add_le_add le_rfl hcross
      _ = _ := by ring
  calc
    _ ≤ (1 + K / Real.log (⌊w⌋₊ : ℝ)) *
        (Real.log (⌊z⌋₊ : ℝ) / Real.log (⌊w⌋₊ : ℝ)) :=
      hbound ⌊w⌋₊ ⌊z⌋₊ ((Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hw))
        (Nat.floor_mono hwz) P hP hodd
    _ ≤ (1 + 2 * K / Real.log w) * (Real.log z / Real.log (⌊w⌋₊ : ℝ)) := by
      gcongr
    _ = (Real.log z / Real.log w) *
        ((1 + 2 * K / Real.log w) * (Real.log w / Real.log (⌊w⌋₊ : ℝ))) := by
      field_simp
    _ ≤ (Real.log z / Real.log w) *
        ((1 + 2 * K / Real.log w) * (1 + 2 * Real.log 2 / Real.log w)) := by
      apply mul_le_mul_of_nonneg_left _ (div_pos hlz hlw).le
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ (Real.log z / Real.log w) * (1 + (6 * K + 2 * Real.log 2) / Real.log w) :=
      mul_le_mul_of_nonneg_left hfactor (div_pos hlz hlw).le
    _ = _ := by ring

end Chen.LinearSieve
