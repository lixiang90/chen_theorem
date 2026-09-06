import ChenTheorem.Lemma9.LinearSieve.RosserUpperTransport

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem sieveParameter_ratio (D w z : ℝ) (hD : 1 < D) (hw : 1 < w) (hz : 1 < z) :
    sieveParameter D w / sieveParameter D z = Real.log z / Real.log w := by
  have hD0 := (Real.log_pos hD).ne'
  have hw0 := (Real.log_pos hw).ne'
  have hz0 := (Real.log_pos hz).ne'
  unfold sieveParameter
  field_simp

/-- Transfer a weighted numerator bound at the stopping cutoff to the
terminal cutoff, retaining the quantitative density error. -/
theorem rosser_upper_transport_numerator_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, ∀ m z : ℕ, 1 < D → 2 ≤ m → m ≤ z →
      D ≤ ((m + 1 : ℕ) : ℝ) ^ 3 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ B : ℝ, sieveParameter D m * (1 + rosserRelativeDefect P (m + 1) true D) ≤ B →
        rosserRelativeDefect P (z + 1) true D ≤ B / sieveParameter D z - 1 +
          K * B / (Real.log m * sieveParameter D z) := by
  obtain ⟨K, hK, hb⟩ := primeDensity_sieveProduct_dimension_one
  refine ⟨K, hK, ?_⟩
  intro D m z hD hm hmz hcube P hP hodd B hnum
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hzR : (1 : ℝ) < z := hmR.trans_le (by exact_mod_cast hmz)
  have hsm := sieveParameter_pos hD hmR
  have hsz := sieveParameter_pos hD hzR
  have hlm := Real.log_pos hmR
  have hfac : 0 ≤ 1 + K / Real.log m := by positivity
  have hmain : 0 ≤ 1 + rosserRelativeDefect P (m + 1) true D := by
    linarith [rosserRelativeDefect_nonneg P hP hodd (m + 1) true D]
  have hratio := hb m z hm hmz P hP hodd
  rw [← sieveParameter_ratio D m z hD hmR hzR] at hratio
  rw [rosserRelativeDefect_upper_transport_of_cube P hP hodd m z hmz D hcube]
  calc
    _ ≤ ((1 + K / Real.log m) * (sieveParameter D m / sieveParameter D z)) *
        (1 + rosserRelativeDefect P (m + 1) true D) - 1 := by
      exact sub_le_sub_right (mul_le_mul_of_nonneg_right hratio hmain) 1
    _ = (1 + K / Real.log m) / sieveParameter D z *
        (sieveParameter D m * (1 + rosserRelativeDefect P (m + 1) true D)) - 1 := by ring
    _ ≤ (1 + K / Real.log m) / sieveParameter D z * B - 1 :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left hnum (div_nonneg hfac hsz.le)) 1
    _ = _ := by ring

/-- In the upper initial interval the transferred main term is the
actual continuous error, with both numerator and density losses explicit. -/
theorem rosser_upper_initial_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, ∀ m z : ℕ, 1 < D → 2 ≤ m → m ≤ z →
      D ≤ ((m + 1 : ℕ) : ℝ) ^ 3 → 1 < sieveParameter D z → sieveParameter D z ≤ 3 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ e : ℝ, sieveParameter D m * (1 + rosserRelativeDefect P (m + 1) true D) ≤
        linearSieveInitialConstant + e →
        rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D z) +
          e / sieveParameter D z +
          K * (linearSieveInitialConstant + e) / (Real.log m * sieveParameter D z) := by
  obtain ⟨K, hK, hb⟩ := rosser_upper_transport_numerator_bound
  refine ⟨K, hK, ?_⟩
  intro D m z hD hm hmz hcube hs hs3 P hP hodd e hnum
  have h := hb D m z hD hm hmz hcube P hP hodd (linearSieveInitialConstant + e) hnum
  rw [upperContinuousError_initial _ hs hs3]
  convert! h using 1
  ring

/-- A sufficiently large stopping cutoff makes the density loss small
uniformly throughout the initial upper interval. Only the local
numerator estimate remains as an induction input. -/
theorem eventually_rosser_upper_initial_comparison (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ D : ℝ, ∀ z : ℕ, 1 < D → m ≤ z →
      D ≤ ((m + 1 : ℕ) : ℝ) ^ 3 → 1 < sieveParameter D z → sieveParameter D z ≤ 3 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      sieveParameter D m * (1 + rosserRelativeDefect P (m + 1) true D) ≤
        linearSieveInitialConstant + ε / 2 →
      rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D z) + ε := by
  obtain ⟨K, hK, hb⟩ := rosser_upper_initial_comparison
  have hA : 0 < linearSieveInitialConstant + ε / 2 := by
    linarith [linearSieveInitialConstant_ge_three]
  have hlim : Tendsto (fun m : ℕ => K * (linearSieveInitialConstant + ε / 2) / Real.log m)
      atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))]
    with m hm herr
  intro D z hD hmz hcube hs hs3 P hP hodd hnum
  have h := hb D m z hD hm hmz hcube hs hs3 P hP hodd (ε / 2) hnum
  have hs0 : 0 < sieveParameter D z := by linarith
  have hlm : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have he : (ε / 2) / sieveParameter D z ≤ ε / 2 :=
    (div_le_iff₀ hs0).mpr (by nlinarith)
  have hd : K * (linearSieveInitialConstant + ε / 2) /
      (Real.log m * sieveParameter D z) ≤ ε / 2 := by
    rw [← div_div]
    have hn : 0 ≤ K * (linearSieveInitialConstant + ε / 2) / Real.log m := by positivity
    have hdiv : (K * (linearSieveInitialConstant + ε / 2) / Real.log m) / sieveParameter D z ≤
        K * (linearSieveInitialConstant + ε / 2) / Real.log m :=
      (div_le_iff₀ hs0).mpr (by nlinarith)
    exact hdiv.trans herr.le
  linarith

end Chen.LinearSieve
