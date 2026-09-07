import Submission.ChenTheorem.Lemma9.LinearSieve.RosserSecondComparison

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

/-- A split whose fourth power is much smaller than the total level. -/
noncomputable def secondDepthCutoff (D : ℝ) : ℝ := D ^ ((8 : ℝ)⁻¹)

theorem secondDepthCutoff_pow (D : ℝ) (hD : 0 ≤ D) :
    secondDepthCutoff D ^ 8 = D :=
  Real.rpow_inv_natCast_pow hD (by norm_num)

theorem log_secondDepthCutoff (D : ℝ) (hD : 0 < D) :
    Real.log (secondDepthCutoff D) = Real.log D / 8 := by
  rw [secondDepthCutoff, Real.log_rpow hD]
  ring

theorem secondDepthCutoff_tendsto : Tendsto secondDepthCutoff atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (8 : ℝ)⁻¹)

/-- The rounding needed for the small terminal-cutoff case is absorbed
by the gap between the fourth and eighth powers. -/
theorem secondDepthCutoff_small_terminal (D : ℝ) (hD : 0 ≤ D)
    (hw : 3 ≤ secondDepthCutoff D) (z : ℕ) (hz : (z : ℝ) < secondDepthCutoff D) :
    ((z + 1 : ℕ) : ℝ) ^ 4 < D := by
  have hw0 : 0 ≤ secondDepthCutoff D := by linarith
  have hbound : ((z + 1 : ℕ) : ℝ) ≤ 2 * secondDepthCutoff D := by push_cast; linarith
  have hp : ((z + 1 : ℕ) : ℝ) ^ 4 ≤ (2 * secondDepthCutoff D) ^ 4 := by gcongr
  have hw4 : 81 ≤ secondDepthCutoff D ^ 4 := by
    calc
      (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ _ := by gcongr
  have hpow := secondDepthCutoff_pow D hD
  nlinarith [sq_nonneg (secondDepthCutoff D ^ 4 - 16),
    show secondDepthCutoff D ^ 8 = (secondDepthCutoff D ^ 4) ^ 2 by ring,
    show (2 * secondDepthCutoff D) ^ 4 = 16 * secondDepthCutoff D ^ 4 by ring]

theorem secondDepthCutoff_prefix_level (D : ℝ) (hD : 0 ≤ D)
    (hw : 3 ≤ secondDepthCutoff D) : (⌊secondDepthCutoff D⌋₊ : ℝ) ^ 4 < D := by
  have hw0 : 0 ≤ secondDepthCutoff D := by linarith
  have hf := Nat.floor_le hw0
  have hp : (⌊secondDepthCutoff D⌋₊ : ℝ) ^ 4 ≤ secondDepthCutoff D ^ 4 := by gcongr
  have hw4 : 81 ≤ secondDepthCutoff D ^ 4 := by
    calc
      (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ _ := by gcongr
  have hpow := secondDepthCutoff_pow D hD
  nlinarith [show secondDepthCutoff D ^ 8 = (secondDepthCutoff D ^ 4) ^ 2 by ring]

theorem sieveParameter_gt_two_of_active (D : ℝ) (z : ℕ) (hz : 2 ≤ z)
    (hactive : ((z + 1 : ℕ) : ℝ) ^ 2 < D) : 2 < sieveParameter D z := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hz0 : (0 : ℝ) < z := zero_lt_one.trans hz1
  have hzpow : (z : ℝ) ^ 2 < D := by push_cast at hactive; nlinarith
  have hlog := Real.log_lt_log (pow_pos hz0 2) hzpow
  rw [Real.log_pow] at hlog
  exact (lt_div_iff₀ (Real.log_pos hz1)).mpr (by simpa [mul_comm] using hlog)

theorem firstContinuousTerm_le_two (s : ℝ) (hs : 1 ≤ s) :
    rosserContinuousTerm 1 s ≤ 2 := by
  have h := antitoneOn_rosserContinuousTerm 1 (by norm_num : (0 : ℝ) < 1)
    (show 0 < s by linarith) hs
  norm_num [rosserContinuousTerm_one 1 (by norm_num)] at h
  exact h

theorem secondDepthCutoff_log_ratio_le (D : ℝ) (hD : 1 < D) (z : ℕ)
    (hz : 2 ≤ z) (hs : 2 < sieveParameter D z) (hw : 2 ≤ secondDepthCutoff D) :
    Real.log z / Real.log (secondDepthCutoff D) ≤ 4 := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hlw : 0 < Real.log (secondDepthCutoff D) := Real.log_pos (by linarith)
  have hlog := (lt_div_iff₀ (Real.log_pos hz1)).mp hs
  rw [div_le_iff₀ hlw, log_secondDepthCutoff D (by linarith)]
  linarith

/-- The actual second stopping contribution is uniformly approximated
from above by the second continuous term. No child-state or cutoff-choice
hypothesis remains; the statement covers every terminal cutoff at least two. -/
theorem eventually_rosserSecondMass_le_continuous (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P 2 (z + 1) false D ≤
        rosserContinuousTerm 2 (sieveParameter D z) + ε := by
  obtain ⟨K, hK, hb⟩ := rosserSecondMass_le_continuous_with_errors
  obtain ⟨T, hT, hb⟩ := hb (ε / 16) (by positivity)
  obtain ⟨C, hC, hbound⟩ := primeDensity_sieveProduct_real_dimension_one
  have hlogw := Real.tendsto_log_atTop.comp secondDepthCutoff_tendsto
  have hsmallC : Tendsto (fun D => C / Real.log (secondDepthCutoff D)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := C)).div_atTop hlogw
  have hsmallK : Tendsto (fun D => (4 * K) / Real.log (secondDepthCutoff D)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := 4 * K)).div_atTop hlogw
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (T ^ 2),
    secondDepthCutoff_tendsto.eventually (eventually_ge_atTop 3),
    hsmallC.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmallK.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))]
      with D hD hDT hw hClog hKlog
  intro z hz P hP hodd
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hz0 : (0 : ℝ) < z := zero_lt_one.trans hz1
  have hf0 := rosserContinuousTerm_nonneg 2 _ (sieveParameter_pos hD hz1)
  by_cases hstop : D ≤ ((z + 1 : ℕ) : ℝ) ^ 2
  · simp only [rosserRelativeStoppingMass, rosserStoppingMass,
      true_and, if_pos hstop, zero_div]
    exact add_nonneg hf0 hε.le
  have hactive : ((z + 1 : ℕ) : ℝ) ^ 2 < D := lt_of_not_ge hstop
  by_cases hwz : secondDepthCutoff D ≤ z
  · have hs := sieveParameter_gt_two_of_active D z hz hactive
    have hw2 : 2 ≤ secondDepthCutoff D := by linarith
    have hlw : 0 < Real.log (secondDepthCutoff D) := Real.log_pos (by linarith)
    have hlevel : T ≤ D / z := by
      apply (le_div_iff₀ hz0).mpr
      have hzpow : (z : ℝ) ^ 2 < D := by push_cast at hactive; nlinarith
      rcases le_total (z : ℝ) T with hzT | hTz
      · nlinarith
      · nlinarith
    have h := hb D (secondDepthCutoff D) z hD hw2 hwz hs
      (secondDepthCutoff_prefix_level D (by linarith) hw) hlevel hactive P hP hodd
    have hratio := hbound (secondDepthCutoff D) z hw2 hwz P hP hodd
    simp only [Nat.floor_natCast] at hratio
    have hlogs := secondDepthCutoff_log_ratio_le D hD z hz hs hw2
    have hratio8 : sieveProduct P primeDensity (⌊secondDepthCutoff D⌋₊ + 1) /
        sieveProduct P primeDensity (z + 1) - 1 ≤ 8 := by
      have hprod : (1 + C / Real.log (secondDepthCutoff D)) *
          (Real.log z / Real.log (secondDepthCutoff D)) ≤ 2 * 4 :=
        mul_le_mul (by linarith) hlogs
          (div_nonneg (Real.log_pos hz1).le hlw.le) (by norm_num)
      linarith
    have hf2 := firstContinuousTerm_le_two (sieveParameter D z - 1) (by linarith)
    have hdensity : 2 * K * rosserContinuousTerm 1 (sieveParameter D z - 1) /
        Real.log (secondDepthCutoff D) ≤ 4 * K / Real.log (secondDepthCutoff D) := by
      apply div_le_div_of_nonneg_right _ hlw.le
      nlinarith
    have herr := mul_le_mul_of_nonneg_left hratio8 (show 0 ≤ ε / 16 by positivity)
    linarith
  · have hzsmall : (z : ℝ) < secondDepthCutoff D := lt_of_not_ge hwz
    have hzero := rosserStoppingMass_eq_zero_of_level P hP 2 (z + 1) false D
      (secondDepthCutoff_small_terminal D (by linarith) hw z hzsmall)
    rw [rosserRelativeStoppingMass, hzero, zero_div]
    exact add_nonneg hf0 hε.le

/-- The uniform second-depth estimate at the prime cutoff used by the
next recursive step. -/
theorem eventually_rosserSecondMass_primeCutoff_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ p : ℕ, 3 ≤ p →
      ∀ P : Finset ℕ, (∀ q ∈ P, q.Prime) → (∀ q ∈ P, 2 < q) →
      rosserRelativeStoppingMass P 2 p false D ≤
        rosserContinuousTerm 2 (sieveParameter D p) + ε := by
  filter_upwards [eventually_rosserSecondMass_le_continuous ε hε,
    eventually_gt_atTop (1 : ℝ)] with D hb hD
  intro p hp P hP hodd
  have hpm : 2 ≤ p - 1 := by omega
  have hm1 : (1 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 1 < p - 1 by omega)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hmp : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hparam := sieveParameter_antitone hD hm1 hp1 hmp
  have h := hb (p - 1) hpm P hP hodd
  rw [Nat.sub_add_cancel (by omega)] at h
  exact h.trans (_root_.add_le_add
    (antitoneOn_rosserContinuousTerm 2 (sieveParameter_pos hD hp1)
      (sieveParameter_pos hD hm1) hparam) le_rfl)

end Chen.LinearSieve
