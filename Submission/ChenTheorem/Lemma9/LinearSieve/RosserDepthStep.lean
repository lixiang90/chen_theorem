import Submission.ChenTheorem.Lemma9.LinearSieve.RosserDepthSplit

set_option autoImplicit true
open Filter Finset
open scoped Topology

namespace Chen.LinearSieve

/-- Uniform comparison at a fixed positive stopping depth. -/
def RosserDepthBound (n : ℕ) (upper : Bool) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z →
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
    rosserRelativeStoppingMass P n (z + 1) upper D ≤ rosserContinuousTerm n (sieveParameter D z) + ε

theorem RosserDepthBound.primeCutoff (n : ℕ) (upper : Bool) (h : RosserDepthBound n upper)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ p : ℕ, 3 ≤ p → 1 < sieveParameter D p →
      ∀ P : Finset ℕ, (∀ q ∈ P, q.Prime) → (∀ q ∈ P, 2 < q) →
      rosserRelativeStoppingMass P n p upper D ≤ rosserContinuousTerm n (sieveParameter D p) + ε := by
  filter_upwards [h ε hε, eventually_gt_atTop (1 : ℝ)] with D hb hD
  intro p hp hs P hP hodd
  have hpm : 2 ≤ p - 1 := by omega
  have hm1 : (1 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 1 < p - 1 by omega)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hmp : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hparam := sieveParameter_antitone hD hm1 hp1 hmp
  have hh := hb (p - 1) hpm (hs.trans_le hparam) P hP hodd
  rw [Nat.sub_add_cancel (by omega)] at hh
  exact hh.trans (_root_.add_le_add
    (antitoneOn_rosserContinuousTerm n (sieveParameter_pos hD hp1)
      (sieveParameter_pos hD hm1) hparam) le_rfl)

/-- A uniform child comparison gives the next depth above its lower
continuous cutoff. All levels, split choices and accumulated child errors
are discharged inside this proof. -/
theorem rosser_depth_large_parameter_step (n : ℕ) (upper : Bool)
    (hchild : RosserDepthBound (n + 1) (!upper)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z →
      rosserContinuousCutoff (n + 2) < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P (n + 2) (z + 1) upper D ≤
        rosserContinuousTerm (n + 2) (sieveParameter D z) + ε := by
  let k := n + 4
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let δ := ε / (4 * (k : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hchild.primeCutoff (n + 1) (!upper) δ hδ)
  let T := max L 2
  have hT : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨K, hK, hstep⟩ := rosserStoppingMass_continuous_step
  obtain ⟨C, hC, hbound⟩ := primeDensity_sieveProduct_real_dimension_one
  let M := rosserContinuousTerm (n + 1) 1
  have hM : 0 ≤ M := rosserContinuousTerm_nonneg (n + 1) 1 (by norm_num)
  have hlogw := Real.tendsto_log_atTop.comp (depthSplit_tendsto k hk)
  have hsmallC : Tendsto (fun D => C / Real.log (depthSplit k D)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogw
  have hsmallK : Tendsto (fun D => (2 * K * M) / Real.log (depthSplit k D)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogw
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (T ^ 2),
    (depthSplit_tendsto k hk).eventually (eventually_ge_atTop 3),
    hsmallC.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmallK.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))]
      with D hD hDT hw hClog hKlog
  intro z hz hs P hP hodd
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hs2 : 2 < sieveParameter D z := lt_of_le_of_lt (rosserContinuousCutoff_bounds _).1 hs
  have hf0 := rosserContinuousTerm_nonneg (n + 2) _ (sieveParameter_pos hD hz1)
  by_cases hstop : upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2
  · simp only [rosserRelativeStoppingMass, rosserStoppingMass, if_pos hstop, zero_div]
    exact add_nonneg hf0 hε.le
  by_cases hwz : depthSplit k D ≤ z
  · have hw2 : 2 ≤ depthSplit k D := by linarith
    have hlw : 0 < Real.log (depthSplit k D) := Real.log_pos (by linarith)
    have hlevel := child_level_ge_of_parameter D T hD hT hDT z hz hs2
    have h := hstep n D (depthSplit k D) δ z hD hw2 hwz hs.le
      (depthSplit_prefix_level k hk D (by linarith) hw) P hP hodd upper hstop (by
        intro p hp hpP
        have hp3 : 3 ≤ p := hodd p hpP
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
        have hpz : (p : ℝ) ≤ z := by exact_mod_cast (mem_Ioc.mp hp).2
        have hEL : L ≤ D / p := (le_max_left L 2).trans (hlevel.trans
          (div_le_div_of_nonneg_left (by linarith : 0 ≤ D) (by linarith) hpz))
        have hparam := sieveParameter_antitone hD hp1 hz1 hpz
        have hEp : 1 < sieveParameter (D / p) p := by
          rw [sieveParameter_div_self D p (by linarith) hp1]
          linarith
        simpa only [sieveParameter_div_self D p (by linarith) hp1] using
          hL (D / p) hEL p hp3 hEp P hP hodd)
    have hratio := hbound (depthSplit k D) z hw2 hwz P hP hodd
    simp only [Nat.floor_natCast] at hratio
    have hlogs := depthSplit_log_ratio_le k hk D hD z hz hs2 hw2
    have htail : sieveProduct P primeDensity (⌊depthSplit k D⌋₊ + 1) /
        sieveProduct P primeDensity (z + 1) - 1 ≤ 2 * (k : ℝ) := by
      have hprod : (1 + C / Real.log (depthSplit k D)) *
          (Real.log z / Real.log (depthSplit k D)) ≤ 2 * (k : ℝ) :=
        mul_le_mul (by linarith) hlogs
          (div_nonneg (Real.log_pos hz1).le hlw.le) (by norm_num)
      linarith
    have hfM : rosserContinuousTerm (n + 1) (sieveParameter D z - 1) ≤ M :=
      antitoneOn_rosserContinuousTerm (n + 1) (by norm_num : (0 : ℝ) < 1)
        (show 0 < sieveParameter D z - 1 by linarith) (by linarith)
    have hdensity : 2 * K * rosserContinuousTerm (n + 1) (sieveParameter D z - 1) /
        Real.log (depthSplit k D) ≤ (2 * K * M) / Real.log (depthSplit k D) := by
      apply div_le_div_of_nonneg_right _ hlw.le
      nlinarith
    have herr := mul_le_mul_of_nonneg_left htail hδ.le
    have hδε : δ * (2 * (k : ℝ)) = ε / 2 := by
      dsimp [δ]
      field_simp
      ring
    rw [hδε] at herr
    linarith
  · have hzero := rosserStoppingMass_eq_zero_of_level P hP (n + 2) (z + 1) upper D
      (depthSplit_small_terminal k hk D (by linarith) hw z (lt_of_not_ge hwz))
    rw [rosserRelativeStoppingMass, hzero, zero_div]
    exact add_nonneg hf0 hε.le

end Chen.LinearSieve
