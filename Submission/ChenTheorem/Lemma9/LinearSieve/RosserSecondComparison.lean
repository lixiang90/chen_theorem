import Submission.ChenTheorem.Lemma9.LinearSieve.RosserDepthComparison

set_option autoImplicit true
open Finset Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The base comparison at the exact child cutoff `p`. Moving from `p-1`
to `p` only increases the continuous upper bound. -/
theorem eventually_rosserFirstMass_primeCutoff_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ p : ℕ, 3 ≤ p → 1 < sieveParameter D p →
      ∀ P : Finset ℕ, (∀ q ∈ P, q.Prime) → (∀ q ∈ P, 2 < q) →
      rosserRelativeStoppingMass P 1 p true D ≤
        rosserContinuousTerm 1 (sieveParameter D p) + ε := by
  filter_upwards [eventually_rosserFirstMass_le_continuous ε hε,
    eventually_gt_atTop (1 : ℝ)] with D hb hD
  intro p hp hs P hP hodd
  have hpm : 2 ≤ p - 1 := by omega
  have hm1 : (1 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 1 < p - 1 by omega)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hmp : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hparam := sieveParameter_antitone hD hm1 hp1 hmp
  have hmparam : 1 < sieveParameter D (p - 1 : ℕ) := hs.trans_le hparam
  have h := hb (p - 1) hpm hmparam P hP hodd
  rw [Nat.sub_add_cancel (by omega)] at h
  exact h.trans (_root_.add_le_add
    (antitoneOn_rosserContinuousTerm 1 (by change 0 < sieveParameter D p; linarith)
      (by change 0 < sieveParameter D (p - 1 : ℕ); linarith) hparam) le_rfl)

/-- An unconditional second-depth estimate with explicit density and
base-comparison errors. The level condition `D/z ≥ T` discharges every
first-depth child hypothesis uniformly in the prime set and cutoff. -/
theorem rosserSecondMass_le_continuous_with_errors :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧
      ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z →
        2 < sieveParameter D z → (⌊w⌋₊ : ℝ) ^ 4 < D → T ≤ D / z →
        ((z + 1 : ℕ) : ℝ) ^ 2 < D →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        rosserRelativeStoppingMass P 2 (z + 1) false D ≤
          rosserContinuousTerm 2 (sieveParameter D z) +
            2 * K * rosserContinuousTerm 1 (sieveParameter D z - 1) / Real.log w +
            ε * (sieveProduct P primeDensity (⌊w⌋₊ + 1) /
              sieveProduct P primeDensity (z + 1) - 1) := by
  obtain ⟨K, hK, hstep⟩ := rosserStoppingMass_continuous_step
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨L, hL⟩ := eventually_atTop.mp (eventually_rosserFirstMass_primeCutoff_le ε hε)
  refine ⟨max L 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro D w z hD hw hwz hs hpower hlevel hactive P hP hodd
  apply hstep 0 D w ε z hD hw hwz
    (by simpa [rosserContinuousCutoff] using hs.le) hpower P hP hodd false
    (by simpa using not_le.mpr hactive)
  intro p hp hpP
  have hp3 : 3 ≤ p := hodd p hpP
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hpz : (p : ℝ) ≤ z := by exact_mod_cast (mem_Ioc.mp hp).2
  have hz1 : (1 : ℝ) < z := hp1.trans_le hpz
  have hchildlevel : L ≤ D / p := (le_max_left L 2).trans (hlevel.trans
    (div_le_div_of_nonneg_left (by linarith : 0 ≤ D) hp0 hpz))
  have hparam := sieveParameter_antitone hD hp1 hz1 hpz
  have hchildparam : 1 < sieveParameter (D / p) p := by
    rw [sieveParameter_div_self D p (by linarith) hp1]
    linarith
  have h := hL (D / p) hchildlevel p hp3 hchildparam P hP hodd
  simpa only [Bool.not_false, sieveParameter_div_self D p (by linarith) hp1] using h

end Chen.LinearSieve
