import ChenTheorem.Lemma9.LinearSieve.RosserDepthStep

open Filter

namespace Chen.LinearSieve

theorem rosserDepthBound_of_zero (n : ℕ) (upper : Bool)
    (hzero : ∀ P z D, rosserRelativeStoppingMass P n z upper D = 0) :
    RosserDepthBound n upper := by
  intro ε hε
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with D hD
  intro z hz hs P _ _
  rw [hzero]
  exact add_nonneg (rosserContinuousTerm_nonneg n _ (by linarith)) hε.le

/-- The active lower branch lies strictly above its continuous cutoff;
the complementary stopped branch contributes nothing at positive depth. -/
theorem rosserDepthBound_lower_of_large (n : ℕ)
    (hc : rosserContinuousCutoff (n + 2) = 2)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z →
      rosserContinuousCutoff (n + 2) < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P (n + 2) (z + 1) false D ≤
        rosserContinuousTerm (n + 2) (sieveParameter D z) + ε) :
    RosserDepthBound (n + 2) false := by
  intro ε hε
  filter_upwards [hlarge ε hε] with D hb
  intro z hz hs P hP hodd
  by_cases hstop : D ≤ ((z + 1 : ℕ) : ℝ) ^ 2
  · rw [rosserRelativeStoppingMass_lower_stopped P (n + 1) (z + 1) D hstop]
    exact add_nonneg (rosserContinuousTerm_nonneg (n + 2) _ (by linarith)) hε.le
  · apply hb z hz _ P hP hodd
    rw [hc]
    exact sieveParameter_gt_two_of_active D z hz (lt_of_not_ge hstop)

/-- Every fixed positive stopping depth has the continuous upper bound,
uniformly in the prime set and all parameters greater than one. The
threshold may depend on the depth and on the requested error. -/
theorem rosserDepthBound_all (n : ℕ) : ∀ upper : Bool, RosserDepthBound (n + 1) upper := by
  induction n with
  | zero =>
    intro upper
    cases upper with
    | false =>
      apply rosserDepthBound_of_zero
      intro P z D
      simp only [rosserRelativeStoppingMass, rosserStoppingMass_lower_odd P 0 z D, zero_div]
    | true =>
      exact eventually_rosserFirstMass_le_continuous
  | succ n ih =>
    intro upper
    by_cases hn : Even (n + 2)
    · have hc : rosserContinuousCutoff (n + 2) = 2 := by simp [rosserContinuousCutoff, hn]
      cases upper with
      | false =>
        apply rosserDepthBound_lower_of_large n hc
        exact rosser_depth_large_parameter_step n false (ih true)
      | true =>
        apply rosserDepthBound_of_zero
        intro P z D
        rw [rosserRelativeStoppingMass, (rosserStoppingMass_parity_zero P (n + 2)).1 hn,
          zero_div]
    · have hc : rosserContinuousCutoff (n + 2) = 3 := by simp [rosserContinuousCutoff, hn]
      cases upper with
      | false =>
        apply rosserDepthBound_of_zero
        intro P z D
        rw [rosserRelativeStoppingMass, (rosserStoppingMass_parity_zero P (n + 2)).2 hn,
          zero_div]
      | true =>
        apply rosser_depth_upper_comparison_of_large_parameter n hc
        simpa only [hc] using rosser_depth_large_parameter_step n true (ih false)

theorem eventually_rosserStoppingMass_le_continuous (n : ℕ) (upper : Bool)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P (n + 1) (z + 1) upper D ≤
        rosserContinuousTerm (n + 1) (sieveParameter D z) + ε :=
  rosserDepthBound_all n upper ε hε

/-- Any fixed finite initial set of positive depths can be compared
with one arbitrarily small total error. No uniformity in the depth count
as a function of the level is asserted here. -/
theorem eventually_sum_rosserStoppingMass_le_continuous (N : ℕ) (upper : Bool)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ n ∈ Finset.range N, rosserRelativeStoppingMass P (n + 1) (z + 1) upper D) ≤
        (∑ n ∈ Finset.range N, rosserContinuousTerm (n + 1) (sieveParameter D z)) + ε := by
  induction N generalizing ε with
  | zero => exact Filter.Eventually.of_forall (by intros; simpa using hε.le)
  | succ N ih =>
    filter_upwards [ih (ε / 2) (by positivity),
      eventually_rosserStoppingMass_le_continuous N upper (ε / 2) (by positivity)]
      with D hsum hterm
    intro z hz hs P hP hodd
    have h₁ := hsum z hz hs P hP hodd
    have h₂ := hterm z hz hs P hP hodd
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

end Chen.LinearSieve
