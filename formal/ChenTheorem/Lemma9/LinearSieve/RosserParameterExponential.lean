import ChenTheorem.Lemma9.LinearSieve.FactorialExponentialTail
import ChenTheorem.Lemma9.LinearSieve.RosserLargeParameter

namespace Chen.LinearSieve

/-- A depth tied directly to the sieve parameter, leaving enough room
for the strict level inequality which annihilates the initial segment. -/
noncomputable def largeParameterDepth (s : ℝ) : ℕ := ⌊s⌋₊ - 2

theorem largeParameterDepth_bounds (s : ℝ) (hs : 4 ≤ s) :
    2 ≤ largeParameterDepth s ∧ s - 3 ≤ (largeParameterDepth s : ℝ) ∧
      (largeParameterDepth s : ℝ) + 1 < s := by
  have hfloor : 4 ≤ ⌊s⌋₊ := Nat.le_floor hs
  have hfle := Nat.floor_le (by linarith : 0 ≤ s)
  have hflt := Nat.lt_floor_add_one s
  have he : (largeParameterDepth s : ℝ) = (⌊s⌋₊ : ℝ) - 2 := by
    rw [largeParameterDepth, Nat.cast_sub (by omega : 2 ≤ ⌊s⌋₊), Nat.cast_ofNat]
  refine ⟨by unfold largeParameterDepth; omega, ?_, ?_⟩
  · rw [he]
    linarith
  · rw [he]
    linarith

theorem largeParameterDepth_level_bound (D z : ℝ) (hD : 1 < D) (hz : 1 < z)
    (hs : 4 ≤ sieveParameter D z) :
    z ^ (largeParameterDepth (sieveParameter D z) + 1) < D := by
  have hn := (largeParameterDepth_bounds (sieveParameter D z) hs).2.2
  change (largeParameterDepth (sieveParameter D z) : ℝ) + 1 < Real.log D / Real.log z at hn
  have hm := (lt_div_iff₀ (Real.log_pos hz)).mp hn
  apply (Real.log_lt_log_iff (pow_pos (by linarith : 0 < z) _) (by linarith : 0 < D)).mp
  rw [Real.log_pow]
  simpa only [Nat.cast_add, Nat.cast_one] using hm

theorem depthMassMajorant_gt_one (K z : ℝ) (hK : 0 < K) (hz : 2 ≤ z) :
    1 < depthMassMajorant K z := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq := div_pos hK hL
  have hzlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hz
  have hr : 1 ≤ Real.log z / Real.log 2 := (le_div_iff₀ hL).2 (by simpa using hzlog)
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1 + K / Real.log 2 by linarith)
  unfold depthMassMajorant
  nlinarith

/-- The full actual Rosser defect has an explicit bound in its sieve
parameter, including the loss from rounding the stopping depth. -/
theorem rosserRelativeDefect_parameter_exponential :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ upper : Bool, ∀ D : ℝ,
      1 < D → 6 ≤ sieveParameter D (z + 1) →
      rosserRelativeDefect P (z + 1) upper D ≤
        Real.exp (2 * Real.log (depthMassMajorant K z) +
          3 * Real.log (sieveParameter D (z + 1)) + sieveParameter D (z + 1) *
            (2 + Real.log (1 + Real.log (depthMassMajorant K z)) -
              Real.log (sieveParameter D (z + 1)))) := by
  obtain ⟨K, hK, hb⟩ := rosserRelativeDefect_large_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd upper D hD hs
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hdepth := largeParameterDepth_bounds (sieveParameter D (z + 1)) (by linarith)
  have hlevel := largeParameterDepth_level_bound D (z + 1) hD (by linarith) (by linarith)
  have h := hb z hz P hP hodd (largeParameterDepth (sieveParameter D (z + 1))) upper D
    (by simpa only [Nat.cast_add, Nat.cast_one] using hlevel)
  change rosserRelativeDefect P (z + 1) upper D ≤ depthMassMajorant K z ^ 2 *
    (Real.log (depthMassMajorant K z) ^ largeParameterDepth (sieveParameter D (z + 1)) /
      (largeParameterDepth (sieveParameter D (z + 1))).factorial) at h
  exact h.trans (factorial_log_tail_le_parameter_exponential _ _
    (depthMassMajorant_gt_one K z hK hzR) hs _ hdepth.2.1 (by linarith [hdepth.2.2]))

end Chen.LinearSieve
