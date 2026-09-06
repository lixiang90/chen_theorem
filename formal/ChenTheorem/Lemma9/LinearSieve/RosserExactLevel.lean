import ChenTheorem.Lemma9.LinearSieve.RosserIntegralStep

open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

/-- A finite, deliberately coarse level beyond which no lower branch
of the finite recursion can stop. It depends only on the prime cutoff. -/
noncomputable def rosserExactLevel (z : ℕ) : ℝ :=
  (z : ℝ) ^ 2 + ∑ p : Fin z, (p : ℝ) * rosserExactLevel p
termination_by z

theorem rosserExactLevel_nonneg (z : ℕ) : 0 ≤ rosserExactLevel z := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
    rw [rosserExactLevel]
    apply add_nonneg (sq_nonneg _)
    apply sum_nonneg
    intro p _
    exact mul_nonneg (Nat.cast_nonneg _) (ih p p.isLt)

theorem sq_le_rosserExactLevel (z : ℕ) : (z : ℝ) ^ 2 ≤ rosserExactLevel z := by
  rw [rosserExactLevel]
  apply le_add_of_nonneg_right
  apply sum_nonneg
  intro p _
  exact mul_nonneg (Nat.cast_nonneg _) (rosserExactLevel_nonneg p)

theorem mul_rosserExactLevel_le (z p : ℕ) (hp : p < z) :
    (p : ℝ) * rosserExactLevel p ≤ rosserExactLevel z := by
  have hterm : (p : ℝ) * rosserExactLevel p ≤
      ∑ q : Fin z, (q : ℝ) * rosserExactLevel q := by
    exact single_le_sum (f := fun q : Fin z => (q : ℝ) * rosserExactLevel q)
      (fun q _ => mul_nonneg (Nat.cast_nonneg _) (rosserExactLevel_nonneg q))
      (show (⟨p, hp⟩ : Fin z) ∈ univ from mem_univ _)
  conv_rhs => rw [rosserExactLevel]
  linarith [sq_nonneg (z : ℝ)]

/-- At a fixed prime cutoff the normalized Rosser defect is eventually
exactly zero, uniformly in the set of odd primes and in the choice of bound. -/
theorem rosserRelativeDefect_eq_zero_of_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (upper : Bool) (D : ℝ) (hD : rosserExactLevel z < D) :
    rosserRelativeDefect P z upper D = 0 := by
  induction z using Nat.strong_induction_on generalizing upper D with
  | h z ih =>
    have hactive : ¬(upper = false ∧ D ≤ (z : ℝ) ^ 2) := by
      intro hs
      exact (lt_of_le_of_lt (sq_le_rosserExactLevel z) hD).not_ge hs.2
    rw [rosserRelativeDefect_recursion P hP hodd, if_neg hactive]
    apply sum_eq_zero
    intro p _
    by_cases hpP : (p : ℕ) ∈ P
    · have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP p hpP).pos
      have hchild : rosserExactLevel p < D / (p : ℕ) := by
        apply (lt_div_iff₀ hp0).mpr
        rw [mul_comm]
        exact lt_of_le_of_lt (mul_rosserExactLevel_le z p p.isLt) hD
      simp only [hpP, ↓reduceIte, ih p p.isLt (!upper) (D / p) hchild, mul_zero]
    · simp [hpP]

theorem rosserEval_eq_product_of_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (D : ℝ) (hD : rosserExactLevel z < D) :
    rosserEval P primeDensity z false D = sieveProduct P primeDensity z ∧
      rosserEval P primeDensity z true D = sieveProduct P primeDensity z := by
  simpa only [rosserRelativeDefect_eq_zero_of_level P hP hodd z false D hD,
    rosserRelativeDefect_eq_zero_of_level P hP hodd z true D hD, sub_zero, add_zero, mul_one] using
      rosserEval_eq_product_mul_relativeDefect P hP hodd z D

/-- The retained small-prime term in the integral comparison disappears
once the level exceeds a constant depending only on its fixed cutoff. -/
theorem rosserDefectPrefix_eq_zero_of_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (upper : Bool) (D : ℝ) (m : ℕ) (hD : rosserExactLevel (m + 1) < D) :
    rosserDefectPrefix P z upper D m = 0 := by
  apply sum_eq_zero
  intro p hp
  by_cases hpP : p ∈ P
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).pos
    have hchild : rosserExactLevel p < D / p := by
      apply (lt_div_iff₀ hp0).mpr
      rw [mul_comm]
      exact lt_of_le_of_lt (mul_rosserExactLevel_le (m + 1) p (mem_range.mp hp)) hD
    rw [rosserRelativeDefect_eq_zero_of_level P hP hodd p (!upper) (D / p) hchild, mul_zero]
  · simp [buchstabCoefficient, hpP]

theorem eventually_rosserDefectPrefix_eq_zero (m : ℕ) :
    ∀ᶠ D : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ z : ℕ, ∀ upper : Bool, rosserDefectPrefix P z upper D m = 0 := by
  filter_upwards [eventually_gt_atTop (rosserExactLevel (m + 1))] with D hD
  intro P hP hodd z upper
  exact rosserDefectPrefix_eq_zero_of_level P hP hodd z upper D m hD

end Chen.LinearSieve
