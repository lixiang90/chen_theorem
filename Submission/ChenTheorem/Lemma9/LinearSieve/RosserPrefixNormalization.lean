import Submission.ChenTheorem.Lemma9.LinearSieve.RosserPartialDefect

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem rosserPartialDefect_le_defect (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z : ℕ) (upper : Bool) (D : ℝ) :
    rosserPartialDefect P N z upper D ≤ rosserRelativeDefect P z upper D := by
  have h := (rosserDefect_partial_bounds P hP hodd N z upper D).1
  rw [rosserPartialDefect_eq_div, rosserRelativeDefect]
  apply div_le_div_of_nonneg_right _ (primeDensity_sieveProduct_pos P hP hodd z).le
  linarith

/-- The prefix is precisely a cumulative defect at the smaller cutoff,
with only the normalization product changed. -/
theorem rosserPartialPrefix_eq_product_ratio (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z m : ℕ) (upper : Bool) (D : ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((m + 1 : ℕ) : ℝ) ^ 2)) :
    rosserPartialPrefix P N z upper D m =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserPartialDefect P (N + 1) (m + 1) upper D := by
  rw [rosserPartialDefect_split P hP hodd N m m le_rfl upper D hactive]
  simp only [Ioc_self, sum_empty, add_zero]
  unfold rosserPartialPrefix
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  have hm := (primeDensity_sieveProduct_pos P hP hodd (m + 1)).ne'
  have hz := (primeDensity_sieveProduct_pos P hP hodd (z + 1)).ne'
  unfold buchstabCoefficient
  split_ifs
  · field_simp
  · simp

theorem rosserPartialPrefix_le_product_ratio_defect (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z m : ℕ) (upper : Bool) (D : ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((m + 1 : ℕ) : ℝ) ^ 2)) :
    rosserPartialPrefix P N z upper D m ≤
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserRelativeDefect P (m + 1) upper D := by
  rw [rosserPartialPrefix_eq_product_ratio P hP hodd N z m upper D hactive]
  exact mul_le_mul_of_nonneg_left (rosserPartialDefect_le_defect P hP hodd (N + 1) (m + 1) upper D)
    (div_nonneg (primeDensity_sieveProduct_pos P hP hodd (m + 1)).le
      (primeDensity_sieveProduct_pos P hP hodd (z + 1)).le)

end Chen.LinearSieve
