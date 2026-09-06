import ChenTheorem.Lemma9.LinearSieve.DensityRatio

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- The nonnegative error relative to the local density product: upper
minus product on an upper branch, product minus lower on a lower branch. -/
noncomputable def rosserDefect (P : Finset ℕ) (g : ℕ → ℝ)
    (z : ℕ) (upper : Bool) (D : ℝ) : ℝ :=
  if upper then rosserEval P g z upper D - sieveProduct P g z
  else sieveProduct P g z - rosserEval P g z upper D

theorem rosserDefect_nonneg (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) (z : ℕ) (upper : Bool) (D : ℝ) :
    0 ≤ rosserDefect P g z upper D := by
  have hb := rosserEval_bounds P g hg z D
  cases upper
  · exact sub_nonneg.mpr hb.1
  · exact sub_nonneg.mpr hb.2

/-- Buchstab recursion for the error has only nonnegative summands.
A stopped lower branch contributes its entire local density product. -/
theorem rosserDefect_recursion (P : Finset ℕ) (g : ℕ → ℝ)
    (z : ℕ) (upper : Bool) (D : ℝ) :
    rosserDefect P g z upper D =
      if upper = false ∧ D ≤ (z : ℝ) ^ 2 then sieveProduct P g z else
        ∑ p : Fin z, if (p : ℕ) ∈ P then
          g p * rosserDefect P g p (!upper) (D / p) else 0 := by
  cases upper
  · have hs : (∑ p : Fin z, if (p : ℕ) ∈ P then
        g p * rosserDefect P g p true (D / p) else 0) =
        (∑ p : Fin z, if (p : ℕ) ∈ P then g p * rosserEval P g p true (D / p) else 0) -
        (∑ p : Fin z, if (p : ℕ) ∈ P then g p * sieveProduct P g p else 0) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro p _
      simp only [rosserDefect, ↓reduceIte]
      split_ifs <;> ring
    simp only [Bool.not_false, true_and]
    change sieveProduct P g z - rosserEval P g z false D =
      if D ≤ (z : ℝ) ^ 2 then sieveProduct P g z else _
    rw [rosserEval_lower]
    by_cases hstop : D ≤ (z : ℝ) ^ 2
    · simp [hstop]
    · rw [if_neg hstop, if_neg hstop, hs, sieveProduct_buchstab]
      ring
  · have hs : (∑ p : Fin z, if (p : ℕ) ∈ P then
        g p * rosserDefect P g p false (D / p) else 0) =
        (∑ p : Fin z, if (p : ℕ) ∈ P then g p * sieveProduct P g p else 0) -
        (∑ p : Fin z, if (p : ℕ) ∈ P then g p * rosserEval P g p false (D / p) else 0) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro p _
      simp only [rosserDefect, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> ring
    change rosserEval P g z true D - sieveProduct P g z = _
    simp only [Bool.true_eq_false, false_and, ↓reduceIte, Bool.not_true]
    rw [hs, rosserEval_upper, sieveProduct_buchstab]
    ring

noncomputable def rosserRelativeDefect (P : Finset ℕ) (z : ℕ) (upper : Bool) (D : ℝ) : ℝ :=
  rosserDefect P primeDensity z upper D / sieveProduct P primeDensity z

theorem rosserRelativeDefect_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (upper : Bool) (D : ℝ) : 0 ≤ rosserRelativeDefect P z upper D := by
  apply div_nonneg
  · exact rosserDefect_nonneg P primeDensity
      (fun p hp => ⟨(primeDensity_bounds (hP p hp) (hodd p hp)).1,
        (primeDensity_bounds (hP p hp) (hodd p hp)).2.le⟩) z upper D
  · exact (primeDensity_sieveProduct_pos P hP hodd z).le

/-- Normalized error recursion. Its coefficients are precisely the
density ratios controlled by the proved dimension-one interval bound. -/
theorem rosserRelativeDefect_recursion (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (upper : Bool) (D : ℝ) :
    rosserRelativeDefect P z upper D =
      if upper = false ∧ D ≤ (z : ℝ) ^ 2 then 1 else
        ∑ p : Fin z, if (p : ℕ) ∈ P then
          primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity z) *
            rosserRelativeDefect P p (!upper) (D / p) else 0 := by
  unfold rosserRelativeDefect
  rw [rosserDefect_recursion]
  have hz0 := ne_of_gt (primeDensity_sieveProduct_pos P hP hodd z)
  split_ifs with hstop
  · exact div_self hz0
  · rw [sum_div]
    apply sum_congr rfl
    intro p _
    have hp0 := ne_of_gt (primeDensity_sieveProduct_pos P hP hodd p)
    split_ifs
    · field_simp
    · simp

/-- Recover both main polynomials from their normalized defects. -/
theorem rosserEval_eq_product_mul_relativeDefect (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z : ℕ) (D : ℝ) :
    rosserEval P primeDensity z false D =
        sieveProduct P primeDensity z * (1 - rosserRelativeDefect P z false D) ∧
      rosserEval P primeDensity z true D =
        sieveProduct P primeDensity z * (1 + rosserRelativeDefect P z true D) := by
  have hz0 := ne_of_gt (primeDensity_sieveProduct_pos P hP hodd z)
  unfold rosserRelativeDefect rosserDefect
  simp only [Bool.false_eq_true, ↓reduceIte]
  constructor <;> field_simp <;> ring

end Chen.LinearSieve
