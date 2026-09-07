import Submission.ChenTheorem.Lemma9.LinearSieve.RosserDepthRecursion
import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabPartials

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- Cumulative relative stopping mass below a depth cutoff. The depth-zero
mass is retained, so a stopped lower branch has value one. -/
noncomputable def rosserPartialDefect (P : Finset ℕ) (N z : ℕ) (upper : Bool) (D : ℝ) : ℝ :=
  ∑ n ∈ range N, rosserRelativeStoppingMass P n z upper D

theorem rosserPartialDefect_eq_div (P : Finset ℕ) (N z : ℕ) (upper : Bool) (D : ℝ) :
    rosserPartialDefect P N z upper D =
      (∑ n ∈ range N, rosserStoppingMass P n z upper D) / sieveProduct P primeDensity z := by
  simp only [rosserPartialDefect, rosserRelativeStoppingMass, sum_div]

theorem rosserPartialDefect_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z : ℕ) (upper : Bool) (D : ℝ) : 0 ≤ rosserPartialDefect P N z upper D :=
  sum_nonneg (fun n _ => rosserRelativeStoppingMass_nonneg P hP hodd n z upper D)

theorem rosserPartialDefect_eq_defect (P : Finset ℕ) (N z : ℕ) (upper : Bool) (D : ℝ)
    (hN : z < N) : rosserPartialDefect P N z upper D = rosserRelativeDefect P z upper D := by
  rw [rosserPartialDefect_eq_div, sum_range_rosserStoppingMass_eq_defect P N z upper D hN]
  rfl

theorem rosserPartialDefect_recursion (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z : ℕ) (upper : Bool) (D : ℝ) :
    rosserPartialDefect P (N + 1) z upper D =
      if upper = false ∧ D ≤ (z : ℝ) ^ 2 then 1 else
        ∑ p : Fin z, if (p : ℕ) ∈ P then
          primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity z) *
            rosserPartialDefect P N p (!upper) (D / p) else 0 := by
  rw [rosserPartialDefect_eq_div, sum_range_rosserStoppingMass_recursion]
  have hz0 := (primeDensity_sieveProduct_pos P hP hodd z).ne'
  split_ifs with hstop
  · exact div_self hz0
  · rw [sum_div]
    apply sum_congr rfl
    intro p _
    have hp0 := (primeDensity_sieveProduct_pos P hP hodd p).ne'
    split_ifs
    · rw [rosserPartialDefect_eq_div]
      field_simp
    · simp

noncomputable def rosserPartialPrefix (P : Finset ℕ) (N z : ℕ) (upper : Bool)
    (D : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ range (m + 1), buchstabCoefficient P z p * rosserPartialDefect P N p (!upper) (D / p)

theorem rosserPartialPrefix_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z : ℕ) (upper : Bool) (D : ℝ) (m : ℕ) :
    0 ≤ rosserPartialPrefix P N z upper D m :=
  sum_nonneg (fun p _ => mul_nonneg (normalized_buchstab_mass_nonneg P hP hodd (z + 1) p)
    (rosserPartialDefect_nonneg P hP hodd N p (!upper) (D / p)))

theorem rosserPartialDefect_split (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z m : ℕ) (hmz : m ≤ z) (upper : Bool) (D : ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) :
    rosserPartialDefect P (N + 1) (z + 1) upper D = rosserPartialPrefix P N z upper D m +
      ∑ p ∈ Ioc m z, buchstabCoefficient P z p * rosserPartialDefect P N p (!upper) (D / p) := by
  rw [rosserPartialDefect_recursion P hP hodd, if_neg hactive]
  have heq : (∑ p : Fin (z + 1), if (p : ℕ) ∈ P then
      primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity (z + 1)) *
        rosserPartialDefect P N p (!upper) (D / p) else 0) =
      ∑ p ∈ range (z + 1), buchstabCoefficient P z p * rosserPartialDefect P N p (!upper) (D / p) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro p _
    unfold buchstabCoefficient
    split_ifs <;> simp
  rw [heq, rosserPartialPrefix]
  have hset : Ioc m z = Ico (m + 1) (z + 1) := by
    ext p
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hset]
  exact (sum_range_add_sum_Ico _ (show m + 1 ≤ z + 1 by omega)).symm

theorem rosserPartialDefect_step_of_child_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z m : ℕ) (hmz : m ≤ z) (upper : Bool) (D : ℝ) (H E : ℕ → ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2))
    (hchild : ∀ p ∈ Ioc m z, p ∈ P → rosserPartialDefect P N p (!upper) (D / p) ≤ H p + E p) :
    rosserPartialDefect P (N + 1) (z + 1) upper D ≤ rosserPartialPrefix P N z upper D m +
      (∑ p ∈ Ioc m z, H p * buchstabCoefficient P z p) +
      ∑ p ∈ Ioc m z, E p * buchstabCoefficient P z p := by
  rw [rosserPartialDefect_split P hP hodd N z m hmz upper D hactive, add_assoc]
  apply _root_.add_le_add le_rfl
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  by_cases hpP : p ∈ P
  · have h := mul_le_mul_of_nonneg_right (hchild p hp hpP)
      (normalized_buchstab_mass_nonneg P hP hodd (z + 1) p)
    change rosserPartialDefect P N p (!upper) (D / p) * buchstabCoefficient P z p ≤
      (H p + E p) * buchstabCoefficient P z p at h
    nlinarith
  · simp [buchstabCoefficient, hpP]

end Chen.LinearSieve
