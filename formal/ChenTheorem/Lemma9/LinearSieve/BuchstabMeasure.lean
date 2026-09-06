import ChenTheorem.Lemma9.LinearSieve.DensityQuantitative
import ChenTheorem.Lemma9.LinearSieve.RosserDefect

open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

theorem sieveProduct_succ (P : Finset ℕ) (g : ℕ → ℝ) (z : ℕ) :
    sieveProduct P g (z + 1) = sieveProduct P g z * (1 - if z ∈ P then g z else 0) := by
  simp only [sieveProduct, prod_range_succ]

/-- The exact mass at a prime step of the local density product. -/
theorem sieveProduct_sub_succ (P : Finset ℕ) (g : ℕ → ℝ) (p : ℕ) :
    sieveProduct P g p - sieveProduct P g (p + 1) =
      if p ∈ P then g p * sieveProduct P g p else 0 := by
  rw [sieveProduct_succ]
  split_ifs <;> ring

/-- Finite Buchstab mass on an arbitrary interval, in a form suitable
for subsequent partial summation against a monotone majorant. -/
theorem sum_buchstab_mass_Ico (P : Finset ℕ) (g : ℕ → ℝ)
    (w z : ℕ) (hwz : w ≤ z) :
    (∑ p ∈ Ico w z, if p ∈ P then g p * sieveProduct P g p else 0) =
      sieveProduct P g w - sieveProduct P g z := by
  induction z, hwz using Nat.le_induction with
  | base => simp
  | succ z hwz ih =>
    rw [sum_Ico_succ_top hwz, ih, ← sieveProduct_sub_succ]
    ring

/-- Normalize the interval mass by its terminal product. The minus one
is exact and is retained for the sharp linear-sieve analysis. -/
theorem sum_normalized_buchstab_mass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (w z : ℕ) (hwz : w ≤ z) :
    (∑ p ∈ Ioc w z, if p ∈ P then
      primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity (z + 1)) else 0) =
      sieveProduct P primeDensity (w + 1) / sieveProduct P primeDensity (z + 1) - 1 := by
  have hset : Ioc w z = Ico (w + 1) (z + 1) := by
    apply Finset.ext
    intro p
    simp only [mem_Ioc, mem_Ico]
    omega
  have hz0 := ne_of_gt (primeDensity_sieveProduct_pos P hP hodd (z + 1))
  calc
    _ = (∑ p ∈ Ioc w z, if p ∈ P then primeDensity p * sieveProduct P primeDensity p else 0) /
        sieveProduct P primeDensity (z + 1) := by
      rw [sum_div]
      apply sum_congr rfl
      intro p _
      split_ifs <;> ring
    _ = (sieveProduct P primeDensity (w + 1) - sieveProduct P primeDensity (z + 1)) /
        sieveProduct P primeDensity (z + 1) := by
      rw [hset, sum_buchstab_mass_Ico P primeDensity _ _ (by omega)]
    _ = _ := by rw [sub_div, div_self hz0]

theorem normalized_buchstab_mass_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z p : ℕ) :
    0 ≤ if p ∈ P then
      primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity z) else 0 := by
  split_ifs with hp
  · exact mul_nonneg (primeDensity_bounds (hP p hp) (hodd p hp)).1
      (div_pos (primeDensity_sieveProduct_pos P hP hodd p)
        (primeDensity_sieveProduct_pos P hP hodd z)).le
  · exact le_rfl

/-- Uniform cumulative bound for the nonnegative measure in the
normalized Rosser recursion. All density input here has been proved. -/
theorem normalized_buchstab_mass_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ w z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Ioc w z, if p ∈ P then
          primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity (z + 1)) else 0) ≤
            (1 + K / Real.log w) * (Real.log z / Real.log w) - 1 := by
  obtain ⟨K, hK, hbound⟩ := primeDensity_sieveProduct_dimension_one
  refine ⟨K, hK, fun w z hw hwz P hP hodd => ?_⟩
  rw [sum_normalized_buchstab_mass P hP hodd w z hwz]
  exact sub_le_sub_right (hbound w z hw hwz P hP hodd) 1

end Chen.LinearSieve
