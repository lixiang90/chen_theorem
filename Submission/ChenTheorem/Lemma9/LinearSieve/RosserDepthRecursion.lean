import Submission.ChenTheorem.Lemma9.LinearSieve.RosserFirstComparison

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem rosserRelativeStoppingMass_succ_recursion (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z : ℕ) (upper : Bool) (D : ℝ) :
    rosserRelativeStoppingMass P (n + 1) z upper D =
      if upper = false ∧ D ≤ (z : ℝ) ^ 2 then 0 else
        ∑ p : Fin z, if (p : ℕ) ∈ P then
          primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity z) *
            rosserRelativeStoppingMass P n p (!upper) (D / p) else 0 := by
  unfold rosserRelativeStoppingMass
  rw [rosserStoppingMass]
  split_ifs with hstop
  · exact zero_div _
  · rw [sum_div]
    apply sum_congr rfl
    intro p _
    have hp0 := (primeDensity_sieveProduct_pos P hP hodd p).ne'
    have hz0 := (primeDensity_sieveProduct_pos P hP hodd z).ne'
    split_ifs
    · field_simp
    · simp

/-- Small-prime contribution to a single depth step; `n` denotes the
remaining depth after selecting the first prime. -/
noncomputable def rosserStoppingPrefix (P : Finset ℕ) (n z : ℕ) (upper : Bool)
    (D : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ range (m + 1), buchstabCoefficient P z p *
    rosserRelativeStoppingMass P n p (!upper) (D / p)

theorem rosserStoppingPrefix_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z : ℕ) (upper : Bool) (D : ℝ) (m : ℕ) : 0 ≤ rosserStoppingPrefix P n z upper D m := by
  apply sum_nonneg
  intro p _
  exact mul_nonneg (normalized_buchstab_mass_nonneg P hP hodd (z + 1) p)
    (rosserRelativeStoppingMass_nonneg P hP hodd n p (!upper) (D / p))

theorem rosserRelativeStoppingMass_split (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z m : ℕ) (hmz : m ≤ z) (upper : Bool) (D : ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) :
    rosserRelativeStoppingMass P (n + 1) (z + 1) upper D = rosserStoppingPrefix P n z upper D m +
      ∑ p ∈ Ioc m z, buchstabCoefficient P z p *
        rosserRelativeStoppingMass P n p (!upper) (D / p) := by
  rw [rosserRelativeStoppingMass_succ_recursion P hP hodd, if_neg hactive]
  have hsum : (∑ p : Fin (z + 1), if (p : ℕ) ∈ P then
      primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity (z + 1)) *
        rosserRelativeStoppingMass P n p (!upper) (D / p) else 0) =
      ∑ p ∈ range (z + 1), buchstabCoefficient P z p *
        rosserRelativeStoppingMass P n p (!upper) (D / p) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro p _
    unfold buchstabCoefficient
    split_ifs <;> simp
  rw [hsum]
  have hset : Ioc m z = Ico (m + 1) (z + 1) := by
    ext p
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hset, rosserStoppingPrefix]
  exact (sum_range_add_sum_Ico _ (show m + 1 ≤ z + 1 by omega)).symm

/-- For a fixed depth, a power level suffices to remove the small-prime
prefix exactly. The required power is explicit in the depth. -/
theorem rosserStoppingPrefix_eq_zero_of_power_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n z : ℕ) (upper : Bool) (D : ℝ) (m : ℕ)
    (hD : (m : ℝ) ^ (n + 3) < D) : rosserStoppingPrefix P n z upper D m = 0 := by
  apply sum_eq_zero
  intro p hp
  by_cases hpP : p ∈ P
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).pos
    have hpm : (p : ℝ) ≤ m := by exact_mod_cast (show p ≤ m by have := mem_range.mp hp; omega)
    have hpow : (p : ℝ) ^ (n + 3) ≤ (m : ℝ) ^ (n + 3) := by gcongr
    have hchild : (p : ℝ) ^ (n + 2) < D / p := by
      apply (lt_div_iff₀ hp0).mpr
      rw [← pow_succ]
      exact hpow.trans_lt hD
    simp only [rosserRelativeStoppingMass,
      rosserStoppingMass_eq_zero_of_level P hP n p (!upper) (D / p) hchild, zero_div, mul_zero]
  · simp [buchstabCoefficient, hpP]

end Chen.LinearSieve
