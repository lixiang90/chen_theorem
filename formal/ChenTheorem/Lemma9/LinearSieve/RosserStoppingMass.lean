import ChenTheorem.Lemma9.LinearSieve.RosserUpperInitial

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- The contribution to the actual Rosser defect from branches which
first stop after exactly `n` selections of decreasing primes. -/
noncomputable def rosserStoppingMass (P : Finset ℕ) : ℕ → ℕ → Bool → ℝ → ℝ
  | 0, z, upper, D =>
      if upper = false ∧ D ≤ (z : ℝ) ^ 2 then sieveProduct P primeDensity z else 0
  | n + 1, z, upper, D =>
      if upper = false ∧ D ≤ (z : ℝ) ^ 2 then 0 else
        ∑ p : Fin z, if (p : ℕ) ∈ P then
          primeDensity p * rosserStoppingMass P n p (!upper) (D / p) else 0

theorem rosserStoppingMass_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z : ℕ) (upper : Bool) (D : ℝ) : 0 ≤ rosserStoppingMass P n z upper D := by
  induction n generalizing z upper D with
  | zero =>
    rw [rosserStoppingMass]
    split_ifs
    · exact (primeDensity_sieveProduct_pos P hP hodd z).le
    · exact le_rfl
  | succ n ih =>
    rw [rosserStoppingMass]
    split_ifs
    · exact le_rfl
    · apply sum_nonneg
      intro p _
      split_ifs with hp
      · exact mul_nonneg (primeDensity_bounds (hP p hp) (hodd p hp)).1 (ih _ _ _)
      · exact le_rfl

theorem rosserStoppingMass_eq_zero_of_depth (P : Finset ℕ)
    (n z : ℕ) (upper : Bool) (D : ℝ) (hdepth : z < n) :
    rosserStoppingMass P n z upper D = 0 := by
  induction n generalizing z upper D with
  | zero => omega
  | succ n ih =>
    rw [rosserStoppingMass]
    split_ifs
    · rfl
    · apply sum_eq_zero
      intro p _
      have hp : (p : ℕ) < n := by omega
      simp only [ih p (!upper) (D / p) hp, mul_zero, ite_self]

theorem rosserStoppingMass_eq_zero_of_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n z : ℕ) (upper : Bool) (D : ℝ)
    (hD : (z : ℝ) ^ (n + 2) < D) : rosserStoppingMass P n z upper D = 0 := by
  induction n generalizing z upper D with
  | zero =>
    simp only [rosserStoppingMass]
    rw [if_neg (fun h => (not_le.mpr hD) h.2)]
  | succ n ih =>
    rw [rosserStoppingMass]
    split_ifs
    · rfl
    · apply sum_eq_zero
      intro p _
      split_ifs with hp
      · have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP p hp).pos
        have hpz : ((p : ℕ) : ℝ) ≤ z := by exact_mod_cast p.isLt.le
        have hpower : ((p : ℕ) : ℝ) ^ (n + 3) ≤ (z : ℝ) ^ (n + 3) := by gcongr
        have hchild : ((p : ℕ) : ℝ) ^ (n + 2) < D / (p : ℕ) := by
          apply (lt_div_iff₀ hp0).mpr
          rw [← pow_succ]
          exact hpower.trans_lt hD
        rw [ih p (!upper) (D / p) hchild, mul_zero]
      · rfl

theorem sum_range_rosserStoppingMass_recursion (P : Finset ℕ)
    (N z : ℕ) (upper : Bool) (D : ℝ) :
    (∑ n ∈ range (N + 1), rosserStoppingMass P n z upper D) =
      if upper = false ∧ D ≤ (z : ℝ) ^ 2 then sieveProduct P primeDensity z else
        ∑ p : Fin z, if (p : ℕ) ∈ P then primeDensity p *
          (∑ n ∈ range N, rosserStoppingMass P n p (!upper) (D / p)) else 0 := by
  rw [sum_range_succ']
  by_cases hs : upper = false ∧ D ≤ (z : ℝ) ^ 2
  · simp [rosserStoppingMass, hs]
  · simp only [rosserStoppingMass, if_neg hs, add_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    by_cases hp : (p : ℕ) ∈ P
    · simp only [hp, if_true, mul_sum]
    · simp only [hp, if_false, sum_const_zero]

/-- The depth decomposition is exact once the finite prime cutoff is
exhausted; it is not a hypothetical approximation to the defect. -/
theorem sum_range_rosserStoppingMass_eq_defect (P : Finset ℕ)
    (N z : ℕ) (upper : Bool) (D : ℝ) (hN : z < N) :
    (∑ n ∈ range N, rosserStoppingMass P n z upper D) = rosserDefect P primeDensity z upper D := by
  induction N generalizing z upper D with
  | zero => omega
  | succ N ih =>
    rw [sum_range_rosserStoppingMass_recursion, rosserDefect_recursion]
    split_ifs
    · rfl
    · apply sum_congr rfl
      intro p _
      have hp : (p : ℕ) < N := by omega
      rw [ih p (!upper) (D / p) hp]

theorem rosserDefect_eq_sum_stoppingMass (P : Finset ℕ) (z : ℕ) (upper : Bool) (D : ℝ) :
    rosserDefect P primeDensity z upper D =
      ∑ n ∈ range (z + 1), rosserStoppingMass P n z upper D :=
  (sum_range_rosserStoppingMass_eq_defect P (z + 1) z upper D (by omega)).symm

end Chen.LinearSieve
