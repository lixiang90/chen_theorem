import Submission.ChenTheorem.Lemma9.LinearSieve.RosserLargeParameter

set_option autoImplicit true
open Finset

namespace Chen.LinearSieve

theorem rosserStoppingMass_parity_zero (P : Finset ℕ) (n : ℕ) :
    (Even n → ∀ z D, rosserStoppingMass P n z true D = 0) ∧
    (¬Even n → ∀ z D, rosserStoppingMass P n z false D = 0) := by
  induction n with
  | zero =>
    constructor
    · intro _ z D
      simp [rosserStoppingMass]
    · intro h
      simp at h
  | succ n ih =>
    constructor
    · intro hn z D
      have hn' : ¬Even n := by simpa only [Nat.even_add_one] using hn
      simp only [rosserStoppingMass, Bool.true_eq_false, false_and, Bool.not_true,
        ih.2 hn', mul_zero, ite_self, sum_const_zero]
    · intro hn z D
      have hn' : Even n := by simpa only [Nat.even_add_one, not_not] using hn
      simp only [rosserStoppingMass, Bool.not_false, ih.1 hn', mul_zero, ite_self, sum_const_zero]

theorem rosserStoppingMass_upper_even (P : Finset ℕ) (N z : ℕ) (D : ℝ) :
    rosserStoppingMass P (2 * N) z true D = 0 :=
  (rosserStoppingMass_parity_zero P (2 * N)).1 (by simp) z D

theorem rosserStoppingMass_lower_odd (P : Finset ℕ) (N z : ℕ) (D : ℝ) :
    rosserStoppingMass P (2 * N + 1) z false D = 0 :=
  (rosserStoppingMass_parity_zero P (2 * N + 1)).2 (by simp) z D

/-- Depth contributions with the same normalization as the continuous
error terms; the prime cutoff is exclusive. -/
noncomputable def rosserRelativeStoppingMass (P : Finset ℕ) (n z : ℕ)
    (upper : Bool) (D : ℝ) : ℝ :=
  rosserStoppingMass P n z upper D / sieveProduct P primeDensity z

theorem rosserRelativeStoppingMass_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z : ℕ) (upper : Bool) (D : ℝ) : 0 ≤ rosserRelativeStoppingMass P n z upper D :=
  div_nonneg (rosserStoppingMass_nonneg P hP hodd n z upper D)
    (primeDensity_sieveProduct_pos P hP hodd z).le

theorem rosserRelativeDefect_eq_sum_stoppingMass (P : Finset ℕ) (z : ℕ) (upper : Bool) (D : ℝ) :
    rosserRelativeDefect P z upper D =
      ∑ n ∈ range (z + 1), rosserRelativeStoppingMass P n z upper D := by
  unfold rosserRelativeDefect rosserRelativeStoppingMass
  rw [rosserDefect_eq_sum_stoppingMass, sum_div]

end Chen.LinearSieve
