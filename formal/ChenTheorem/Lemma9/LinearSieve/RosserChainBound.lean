import ChenTheorem.Lemma9.LinearSieve.RosserStoppingMass
import Mathlib.Algebra.Order.Ring.Pow

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- Unrestricted mass of strictly decreasing chains of a given length. -/
noncomputable def decreasingChainMass (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, z => ∑ p : Fin z, g p * decreasingChainMass g n p

theorem decreasingChainMass_nonneg (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (n z : ℕ) :
    0 ≤ decreasingChainMass g n z := by
  induction n generalizing z with
  | zero => exact zero_le_one
  | succ n ih => exact sum_nonneg (fun p _ => mul_nonneg (hg p) (ih p))

theorem decreasingChainMass_succ_cutoff (g : ℕ → ℝ) (n z : ℕ) :
    decreasingChainMass g (n + 1) (z + 1) =
      decreasingChainMass g (n + 1) z + g z * decreasingChainMass g n z := by
  rw [decreasingChainMass, Fin.sum_univ_castSucc]
  rfl

/-- Ordering the selected primes supplies a factorial saving. This
bound is proved by induction and Bernoulli's inequality. -/
theorem factorial_mul_decreasingChainMass_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (n z : ℕ) :
    (n.factorial : ℝ) * decreasingChainMass g n z ≤ (∑ p ∈ range z, g p) ^ n := by
  induction z generalizing n with
  | zero =>
    cases n <;> simp [decreasingChainMass]
  | succ z ih =>
    cases n with
    | zero => simp [decreasingChainMass]
    | succ n =>
      have hx : 0 ≤ ∑ p ∈ range z, g p := sum_nonneg (fun p _ => hg p)
      have h1 := ih (n + 1)
      have h2 := mul_le_mul_of_nonneg_left (ih n)
        (mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (hg z))
      have hb := pow_add_mul_le_add_pow hx (show 0 ≤ 2 * (∑ p ∈ range z, g p) + g z by linarith [hg z]) (n + 1)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hb
      rw [decreasingChainMass_succ_cutoff, sum_range_succ]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1 ⊢
      nlinarith

theorem decreasingChainMass_le_factorial (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (n z : ℕ) :
    decreasingChainMass g n z ≤ (∑ p ∈ range z, g p) ^ n / n.factorial := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (le_div_iff₀ hn).mpr
  simpa only [mul_comm] using factorial_mul_decreasingChainMass_le g hg n z

theorem primeDensity_sieveProduct_le_one (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z : ℕ) :
    sieveProduct P primeDensity z ≤ 1 := by
  apply prod_le_one
  · intro p _
    split_ifs with hp
    · exact sub_nonneg.mpr (primeDensity_bounds (hP p hp) (hodd p hp)).2.le
    · norm_num
  · intro p _
    split_ifs with hp
    · linarith [(primeDensity_bounds (hP p hp) (hodd p hp)).1]
    · norm_num

theorem rosserStoppingMass_le_chainMass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z : ℕ) (upper : Bool) (D : ℝ) :
    rosserStoppingMass P n z upper D ≤
      decreasingChainMass (fun p => if p ∈ P then primeDensity p else 0) n z := by
  have hg : ∀ p, 0 ≤ if p ∈ P then primeDensity p else 0 := by
    intro p
    split_ifs with hp
    · exact (primeDensity_bounds (hP p hp) (hodd p hp)).1
    · exact le_rfl
  induction n generalizing z upper D with
  | zero =>
    rw [rosserStoppingMass, decreasingChainMass]
    split_ifs
    · exact primeDensity_sieveProduct_le_one P hP hodd z
    · exact zero_le_one
  | succ n ih =>
    rw [rosserStoppingMass]
    split_ifs
    · exact decreasingChainMass_nonneg _ hg _ _
    · rw [decreasingChainMass]
      apply sum_le_sum
      intro p _
      split_ifs with hp
      · exact mul_le_mul_of_nonneg_left (ih p (!upper) (D / p))
          (primeDensity_bounds (hP p hp) (hodd p hp)).1
      · simp only [zero_mul, le_refl]

theorem rosserStoppingMass_le_factorial (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z : ℕ) (upper : Bool) (D : ℝ) :
    rosserStoppingMass P n z upper D ≤
      (∑ p ∈ range z, if p ∈ P then primeDensity p else 0) ^ n / n.factorial := by
  apply (rosserStoppingMass_le_chainMass P hP hodd n z upper D).trans
  apply decreasingChainMass_le_factorial
  intro p
  split_ifs with hp
  · exact (primeDensity_bounds (hP p hp) (hodd p hp)).1
  · exact le_rfl

end Chen.LinearSieve
