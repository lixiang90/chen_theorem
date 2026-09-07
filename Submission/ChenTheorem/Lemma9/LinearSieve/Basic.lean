import Mathlib.NumberTheory.SelbergSieve

set_option autoImplicit true

open Finset Nat
open scoped Classical

namespace Chen.LinearSieve

/-!
The finite lower-bound counterpart to Mathlib's upper Moebius sieve.
These are exact finite inequalities: the construction and asymptotic
evaluation of Richert's coefficients are still separate obligations.
-/

/-- Lower coefficients minorize the coprimality indicator on divisors of
the sifting product. A global condition on all natural numbers would
incorrectly exclude finite-support lower sieves with coefficient 1 at 1. -/
def IsLowerMoebius (P : ℕ) (mu : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∣ P → (∑ d ∈ n.divisors, mu d) ≤ if n = 1 then 1 else 0

variable {s : BoundingSieve}

/-- The exact interchange of the sequence sum and the divisor sum. -/
theorem sum_divisors_multSum (mu : ℕ → ℝ) :
    (∑ d ∈ s.prodPrimes.divisors, mu d * s.multSum d) =
      ∑ n ∈ s.support,
        s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, mu d := by
  symm
  calc
    _ = ∑ n ∈ s.support, ∑ d ∈ s.prodPrimes.divisors,
        if d ∣ n then s.weights n * mu d else 0 := by
      simp_rw [mul_sum, ← sum_filter]
      congr with n
      congr
      rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
        (Nat.gcd_dvd_left _ _)]
      ext d
      simp +contextual [dvd_gcd_iff]
    _ = _ := by
      rw [sum_comm]
      simp_rw [BoundingSieve.multSum, ← sum_filter, mul_sum, mul_comm]

/-- Lower coefficients give a lower bound on the finite sifted sum. -/
theorem sum_le_siftedSum_of_lowerMoebius
    (mu : ℕ → ℝ) (hmu : IsLowerMoebius s.prodPrimes mu) :
    (∑ d ∈ s.prodPrimes.divisors, mu d * s.multSum d) ≤ s.siftedSum := by
  rw [sum_divisors_multSum, s.siftedSum_eq_sum_support_mul_ite]
  exact sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
    (hmu (Nat.gcd s.prodPrimes n) (Nat.gcd_dvd_left _ _)) (s.weights_nonneg n)

/-- The lower sieve bound with the signed remainder replaced by its
absolute majorant. -/
theorem mainSum_sub_errSum_le_siftedSum
    (mu : ℕ → ℝ) (hmu : IsLowerMoebius s.prodPrimes mu) :
    s.totalMass * s.mainSum mu - s.errSum mu ≤ s.siftedSum := by
  calc
    _ ≤ s.totalMass * s.mainSum mu +
        ∑ d ∈ s.prodPrimes.divisors, mu d * s.rem d := by
      rw [sub_eq_add_neg, BoundingSieve.errSum, ← sum_neg_distrib]
      apply _root_.add_le_add le_rfl
      apply sum_le_sum
      intro d _
      rw [← abs_mul]
      exact neg_abs_le _
    _ = ∑ d ∈ s.prodPrimes.divisors, mu d * s.multSum d := by
      rw [BoundingSieve.mainSum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      rw [s.multSum_eq_main_err]
      ring
    _ ≤ s.siftedSum := sum_le_siftedSum_of_lowerMoebius mu hmu

/-- Coefficients bounded by one and supported at level `Q` reduce the
sieve remainder to an unweighted sum of error majorants. This is the finite
interface needed before applying a level-of-distribution estimate. -/
theorem errSum_le_sum_of_level
    (mu E : ℕ → ℝ) (Q : ℕ)
    (hlevel : ∀ d, Q < d → mu d = 0)
    (hmu : ∀ d ∈ s.prodPrimes.divisors, |mu d| ≤ 1)
    (hE : ∀ d, 0 ≤ E d)
    (hrem : ∀ d ∈ s.prodPrimes.divisors, d ≤ Q → |s.rem d| ≤ E d) :
    s.errSum mu ≤ ∑ d ∈ Icc 1 Q, E d := by
  let D := s.prodPrimes.divisors.filter (· ≤ Q)
  have hD : D ⊆ Icc 1 Q := by
    intro d hd
    rcases mem_filter.mp hd with ⟨hd, hQ⟩
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, hQ⟩
  have heq : s.errSum mu = ∑ d ∈ D, |mu d| * |s.rem d| := by
    unfold BoundingSieve.errSum
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hnot
    have hQ : Q < d := by
      have : ¬d ≤ Q := by
        intro hdQ
        exact hnot (mem_filter.mpr ⟨hd, hdQ⟩)
      omega
    simp [hlevel d hQ]
  rw [heq]
  calc
    _ ≤ ∑ d ∈ D, E d := by
      apply sum_le_sum
      intro d hd
      rcases mem_filter.mp hd with ⟨hd, hdQ⟩
      calc
        |mu d| * |s.rem d| ≤ 1 * |s.rem d| :=
          mul_le_mul_of_nonneg_right (hmu d hd) (abs_nonneg _)
        _ ≤ E d := by simpa using hrem d hd hdQ
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => hE d)

end Chen.LinearSieve
