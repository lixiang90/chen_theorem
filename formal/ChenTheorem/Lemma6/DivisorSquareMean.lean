import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import ChenTheorem.Lemma6.Mollifier

/-!
# The divisor-square mean needed in Lemma 6

Chen uses `∑_{n ≤ X} τ(n)² ≪ X (log X)³` immediately before equation (14).
This file isolates that arithmetic input from the character large sieve and
proves its weighted dyadic consequence.
-/

open scoped Classical

namespace Chen

/-- The divisor-square mean estimate used in equation (14).  The separate
arithmetic proof of this proposition is the next elementary input required
by the Lemma 6 argument. -/
def Lemma6DivisorSquareMean : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
    ∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 ≤
      C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3

/-- The divisor-square mean implies the weighted interval estimate that
occurs after applying the large sieve to `C_H(n) / n^ω`. -/
theorem lemma6_divisorSquare_weighted_Ioc_le
    (hmean : Lemma6DivisorSquareMean) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ M → 2 ≤ M + N →
      ∑ n ∈ Finset.Ioc M (M + N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
        C * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
          (M : ℝ) ^ 2 := by
  rcases hmean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro M N hM hMN
  let S := Finset.Ioc M (M + N)
  let T := Finset.Icc 1 (M + N)
  have hST : S ⊆ T := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
  have hpoint : ∀ n ∈ S,
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1.le
    have hsq : (M : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMn 2
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hsq
  calc
    ∑ n ∈ S,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
      ∑ n ∈ S,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun n hn => hpoint n hn
    _ = (∑ n ∈ S, (n.divisorsAntidiagonal.card : ℝ) ^ 2) /
        (M : ℝ) ^ 2 := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ T, (n.divisorsAntidiagonal.card : ℝ) ^ 2) /
        (M : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum_of_subset_of_nonneg hST
        intro n hnT hnS
        positivity
      · positivity
    _ ≤ (C * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3) /
        (M : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right (hmean (M + N) hMN)
      positivity

end Chen
