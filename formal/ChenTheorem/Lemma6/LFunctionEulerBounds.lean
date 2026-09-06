import ChenTheorem.Lemma6.StripGrowth
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SumIntegralComparisons

open Set MeasureTheory
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace Chen

theorem tsum_nat_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hsum := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Ici ((1 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono
      (fun t ht => by
        have ht' : (1 : ℝ) ≤ t := by simpa using ht
        change 0 < t
        linarith)
  have hint : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Ioi ((1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun t : ℝ => t ^ (-σ))
    (1 : ℕ) hanti hint (fun t ht => Real.rpow_nonneg (by
      have ht' : (1 : ℝ) < t := by simpa using ht
      linarith) _)
  have hi : (∫ t : ℝ in Ioi ((1 : ℕ) : ℝ), t ^ (-σ)) = 1 / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    norm_num only [Nat.cast_one, Real.one_rpow]
    field_simp [show σ - 1 ≠ 0 by linarith, show -σ + 1 ≠ 0 by linarith]
    ring
  rw [hi] at htail
  rw [← hsum.sum_add_tsum_nat_add 2]
  norm_num [Finset.sum_range_succ, Real.zero_rpow (by linarith : -σ ≠ 0)]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num, one_div] using htail

theorem norm_LSeries_le_of_unit_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : ‖LSeries f s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hsum : LSeriesSummable f s := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hs
  have hpow := Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)
  calc
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
      apply hsum.norm.tsum_le_tsum _ hpow
      intro n
      by_cases hn : n = 0
      · subst n
        simp [LSeries.term_zero, Real.zero_rpow (by linarith : -s.re ≠ 0)]
      · rw [LSeries.norm_term_eq, if_neg hn, Real.rpow_neg (Nat.cast_nonneg n)]
        exact (div_le_div_of_nonneg_right (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans_eq (one_div _)
    _ ≤ _ := tsum_nat_rpow_neg_le s.re hs

theorem norm_LFunction_euler_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) : ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact norm_LSeries_le_of_unit_bound _ (fun n => χ.norm_le_one n) s hs

/-- An absolute lower bound to the right of one, obtained from the
Möbius-twisted inverse series. It supplies an anchor for disk estimates. -/
theorem norm_LFunction_euler_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hmu : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := by
    intro n
    rw [Pi.mul_apply, norm_mul]
    have hm : ‖(μ n : ℂ)‖ ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    exact mul_le_one₀ (χ.norm_le_one n) (norm_nonneg _) hm
  have hb := norm_LSeries_le_of_unit_bound (↗χ * ↗μ) hmu s hs
  have hprod := congrArg norm (DirichletCharacter.LSeries.mul_mu_eq_one χ hs)
  rw [norm_mul, norm_one] at hprod
  have hB : 0 < 1 + 1 / (s.re - 1) := by positivity
  have hl : 1 / (1 + 1 / (s.re - 1)) ≤ ‖L ↗χ s‖ := by
    apply (div_le_iff₀ hB).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (L ↗χ s))]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  convert hl using 1
  field_simp [show s.re - 1 ≠ 0 by linarith, show s.re ≠ 0 by linarith]
  ring

end Chen
