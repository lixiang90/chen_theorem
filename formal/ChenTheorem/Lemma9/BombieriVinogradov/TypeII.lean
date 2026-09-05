import ChenTheorem.Lemma9.BombieriVinogradov.TypeI
import ChenTheorem.Lemma9.BombieriVinogradov.Maximal
import ChenTheorem.Lemma6.DivisorSquareMeanProof

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Type-II structure for Bombieri--Vinogradov

This file packages the two long factors in Vaughan's identity into a single
coefficient, proves its exact support, and exposes the remaining zeta factor
as a finite hyperbola sum.  This is the input for the subsequent dyadic
rectangle decomposition and character large sieve.
-/

/-- The convolution coefficient carried by the two long variables in
Vaughan's Type-II term. -/
noncomputable def vaughanTypeIICoefficient (U V : ℕ) :
    ArithmeticFunction ℝ :=
  truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    truncateGT ArithmeticFunction.vonMangoldt V

theorem vaughanTypeII_eq_coefficient_mul_zeta (U V : ℕ) :
    vaughanTypeII U V =
      vaughanTypeIICoefficient U V * ArithmeticFunction.zeta := by
  rfl

/-- The standard left factor in the genuinely bilinear form of Vaughan's
Type-II term.  Associating the zeta factor here, rather than after the two
long variables have already been convolved, keeps both variables visible. -/
noncomputable def vaughanTypeIILeftCoefficient (U : ℕ) :
    ArithmeticFunction ℝ :=
  truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    ArithmeticFunction.zeta

theorem vaughanTypeII_eq_leftCoefficient_mul_longLambda (U V : ℕ) :
    vaughanTypeII U V =
      vaughanTypeIILeftCoefficient U *
        truncateGT ArithmeticFunction.vonMangoldt V := by
  rw [vaughanTypeII, vaughanTypeIILeftCoefficient]
  ac_rfl

/-- The left Type-II coefficient has no support at or below its cutoff. -/
theorem vaughanTypeIILeftCoefficient_eq_zero_of_le
    (U n : ℕ) (hn : n ≤ U) :
    vaughanTypeIILeftCoefficient U n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [vaughanTypeIILeftCoefficient]
  rw [vaughanTypeIILeftCoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
  have hp1dvd : p.1 ∣ n := ⟨p.2, hpdata.1.symm⟩
  have hp1le : p.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp1dvd
  have hp1U : p.1 ≤ U := hp1le.trans hn
  simp [truncateGT_apply, Nat.not_lt.mpr hp1U]

/-- Pointwise divisor bound for the visible left Type-II coefficient. -/
theorem abs_vaughanTypeIILeftCoefficient_le
    (U n : ℕ) :
    |vaughanTypeIILeftCoefficient U n| ≤
      (n.divisorsAntidiagonal.card : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanTypeIILeftCoefficient]
  rw [vaughanTypeIILeftCoefficient, ArithmeticFunction.mul_apply]
  calc
    |∑ p ∈ n.divisorsAntidiagonal,
        truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          ArithmeticFunction.zeta p.2| ≤
        ∑ p ∈ n.divisorsAntidiagonal,
          |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
            ArithmeticFunction.zeta p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2ne : p.2 ≠ 0 :=
        Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
      have hmu :
          |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| ≤ 1 := by
        rw [truncateGT_apply]
        split_ifs
        · change |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
        · norm_num
      simpa [ArithmeticFunction.zeta_apply, hp2ne] using hmu
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp

/-- The divisor-square theorem gives the `L²` input for the standard visible
left factor, without the extra logarithm carried by the grouped coefficient. -/
theorem vaughanTypeIILeftCoefficient_sq_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (U X : ℕ), 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
        C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3 := by
  rcases Chen.lemma6_divisorSquareMean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U X hX
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_vaughanTypeIILeftCoefficient_le U n) 2
    _ ≤ C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3 := hmean X hX

/-- The Type-II convolution vanishes below the product of its two strict
cutoffs. -/
theorem vaughanTypeIICoefficient_eq_zero_of_le
    (U V n : ℕ) (hn : n ≤ U * V) :
    vaughanTypeIICoefficient U V n = 0 := by
  rw [vaughanTypeIICoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hd : U < p.1
  · by_cases he : V < p.2
    · have huv : U * V < p.1 * p.2 :=
        Nat.mul_lt_mul_of_lt_of_lt hd he
      omega
    · simp [truncateGT_apply, hd, Nat.not_lt.mpr (le_of_not_gt he)]
  · simp [truncateGT_apply, Nat.not_lt.mpr (le_of_not_gt hd)]

/-- A cutoff-independent divisor bound for the Type-II coefficient. -/
theorem abs_vaughanTypeIICoefficient_le
    (U V n : ℕ) :
    |vaughanTypeIICoefficient U V n| ≤
      (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanTypeIICoefficient]
  rw [vaughanTypeIICoefficient, ArithmeticFunction.mul_apply]
  calc
    |∑ p ∈ n.divisorsAntidiagonal,
        truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateGT ArithmeticFunction.vonMangoldt V p.2| ≤
      ∑ p ∈ n.divisorsAntidiagonal,
        |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateGT ArithmeticFunction.vonMangoldt V p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, Real.log n := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1pos : 0 < p.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2pos : 0 < p.2 :=
        Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2dvd : p.2 ∣ n := ⟨p.1, by simpa [mul_comm] using hpdata.1.symm⟩
      have hp2le : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp2dvd
      have hlogmono : Real.log (p.2 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp2pos) (by exact_mod_cast hp2le)
      have hmu :
          |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| ≤ 1 := by
        rw [truncateGT_apply]
        split_ifs
        · change |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
        · norm_num
      have hlambda :
          |truncateGT ArithmeticFunction.vonMangoldt V p.2| ≤ Real.log n := by
        rw [truncateGT_apply]
        split_ifs
        · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact ArithmeticFunction.vonMangoldt_le_log.trans hlogmono
        · rw [abs_zero]
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      rw [abs_mul]
      calc
        |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| *
            |truncateGT ArithmeticFunction.vonMangoldt V p.2| ≤
            1 * Real.log n := by gcongr
        _ = Real.log n := one_mul _
    _ = (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by simp

/-- The divisor-square mean gives the standard `L²` bound for Vaughan's
Type-II coefficient. -/
theorem vaughanTypeIICoefficient_sq_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V X : ℕ), 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
          C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by
  rcases Chen.lemma6_divisorSquareMean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U V X hX
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
          (Real.log (X : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hndata := Finset.mem_Icc.mp hn
      have hlogn : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hndata.1)
      have hlogmono : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hndata.2)
      have habs := abs_vaughanTypeIICoefficient_le U V n
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        |vaughanTypeIICoefficient U V n| ^ 2 ≤
            ((n.divisorsAntidiagonal.card : ℝ) * Real.log n) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ ≤ ((n.divisorsAntidiagonal.card : ℝ) * Real.log X) ^ 2 := by
          gcongr
        _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
            (Real.log X) ^ 2 := by ring
    _ = (∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2) *
        (Real.log X) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (C * (X : ℝ) * (Real.log X) ^ 3) *
        (Real.log X) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (hmean X hX) (sq_nonneg _)
    _ = C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by ring

/-- A Type-II dyadic rectangle, specialized to Vaughan's coefficient on one
side and the constant coefficient on the zeta side. -/
theorem vaughanTypeIIRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U V D Q M N K L : ℕ), 1 ≤ D → D ≤ Q → 2 ≤ M + N →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N
                (fun n => (vaughanTypeIICoefficient U V n : ℂ)) i.2‖ *
              ‖characterIntervalSum K L (fun _ => (1 : ℂ)) i.2‖) ^ 2 ≤
          (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              (C₁ * ((M + N : ℕ) : ℝ) *
                (Real.log ((M + N : ℕ) : ℝ)) ^ 5)) *
            (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) * (L : ℝ)) := by
  rcases bilinearCharacterMean_dyadic_sq_le with ⟨C₀, hC₀, hbilinear⟩
  rcases vaughanTypeIICoefficient_sq_mean with ⟨C₁, hC₁, hcoeffMean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U V D Q M N K L hD hDQ hMN
  have hcoeff :
      (∑ n ∈ Finset.Ioc M (M + N),
        ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
          C₁ * ((M + N : ℕ) : ℝ) *
            (Real.log ((M + N : ℕ) : ℝ)) ^ 5 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 :=
        hcoeffMean U V (M + N) hMN
  have hbase := hbilinear D Q M N K L
    (fun n => (vaughanTypeIICoefficient U V n : ℂ))
    (fun _ => (1 : ℂ)) hD hDQ
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · simp
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₁.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 5))

/-- Rectangular large-sieve estimate for the standard visible Type-II
factors `μ_{>U}*1` and `Λ_{>V}`. -/
theorem vaughanTypeIIVisibleRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U D Q M N K L : ℕ),
        1 ≤ D → D ≤ Q → 2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M N
                  (fun n => (vaughanTypeIILeftCoefficient U n : ℂ)) i.2‖ *
                ‖characterIntervalSum K L
                  (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) i.2‖) ^ 2 ≤
            (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
                (C₁ * ((M + N : ℕ) : ℝ) *
                  (Real.log ((M + N : ℕ) : ℝ)) ^ 3)) *
              (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) *
                ((L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2)) := by
  rcases bilinearCharacterMean_dyadic_sq_le with ⟨C₀, hC₀, hbilinear⟩
  rcases vaughanTypeIILeftCoefficient_sq_mean with ⟨C₁, hC₁, hleftMean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U D Q M N K L hD hDQ hMN hKL
  have hleft :
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
        C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
          ∑ n ∈ Finset.Icc 1 (M + N),
            ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 :=
        hleftMean U (M + N) hMN
  have hlambda :
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) ≤
        (L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by
    calc
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) ≤
          ∑ _n ∈ Finset.Ioc K (K + L),
            (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hndata := Finset.mem_Ioc.mp hn
        have hnpos : 0 < n := by omega
        have hlogn : 0 ≤ Real.log (n : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
        have hlogmono : Real.log (n : ℝ) ≤ Real.log ((K + L : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hnpos)
            (by exact_mod_cast hndata.2)
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
          (ArithmeticFunction.vonMangoldt_le_log.trans hlogmono) 2
      _ = (L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by simp
  have hbase := hbilinear D Q M N K L
    (fun n => (vaughanTypeIILeftCoefficient U n : ℂ))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) hD hDQ
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · gcongr
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₁.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 3))

/-- Type-II rectangle estimate with a character-dependent prefix in the
constant-coefficient factor.  This is the form needed at the staircase
boundary of a dyadic cover of `m*n ≤ x`. -/
theorem vaughanTypeIIMaximalRectangleMean_sq_le :
    ∃ C₀ C₁ C₂ : ℝ,
      0 < C₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (U V D Q M N K R L : ℕ),
        1 ≤ D → D ≤ Q → 2 ≤ M + N → R ≤ 2 ^ L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M N
                  (fun n => (vaughanTypeIICoefficient U V n : ℂ)) i.2‖ *
                Real.sqrt
                  (maxCharacterPrefixSq K R (fun _ => (1 : ℂ)) i.2)) ^ 2 ≤
            (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
                (C₂ * ((M + N : ℕ) : ℝ) *
                  (Real.log ((M + N : ℕ) : ℝ)) ^ 5)) *
              (C₁ * (((L + 1 : ℕ) : ℝ) ^ 2) *
                ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
                  ((2 ^ L : ℕ) : ℝ)) := by
  rcases maximalBilinearCharacterMean_dyadic_sq_le with
    ⟨C₀, C₁, hC₀, hC₁, hmaximal⟩
  rcases vaughanTypeIICoefficient_sq_mean with ⟨C₂, hC₂, hcoeffMean⟩
  refine ⟨C₀, C₁, C₂, hC₀, hC₁, hC₂, ?_⟩
  intro U V D Q M N K R L hD hDQ hMN hR
  have hcoeff :
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
        C₂ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
          ∑ n ∈ Finset.Icc 1 (M + N),
            ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₂ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 :=
        hcoeffMean U V (M + N) hMN
  have hbase := hmaximal D Q M N K R L
    (fun n => (vaughanTypeIICoefficient U V n : ℂ))
    (fun _ => (1 : ℂ)) hD hDQ hR
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · simp
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg hC₁.le (sq_nonneg _)) (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₂.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 5))

/-- Exact Type-II hyperbola expansion before dyadic subdivision. -/
theorem vaughanTypeIISum_eq_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ m ∈ Finset.Ioc 0 x,
        (vaughanTypeIICoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeIISum, vaughanTypeII_eq_coefficient_mul_zeta]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval, sum_characterTwist_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : n ≠ 0 := (Finset.mem_Ioc.mp hn).1.ne'
  simp [ArithmeticFunction.zeta_apply, hnpos]

/-- Standard two-long-variable form of Vaughan's Type-II sum.  Unlike the
grouped-coefficient expansion above, this exposes the separate supports
`l > U` and `m > V`, which is the form required by the bilinear large sieve. -/
theorem vaughanTypeIISum_eq_visible_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ l ∈ Finset.Ioc U x,
        (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
          ∑ m ∈ Finset.Ioc V (x / l),
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ m := by
  rw [vaughanTypeIISum, vaughanTypeII_eq_leftCoefficient_mul_longLambda]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval, sum_characterTwist_mul_eq_sum_sum]
  let term : ℕ → ℂ := fun l =>
    (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
      ∑ m ∈ Finset.Ioc 0 (x / l),
        (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m
  calc
    (∑ l ∈ Finset.Ioc 0 x,
        (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
          ∑ m ∈ Finset.Ioc 0 (x / l),
            (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m) =
        ∑ l ∈ Finset.Ioc U x, term l := by
      symm
      apply Finset.sum_subset
      · intro l hl
        have hl' := Finset.mem_Ioc.mp hl
        exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hl'.1, hl'.2⟩
      · intro l hlx hlnot
        have hldata := Finset.mem_Ioc.mp hlx
        have hlU : l ≤ U := by
          by_contra h
          exact hlnot (Finset.mem_Ioc.mpr ⟨lt_of_not_ge h, hldata.2⟩)
        dsimp only [term]
        rw [vaughanTypeIILeftCoefficient_eq_zero_of_le U l hlU]
        simp
    _ = ∑ l ∈ Finset.Ioc U x,
        (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
          ∑ m ∈ Finset.Ioc V (x / l),
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ m := by
      apply Finset.sum_congr rfl
      intro l hl
      dsimp only [term]
      congr 1
      let innerTerm : ℕ → ℂ := fun m =>
        (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m
      calc
        (∑ m ∈ Finset.Ioc 0 (x / l),
            (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m) =
            ∑ m ∈ Finset.Ioc V (x / l), innerTerm m := by
          symm
          apply Finset.sum_subset
          · intro m hm
            have hm' := Finset.mem_Ioc.mp hm
            exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hm'.1, hm'.2⟩
          · intro m hmx hmnot
            have hmdata := Finset.mem_Ioc.mp hmx
            have hmV : m ≤ V := by
              by_contra h
              exact hmnot (Finset.mem_Ioc.mpr
                ⟨lt_of_not_ge h, hmdata.2⟩)
            simp [innerTerm, truncateGT_apply, Nat.not_lt.mpr hmV]
        _ = ∑ m ∈ Finset.Ioc V (x / l),
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ m := by
          apply Finset.sum_congr rfl
          intro m hm
          have hmV : V < m := (Finset.mem_Ioc.mp hm).1
          simp [innerTerm, truncateGT_apply, hmV]

/-- The same expansion with the vanishing range `m ≤ U*V` removed. -/
theorem vaughanTypeIISum_eq_long_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ m ∈ Finset.Ioc (U * V) x,
        (vaughanTypeIICoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeIISum_eq_hyperbola]
  symm
  apply Finset.sum_subset
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hm'.1, hm'.2⟩
  · intro m hm hmlong
    have hmdata := Finset.mem_Ioc.mp hm
    have hmle : m ≤ U * V := by
      by_contra h
      exact hmlong (Finset.mem_Ioc.mpr ⟨lt_of_not_ge h, hmdata.2⟩)
    rw [vaughanTypeIICoefficient_eq_zero_of_le U V m hmle]
    simp

/-- The finite lattice region below the Type-II hyperbola. -/
noncomputable def typeIIHyperbolaPairs (x U V : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc (U * V) x ×ˢ Finset.Ioc 0 x).filter
    (fun p => p.1 * p.2 ≤ x)

/-- Exact two-variable form of the Type-II sum. -/
theorem vaughanTypeIISum_eq_pairSum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ p ∈ typeIIHyperbolaPairs x U V,
        (vaughanTypeIICoefficient U V p.1 : ℂ) * χ p.1 * χ p.2 := by
  rw [vaughanTypeIISum_eq_long_hyperbola]
  rw [typeIIHyperbolaPairs, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hm).1
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    constructor
    · intro hn
      exact ⟨⟨hn.1, hn.2.trans (Nat.div_le_self x m)⟩,
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hmpos).mp hn.2⟩
    · intro hn
      exact ⟨hn.1.1, (Nat.le_div_iff_mul_le hmpos).mpr (by
        simpa [Nat.mul_comm] using hn.2)⟩
  · intro n hn
    rfl

end Chen.BombieriVinogradov
