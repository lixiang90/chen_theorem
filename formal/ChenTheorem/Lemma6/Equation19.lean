/-
Assembly of the three moment estimates in equation (19) of Chen's proof.
-/
import ChenTheorem.Lemma6.PairLargeSieve

open Real Filter
open scoped Classical

namespace Chen

/-- Insert independent bounds for the pair second moment, mollifier fourth
moment, and `L'` fourth moment into the `2,4,4` Hölder inequality (19). -/
theorem lemma6_equation19_B_of_moment_bounds
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) (P M L : ℝ)
    (hpair :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ≤ P)
    (hmollifier :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤ M)
    (hderiv :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤ L) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l * P) ^ 2 * M * L := by
  have hpair0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (sq_nonneg _)
  have hmollifier0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hderiv0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hP0 : 0 ≤ P := hpair0.trans hpair
  have hM0 : 0 ≤ M := hmollifier0.trans hmollifier
  have hL0 : 0 ≤ L := hderiv0.trans hderiv
  have hE0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 :=
      lemma6_equation19_B_holder hxlarge m k H ν
    _ ≤ (lemma6ExceptionalFactorAt x l * P) ^ 2 * M * L := by
      gcongr

/-- Large-sieve majorant for the pair-polynomial second moment. -/
noncomputable def lemma6PairSecondMajorant
    (x l m k : ℕ) (s : ℂ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      ((lemma6PairUpperCutoff x k -
        lemma6PairLowerCutoff x k : ℕ) : ℝ) /
        (lemma6ModulusLowerCutoff x l : ℝ)) *
    ∑ n ∈ Finset.Ioc (lemma6PairLowerCutoff x k)
      (lemma6PairUpperCutoff x k),
        ‖lemma6PairCoefficient x
          (lemma6AdmissiblePairBlock x m k) s n‖ ^ 2

/-- The pair second-moment majorant on the `β`-line after the coefficient
sum is reduced to a scalar logarithm. -/
theorem lemma6PairSecondMajorant_beta_le_log
    (x l m k : ℕ) (ν : ℝ) (hxlog : 3 ≤ Real.log (x : ℝ)) :
    lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν) ≤
      ((lemma6ModulusCutoff x l : ℝ) +
          ((lemma6PairUpperCutoff x k -
            lemma6PairLowerCutoff x k : ℕ) : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        (1 + Real.log (lemma6PairUpperCutoff x k)) := by
  unfold lemma6PairSecondMajorant
  apply mul_le_mul_of_nonneg_left
    (lemma6_pairCoefficient_sum_sq_beta_le_log x m k ν hxlog)
  positivity

/-- Equation-(15) majorant for the mollifier fourth moment. -/
noncomputable def lemma6MollifierFourthMajorant
    (x l H : ℕ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      ((H * H : ℕ) : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
    (Real.log ((H * H : ℕ) : ℝ)) ^ 4

/-- Lemma-3/Cauchy majorant for the fourth moment of `L'`. -/
noncomputable def lemma6DerivativeFourthMajorant
    (x l : ℕ) (ν : ℝ) : ℝ :=
  (2 : ℝ) ^ l * (Real.log x) ^ 110 *
    ‖lemma6BetaPoint x ν‖ ^ 2 * (1 + ν ^ 2) ^ 2

/-- Formula (19), with all three moment inputs instantiated by the results
proved in `PairLargeSieve`, `MomentConnection`, and `FourthMoment`.

The remaining work for the printed numerical exponent is now elementary:
bound the three displayed majorants for Chen's choices of `H`, `k`, and
`l`, then integrate in `ν`. -/
theorem lemma6_equation19_B_with_large_sieve_moments_of_deriv_fourth_moment
    (hfourth : Lemma6DerivativeFourthMoment) :
    ∃ Cp Cm Cd : ℝ, 0 < Cp ∧ 0 < Cm ∧ 0 < Cd ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ (l m k H : ℕ) (ν : ℝ), 1 ≤ l → 2 ≤ H →
          (∑ i ∈ lemma6CharacterBlock x l,
              lemma6PrimitiveBaseWeight i *
                (3 : ℝ) ^ distinctPrimeFactors i.1 *
                lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
                lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
                lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
            (lemma6ExceptionalFactorAt x l *
              (Cp * lemma6PairSecondMajorant x l m k
                (lemma6BetaPoint x ν))) ^ 2 *
              (Cm * lemma6MollifierFourthMajorant x l H) *
                (Cd * lemma6DerivativeFourthMajorant x l ν) := by
  rcases lemma6_pair_second_moment_characterBlock with
    ⟨Cp, hCp, hpair⟩
  rcases lemma6_mollifier_fourth_moment_characterBlock with
    ⟨Cm, hCm, hmollifier⟩
  rcases lemma6_deriv_fourth_moment_characterBlock_of hfourth with
    ⟨Cd, hCd, hderiv⟩
  refine ⟨Cp, Cm, Cd, hCp, hCm, hCd, ?_⟩
  have hlogReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hderiv, hlog,
    eventually_exp_exp_one_le_log_pow_hundred] with x hxderiv hxlog hxlarge
  intro l m k H ν hl hH
  apply lemma6_equation19_B_of_moment_bounds hxlarge m k H ν
      (Cp * lemma6PairSecondMajorant x l m k (lemma6BetaPoint x ν))
      (Cm * lemma6MollifierFourthMajorant x l H)
      (Cd * lemma6DerivativeFourthMajorant x l ν)
  · simpa only [lemma6PairSecondMajorant, mul_assoc] using
      hpair x l m k (lemma6BetaPoint x ν) hxlog
  · simpa only [lemma6MollifierFourthMajorant, mul_assoc] using
      hmollifier x l H ν hxlog hH
  · simpa only [lemma6DerivativeFourthMajorant, mul_assoc] using
      hxderiv l ν hl

end Chen
