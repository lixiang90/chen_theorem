/-
Assembly of the three moment estimates in equation (20) of Chen's proof.
-/
import ChenTheorem.Lemma6.Equation19

open Real Filter
open scoped Classical

namespace Chen

/-- Insert bounds for the mollifier second moment, `L'` fourth moment, and
pair-polynomial fourth moment into the `2,4,4` Hölder ordering of (20). -/
theorem lemma6_equation20_B_of_moment_bounds
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) (S2 L4 P4 : ℝ)
    (hmollifier :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ≤ S2)
    (hderiv :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤ L4)
    (hpair :
      (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4) ≤ P4) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l * S2) ^ 2 * L4 * P4 := by
  have hmollifier0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (sq_nonneg _)
  have hderiv0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hpair0 : 0 ≤
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lemma6PrimitiveBaseWeight_nonneg i) (by positivity)
  have hS20 : 0 ≤ S2 := hmollifier0.trans hmollifier
  have hL40 : 0 ≤ L4 := hderiv0.trans hderiv
  have hP40 : 0 ≤ P4 := hpair0.trans hpair
  have hI0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
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
              lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4 :=
      lemma6_equation20_B_holder hxlarge m k H ν
    _ ≤ (lemma6ExceptionalFactorAt x l * S2) ^ 2 * L4 * P4 := by
      gcongr

/-- Large-sieve majorant for the mollifier second moment in (20). -/
noncomputable def lemma6MollifierSecondMajorant
    (x l H : ℕ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      (H : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
    (1 + Real.log H)

/-- Large-sieve majorant for the pair-polynomial fourth moment in (20). -/
noncomputable def lemma6PairFourthMajorant
    (x l m k : ℕ) (s : ℂ) : ℝ :=
  ((lemma6ModulusCutoff x l : ℝ) +
      (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
        (lemma6ModulusLowerCutoff x l : ℝ)) *
  ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
      ‖lemma6PairSquareCoefficient x m k s r‖ ^ 2

/-- The pair fourth-moment majorant after the squared coefficients are
controlled by the divisor-square mean. -/
theorem lemma6PairFourthMajorant_beta_le_log_four :
    ∃ C : ℝ, 0 < C ∧ ∀ (x l m k : ℕ) (ν : ℝ),
      3 ≤ Real.log (x : ℝ) → 2 ≤ lemma6PairUpperCutoff x k ^ 2 →
      lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν) ≤
        C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
          (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by
  rcases lemma6_pairSquareCoefficient_sum_sq_beta_le_log_four with
    ⟨C, hC, hcoeff⟩
  refine ⟨C, hC, ?_⟩
  intro x l m k ν hxlog hU
  unfold lemma6PairFourthMajorant
  calc
    ((lemma6ModulusCutoff x l : ℝ) +
        (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ)) *
      ∑ r ∈ Finset.Ioc 0 (lemma6PairUpperCutoff x k ^ 2),
        ‖lemma6PairSquareCoefficient x m k
          (lemma6BetaPoint x ν) r‖ ^ 2 ≤
      ((lemma6ModulusCutoff x l : ℝ) +
        (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
          (lemma6ModulusLowerCutoff x l : ℝ)) *
        (C * (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4) := by
      gcongr
      exact hcoeff x m k ν hxlog hU
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          (lemma6PairUpperCutoff x k ^ 2 : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
        (Real.log (lemma6PairUpperCutoff x k ^ 2 : ℕ)) ^ 4 := by ring

/-- Formula (20) with all three moments instantiated.  The remaining
paper-specific work is to simplify the two coefficient majorants under the
third regime returned by `lemma6_occupied_pair_modulus_regime_split` and
to perform the `ν` integral. -/
theorem lemma6_equation20_B_with_large_sieve_moments_of_deriv_fourth_moment
    (hfourth : Lemma6DerivativeFourthMoment) :
    ∃ Cs Cd Cp : ℝ, 0 < Cs ∧ 0 < Cd ∧ 0 < Cp ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ (l m k H : ℕ) (ν : ℝ), 1 ≤ l →
          (∑ i ∈ lemma6CharacterBlock x l,
              lemma6PrimitiveBaseWeight i *
                (3 : ℝ) ^ distinctPrimeFactors i.1 *
                lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
                lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
                lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
            (lemma6ExceptionalFactorAt x l *
              (Cs * lemma6MollifierSecondMajorant x l H)) ^ 2 *
              (Cd * lemma6DerivativeFourthMajorant x l ν) *
                (Cp * lemma6PairFourthMajorant x l m k
                  (lemma6BetaPoint x ν)) := by
  rcases lemma6_mollifier_second_moment_characterBlock with
    ⟨Cs, hCs, hmollifier⟩
  rcases lemma6_deriv_fourth_moment_characterBlock_of hfourth with
    ⟨Cd, hCd, hderiv⟩
  rcases lemma6_pair_fourth_moment_characterBlock with
    ⟨Cp, hCp, hpair⟩
  refine ⟨Cs, Cd, Cp, hCs, hCd, hCp, ?_⟩
  have hlogReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hderiv, hlog,
    eventually_exp_exp_one_le_log_pow_hundred] with x hxderiv hxlog hxlarge
  intro l m k H ν hl
  apply lemma6_equation20_B_of_moment_bounds hxlarge m k H ν
      (Cs * lemma6MollifierSecondMajorant x l H)
      (Cd * lemma6DerivativeFourthMajorant x l ν)
      (Cp * lemma6PairFourthMajorant x l m k (lemma6BetaPoint x ν))
  · simpa only [lemma6MollifierSecondMajorant, mul_assoc] using
      hmollifier x l H ν hxlog
  · simpa only [lemma6DerivativeFourthMajorant, mul_assoc] using
      hxderiv l ν hl
  · simpa only [lemma6PairFourthMajorant, mul_assoc] using
      hpair x l m k (lemma6BetaPoint x ν) hxlog

end Chen
