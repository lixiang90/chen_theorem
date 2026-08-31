import ChenTheorem.Main.ShiftedLemma6

open Filter Real MeasureTheory
open scoped Classical

namespace Chen

/-! # Fixed-shift large-conductor assembly for Lemma 6

The character phase has already disappeared from the scalar majorants proved
in `ShiftedLemma6`.  This file instantiates the original moment estimates and
rebuilds only the occupied-block parameter bounds for the shifted modulus set.
-/

theorem eventually_shifted_sum_largeConductor_pairTerm_le_scalar20_majorant
    (hfourth : Lemma6DerivativeFourthMoment) (h : ℕ) (ε : ℝ) :
    ∃ Cpair CremP CremT Cs Cd Cp C4 : ℝ,
      0 < Cpair ∧ 0 < CremP ∧ 0 < CremT ∧
      0 < Cs ∧ 0 < Cd ∧ 0 < Cp ∧ 0 < C4 ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ (m l k H : ℕ),
          1 ≤ l → 4 ≤ lemma6DyadicModulusScale x l →
          2 ≤ lemma6PairDyadicScale x k → 2 ≤ H →
          1 ≤ Real.log (H : ℝ) →
          Real.log ((2 * H * H : ℕ) : ℝ) ≤ 8 * Real.log (x : ℝ) →
          Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
            2 * Real.log (x : ℝ) →
          (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
              (fun d => d ∈ lemma6ModulusBlock x l),
            shiftedLemma6NmPairTerm h x m d k) ≤
            lemma6LargePairBlock20Majorant x l k H
              Cpair CremP CremT Cs Cd Cp C4 := by
  rcases lemma6_equation19_A_with_large_sieve_moments with
    ⟨Cpair, CremP, CremT, hCpair, hCremP, hCremT, hA⟩
  rcases lemma6_mollifier_second_moment_characterBlock with
    ⟨Cs, hCs, hmol⟩
  rcases lemma6_deriv_fourth_moment_characterBlock_of hfourth with
    ⟨Cd, hCd, hder⟩
  rcases lemma6_pair_fourth_moment_characterBlock with
    ⟨Cp, hCp, hpair⟩
  rcases lemma6PairFourthMajorant_beta_le_scales with
    ⟨C4, hC4, hpairScale⟩
  refine ⟨Cpair, CremP, CremT, Cs, Cd, Cp, C4,
    hCpair, hCremP, hCremT, hCs, hCd, hCp, hC4, ?_⟩
  filter_upwards [hder, eventually_exp_exp_one_le_log_pow_hundred,
    eventually_three_le_log_nat, eventually_ge_atTop 2] with
      x hxder hxlarge hxlog hx2
  intro m l k H hl hD4 hY hH2 hlogH hlogHH hlogQ
  apply shifted_sum_largeConductor_pairTerm_le_scalar20_majorant
    (h := h) hx2 hxlarge hxlog ε m l k H
    hCpair.le hCremP hCremT hCs.le hCd.le hCp.le hC4.le
    hl hD4 hY hH2 hlogH hlogHH hlogQ
  · intro nu
    exact hA x l m k H nu hxlarge (by linarith) (by omega)
  · intro nu
    simpa only [lemma6MollifierSecondMajorant, mul_assoc] using
      hmol x l H nu (by linarith)
  · intro nu
    simpa only [lemma6DerivativeFourthMajorant, mul_assoc] using
      hxder l nu hl
  · intro nu
    simpa only [lemma6PairFourthMajorant, mul_assoc] using
      hpair x l m k (lemma6BetaPoint x nu) (by linarith)
  · intro nu
    simpa only [mul_assoc] using hpairScale x l m k nu hxlog hl hD4 hY

theorem eventually_shifted_sum_largeConductor_pairTerm_le_scalar_majorant
    (hfourth : Lemma6DerivativeFourthMoment) (h : ℕ) (ε : ℝ) :
    ∃ Cpair CremP CremT Cp Cm Cd : ℝ,
      0 < Cpair ∧ 0 < CremP ∧ 0 < CremT ∧
      0 < Cp ∧ 0 < Cm ∧ 0 < Cd ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ (m l k H : ℕ),
          1 ≤ l → 4 ≤ lemma6DyadicModulusScale x l →
          2 ≤ lemma6PairDyadicScale x k → 2 ≤ H →
          1 ≤ Real.log (H : ℝ) →
          Real.log ((2 * H * H : ℕ) : ℝ) ≤ 8 * Real.log (x : ℝ) →
          Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
            2 * Real.log (x : ℝ) →
          (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
              (fun d => d ∈ lemma6ModulusBlock x l),
            shiftedLemma6NmPairTerm h x m d k) ≤
            lemma6LargePairBlockMajorant x l k H
              Cpair CremP CremT Cp Cm Cd := by
  rcases lemma6_equation19_A_with_large_sieve_moments with
    ⟨Cpair, CremP, CremT, hCpair, hCremP, hCremT, hA⟩
  rcases lemma6_pair_second_moment_characterBlock with ⟨Cp, hCp, hpair⟩
  rcases lemma6_mollifier_fourth_moment_characterBlock with ⟨Cm, hCm, hmol⟩
  rcases lemma6_deriv_fourth_moment_characterBlock_of hfourth with
    ⟨Cd, hCd, hder⟩
  refine ⟨Cpair, CremP, CremT, Cp, Cm, Cd,
    hCpair, hCremP, hCremT, hCp, hCm, hCd, ?_⟩
  filter_upwards [hder, eventually_exp_exp_one_le_log_pow_hundred,
    eventually_three_le_log_nat, eventually_ge_atTop 2] with
      x hxder hxlarge hxlog hx2
  intro m l k H hl hD4 hY hH2 hlogH hlogHH hlogQ
  apply shifted_sum_largeConductor_pairTerm_le_scalar_majorant
    (h := h) hx2 hxlarge hxlog ε m l k H
    hCpair.le hCremP hCremT hCp.le hCm.le hCd.le
    hl hD4 hY hH2 hlogH hlogHH hlogQ
  · intro nu
    exact hA x l m k H nu hxlarge (by linarith) (by omega)
  · intro nu
    simpa only [lemma6PairSecondMajorant, mul_assoc] using
      hpair x l m k (lemma6BetaPoint x nu) (by linarith)
  · intro nu
    simpa only [lemma6MollifierFourthMajorant, mul_assoc] using
      hmol x l H nu (by linarith) hH2
  · intro nu
    simpa only [lemma6DerivativeFourthMajorant, mul_assoc] using
      hxder l nu hl

theorem eventually_shiftedLemma6ExceptionalFactor_le_of_mem
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      lemma6ExceptionalFactorAt x l ≤ 2 * (x : ℝ) ^ (ε / 32) := by
  have hδ : (0 : ℝ) < ε / 16 := by positivity
  filter_upwards [eventually_lemma6ExceptionalFactorAt_le_rpow hδ,
    eventually_three_le_log_nat, eventually_ge_atTop 1] with
    x hI hxlog hx1
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hD2T := shiftedLemma6_occupied_modulusScale_lt_two_threshold
    (h := h) hlog1 hl
  have hT : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hD : lemma6DyadicModulusScale x l ≤
      2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by linarith
  have hID : lemma6ExceptionalFactorAt x l ≤
      lemma6DyadicModulusScale x l ^ (ε / 16) := hI l
  have h2ε : (2 : ℝ) ^ (ε / 16) ≤ 2 := by
    calc
      (2 : ℝ) ^ (ε / 16) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  calc
    lemma6ExceptionalFactorAt x l ≤
        lemma6DyadicModulusScale x l ^ (ε / 16) := hID
    _ ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 2)) ^ (ε / 16) := by
      exact Real.rpow_le_rpow (lemma6DyadicModulusScale_nonneg x l) hD hδ.le
    _ = (2 : ℝ) ^ (ε / 16) *
        ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ (ε / 16) := by
      exact Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _)
    _ = (2 : ℝ) ^ (ε / 16) *
        (x : ℝ) ^ ((1 : ℝ) / 2 * (ε / 16)) := by
      rw [← Real.rpow_mul hx0.le]
    _ ≤ 2 * (x : ℝ) ^ (ε / 32) := by
      apply mul_le_mul h2ε _ (Real.rpow_nonneg hx0.le _) (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hx1'
      linarith

theorem eventually_shiftedLemma6Equation19HCutoff_le_sq
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      (lemma6Equation19HCutoff x l : ℝ) ≤ (x : ℝ) ^ 2 := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 16 := by norm_num
  have hab : (9 : ℝ) / 16 + ε / 32 < 7 / 8 := by linarith
  filter_upwards [eventually_shiftedLemma6ExceptionalFactor_le_of_mem h hε hε',
    eventually_three_le_log_nat,
    eventually_log_pow_nat_le_rpow 100 hδ,
    eventually_const_mul_rpow_le_rpow 4 hab,
    eventually_ge_atTop 2] with x hI hxlog hlogpow hpow hx2
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hD2T := shiftedLemma6_occupied_modulusScale_lt_two_threshold
    (h := h) hlog1 hl
  have hT : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hD : lemma6DyadicModulusScale x l ≤
      2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by linarith
  have hIl : lemma6ExceptionalFactorAt x l ≤
      2 * (x : ℝ) ^ (ε / 32) := hI l hl
  have hI0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  have hscale : lemma6Equation19HScale x l ≤ (x : ℝ) ^ (7 / 8 : ℝ) := by
    have h1 : lemma6Equation19HScale x l ≤
        4 * ((Real.log (x : ℝ)) ^ 100 *
          (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := by
      unfold lemma6Equation19HScale
      have e1 : lemma6DyadicModulusScale x l * (Real.log x) ^ 100 *
            lemma6ExceptionalFactorAt x l ≤
          (2 * (x : ℝ) ^ ((1 : ℝ) / 2)) * (Real.log x) ^ 100 *
            (2 * (x : ℝ) ^ (ε / 32)) := by
        apply mul_le_mul _ hIl hI0 (by positivity)
        exact mul_le_mul_of_nonneg_right hD (by positivity)
      calc
        lemma6DyadicModulusScale x l * (Real.log x) ^ 100 *
              lemma6ExceptionalFactorAt x l ≤
            (2 * (x : ℝ) ^ ((1 : ℝ) / 2)) * (Real.log x) ^ 100 *
              (2 * (x : ℝ) ^ (ε / 32)) := e1
        _ = 4 * ((Real.log x) ^ 100 *
              ((x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ (ε / 32))) := by ring
        _ = 4 * ((Real.log (x : ℝ)) ^ 100 *
              (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := by
          rw [← Real.rpow_add hx0]
    calc
      lemma6Equation19HScale x l ≤
          4 * ((Real.log (x : ℝ)) ^ 100 *
            (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := h1
      _ ≤ 4 * ((x : ℝ) ^ ((1 : ℝ) / 16) *
            (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hlogpow (Real.rpow_nonneg hx0.le _)
      _ = 4 * (x : ℝ) ^ (9 / 16 + ε / 32 : ℝ) := by
        rw [← Real.rpow_add hx0]
        congr 1
        congr 1
        ring
      _ ≤ (x : ℝ) ^ (7 / 8 : ℝ) := hpow
  calc
    (lemma6Equation19HCutoff x l : ℝ) ≤ lemma6Equation19HScale x l + 1 :=
      (lemma6Equation19HCutoff_cast_lt_scale_add_one x l).le
    _ ≤ (x : ℝ) ^ (7 / 8 : ℝ) + 1 := by linarith [hscale]
    _ ≤ (x : ℝ) ^ 2 := by
      have h2 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
      have h78 : (0 : ℝ) ≤ (x : ℝ) ^ (7 / 8 : ℝ) :=
        Real.rpow_nonneg hx0.le _
      have h9 : (2 : ℝ) ≤ (x : ℝ) ^ (9 / 8 : ℝ) := by
        calc
          (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ (2 : ℝ) ^ (9 / 8 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ ≤ (x : ℝ) ^ (9 / 8 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
      have hprod : (x : ℝ) ^ (9 / 8 : ℝ) *
          (x : ℝ) ^ (7 / 8 : ℝ) = (x : ℝ) ^ 2 := by
        rw [← Real.rpow_add hx0,
          show (9 : ℝ) / 8 + 7 / 8 = 2 by norm_num, Real.rpow_two]
      have h22 : (2 : ℝ) ≤ (x : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right h2
          (show (0 : ℝ) ≤ (x : ℝ) by linarith)]
      nlinarith [h9, h78, hprod, h22]

theorem eventually_shiftedLemma6Equation20HCutoff_le_sq
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ, (lemma6Equation20HCutoff x l k ε : ℝ) ≤ (x : ℝ) ^ 2 := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 60 := by norm_num
  have hab : (7 : ℝ) / 12 - 63 * ε / 32 < 3 / 4 := by linarith
  filter_upwards [eventually_shiftedLemma6ExceptionalFactor_le_of_mem h hε hε',
    eventually_three_le_log_nat,
    eventually_log_pow_nat_le_rpow 200 hδ,
    eventually_const_mul_rpow_le_rpow 8 hab,
    eventually_ge_atTop 2] with x hI hxlog hlogpow hpow hx2
  intro l hl k
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hD2T := shiftedLemma6_occupied_modulusScale_lt_two_threshold
    (h := h) hlog1 hl
  have hDsq : lemma6DyadicModulusScale x l ^ 2 ≤
      4 * (x : ℝ) ^ (1 - 2 * ε : ℝ) := by
    have h2 : lemma6DyadicModulusScale x l ^ 2 ≤
        (2 * (x : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^ 2 :=
      pow_le_pow_left₀ (lemma6DyadicModulusScale_nonneg x l) hD2T.le 2
    have h3 : (2 * (x : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^ 2 =
        4 * (x : ℝ) ^ (1 - 2 * ε : ℝ) := by
      rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num]
      congr 1
      rw [← Real.rpow_two, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    exact h2.trans_eq h3
  have hIl : lemma6ExceptionalFactorAt x l ≤
      2 * (x : ℝ) ^ (ε / 32) := hI l hl
  have hI0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  have hlog2000 : 0 ≤ Real.log (x : ℝ) ^ 200 := by positivity
  have hY : (x : ℝ) ^ ((13 : ℝ) / 30) ≤ lemma6PairDyadicScale x k :=
    lemma6_rpow_thirteen_thirty_le_pairScale x k
  have hYpos : 0 < lemma6PairDyadicScale x k :=
    (Real.rpow_pos_of_pos hx0 _).trans_le hY
  have hF : lemma6Equation20HFirstScale x l k ≤
      8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) := by
    have e1 : lemma6Equation20HFirstScale x l k =
        (lemma6DyadicModulusScale x l ^ 2 * (Real.log x) ^ 200 *
            lemma6ExceptionalFactorAt x l) /
          lemma6PairDyadicScale x k := by
      unfold lemma6Equation20HFirstScale
      ring
    rw [e1, div_le_iff₀ hYpos]
    have e2 : lemma6DyadicModulusScale x l ^ 2 * (Real.log x) ^ 200 *
          lemma6ExceptionalFactorAt x l ≤
        (4 * (x : ℝ) ^ (1 - 2 * ε : ℝ)) *
          (x : ℝ) ^ ((1 : ℝ) / 60) *
          (2 * (x : ℝ) ^ (ε / 32)) := by
      apply mul_le_mul _ hIl hI0 (by positivity)
      exact mul_le_mul hDsq hlogpow hlog2000 (by positivity)
    have hexp : (1 : ℝ) - 2 * ε + 1 / 60 + ε / 32 =
        (7 / 12 - 63 * ε / 32) + 13 / 30 := by ring
    calc
      lemma6DyadicModulusScale x l ^ 2 * (Real.log x) ^ 200 *
            lemma6ExceptionalFactorAt x l ≤
          (4 * (x : ℝ) ^ (1 - 2 * ε : ℝ)) *
            (x : ℝ) ^ ((1 : ℝ) / 60) *
            (2 * (x : ℝ) ^ (ε / 32)) := e2
      _ = 8 * ((x : ℝ) ^ (1 - 2 * ε : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 60) * (x : ℝ) ^ (ε / 32)) := by ring
      _ = 8 * (x : ℝ) ^ ((1 - 2 * ε) + 1 / 60 + ε / 32 : ℝ) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ = 8 * ((x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) *
            (x : ℝ) ^ ((13 : ℝ) / 30)) := by
        rw [hexp, Real.rpow_add hx0]
      _ ≤ 8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) *
            lemma6PairDyadicScale x k := by
        calc
          8 * ((x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) *
                (x : ℝ) ^ ((13 : ℝ) / 30)) =
              (8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ)) *
                (x : ℝ) ^ ((13 : ℝ) / 30) := by ring
          _ ≤ (8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ)) *
                lemma6PairDyadicScale x k :=
            mul_le_mul_of_nonneg_left hY (by positivity)
  have hT2 : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hscale : lemma6Equation20HScale x l k ε ≤ (x : ℝ) ^ (3 / 4 : ℝ) := by
    have hF' : lemma6Equation20HFirstScale x l k ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
      hF.trans hpow
    unfold lemma6Equation20HScale
    exact max_le hF' hT2
  have h34 : (x : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have h340 : (0 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg hx0.le _
    have h5 : (2 : ℝ) ≤ (x : ℝ) ^ (5 / 4 : ℝ) := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ (5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ (x : ℝ) ^ (5 / 4 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
    have hprod : (x : ℝ) ^ (5 / 4 : ℝ) *
        (x : ℝ) ^ (3 / 4 : ℝ) = (x : ℝ) ^ 2 := by
      rw [← Real.rpow_add hx0,
        show (5 : ℝ) / 4 + 3 / 4 = 2 by norm_num, Real.rpow_two]
    have h22 : (2 : ℝ) ≤ (x : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h2
        (show (0 : ℝ) ≤ (x : ℝ) by linarith)]
    nlinarith [h5, h340, hprod, h22]
  calc
    (lemma6Equation20HCutoff x l k ε : ℝ) ≤
        lemma6Equation20HScale x l k ε + 1 :=
      (lemma6Equation20HCutoff_cast_lt_scale_add_one x l k ε).le
    _ ≤ (x : ℝ) ^ (3 / 4 : ℝ) + 1 := by linarith [hscale]
    _ ≤ (x : ℝ) ^ 2 := h34

theorem eventually_shifted_log_two_mul_H19sq_le
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      Real.log ((2 * lemma6Equation19HCutoff x l *
          lemma6Equation19HCutoff x l : ℕ) : ℝ) ≤
        8 * Real.log (x : ℝ) := by
  filter_upwards [eventually_shiftedLemma6Equation19HCutoff_le_sq h hε hε',
    eventually_three_le_log_nat, eventually_ge_atTop 2] with
    x hH hxlog hx2
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hHl := hH l hl
  have hH1 : (1 : ℝ) ≤ (lemma6Equation19HCutoff x l : ℝ) := by
    have hle := lemma6Equation19HScale_le_cutoff x l
    have hD := shiftedLemma6_fiftyfour_le_dyadicScale
      (h := h) hxlog hl
    have hI1 := one_le_lemma6ExceptionalFactorAt (x := x) (l := l) hxlog
    have hInn : (0 : ℝ) ≤ lemma6ExceptionalFactorAt x l := by linarith
    have hDnn : (0 : ℝ) ≤ lemma6DyadicModulusScale x l := by linarith
    have hp : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 :=
      one_le_pow₀ (by linarith)
    have h1 : (1 : ℝ) ≤ lemma6Equation19HScale x l := by
      unfold lemma6Equation19HScale
      calc
        (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 100 *
              lemma6ExceptionalFactorAt x l :=
          mul_le_mul (mul_le_mul (by linarith) hp (by positivity) (by linarith))
            hI1 (by linarith) (by positivity)
    linarith
  have hcast : ((2 * lemma6Equation19HCutoff x l *
        lemma6Equation19HCutoff x l : ℕ) : ℝ) =
      2 * (lemma6Equation19HCutoff x l : ℝ) ^ 2 := by
    push_cast
    ring
  have hle : ((2 * lemma6Equation19HCutoff x l *
        lemma6Equation19HCutoff x l : ℕ) : ℝ) ≤ (x : ℝ) ^ 5 := by
    rw [hcast]
    have h1 : (lemma6Equation19HCutoff x l : ℝ) ^ 2 ≤
        ((x : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hHl 2
    have h2 : ((x : ℝ) ^ 2) ^ 2 = (x : ℝ) ^ 4 := by ring
    have h3 : (x : ℝ) ^ 4 ≤ (x : ℝ) ^ 5 :=
      pow_le_pow_right₀
        (by exact_mod_cast (show (1 : ℕ) ≤ x by omega) : (1 : ℝ) ≤ x)
        (by norm_num)
    have h4 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have h5 : (0 : ℝ) < (x : ℝ) ^ 4 := by positivity
    nlinarith [h1, h2, h3, h4, h5]
  have hpos : (0 : ℝ) < (2 * lemma6Equation19HCutoff x l *
      lemma6Equation19HCutoff x l : ℕ) := by
    have hH1n : 1 ≤ lemma6Equation19HCutoff x l := by exact_mod_cast hH1
    exact_mod_cast (mul_pos
      (by omega : (0 : ℕ) < 2 * lemma6Equation19HCutoff x l) (by omega))
  calc
    Real.log ((2 * lemma6Equation19HCutoff x l *
          lemma6Equation19HCutoff x l : ℕ) : ℝ) ≤
        Real.log ((x : ℝ) ^ 5) := Real.log_le_log hpos hle
    _ = 5 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_cast
    _ ≤ 8 * Real.log (x : ℝ) := by linarith

theorem eventually_shifted_log_two_mul_H20sq_le
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      Real.log ((2 * lemma6Equation20HCutoff x l k ε *
          lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) ≤
        8 * Real.log (x : ℝ) := by
  filter_upwards [eventually_shiftedLemma6Equation20HCutoff_le_sq h hε hε',
    eventually_three_le_log_nat, eventually_ge_atTop 2] with
    x hH hxlog hx2
  intro l hl k
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hHl := hH l hl k
  have hH1 : (1 : ℝ) ≤ (lemma6Equation20HCutoff x l k ε : ℝ) := by
    have hle := lemma6Equation20HScale_le_cutoff x l k ε
    have hT : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
      apply Real.one_le_rpow
        (by exact_mod_cast (show (1 : ℕ) ≤ x by omega) : (1 : ℝ) ≤ x)
      linarith
    have hle2 := lemma6_threshold_le_Equation20HScale x l k ε
    linarith
  have hcast : ((2 * lemma6Equation20HCutoff x l k ε *
        lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) =
      2 * (lemma6Equation20HCutoff x l k ε : ℝ) ^ 2 := by
    push_cast
    ring
  have hle : ((2 * lemma6Equation20HCutoff x l k ε *
        lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) ≤ (x : ℝ) ^ 5 := by
    rw [hcast]
    have h1 : (lemma6Equation20HCutoff x l k ε : ℝ) ^ 2 ≤
        ((x : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hHl 2
    have h2 : ((x : ℝ) ^ 2) ^ 2 = (x : ℝ) ^ 4 := by ring
    have h3 : (x : ℝ) ^ 4 ≤ (x : ℝ) ^ 5 :=
      pow_le_pow_right₀
        (by exact_mod_cast (show (1 : ℕ) ≤ x by omega) : (1 : ℝ) ≤ x)
        (by norm_num)
    have h4 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have h5 : (0 : ℝ) < (x : ℝ) ^ 4 := by positivity
    nlinarith [h1, h2, h3, h4, h5]
  have hpos : (0 : ℝ) < (2 * lemma6Equation20HCutoff x l k ε *
      lemma6Equation20HCutoff x l k ε : ℕ) := by
    have hH1n : 1 ≤ lemma6Equation20HCutoff x l k ε := by exact_mod_cast hH1
    exact_mod_cast (mul_pos
      (by omega : (0 : ℕ) < 2 * lemma6Equation20HCutoff x l k ε) (by omega))
  calc
    Real.log ((2 * lemma6Equation20HCutoff x l k ε *
          lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) ≤
        Real.log ((x : ℝ) ^ 5) := Real.log_le_log hpos hle
    _ = 5 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_cast
    _ ≤ 8 * Real.log (x : ℝ) := by linarith

theorem eventually_shifted_log_two_mul_modulusCutoff_le
    (h : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
        2 * Real.log (x : ℝ) := by
  filter_upwards [eventually_three_le_log_nat, eventually_ge_atTop 25] with
    x hxlog hx25
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hD2T := shiftedLemma6_occupied_modulusScale_lt_two_threshold
    (h := h) hlog1 hl
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hT : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hD : lemma6DyadicModulusScale x l ≤
      2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by linarith
  have hQ := lemma6DyadicModulusScale_le_modulusCutoff x l
  have hQ2 : (lemma6ModulusCutoff x l : ℝ) ≤
      lemma6DyadicModulusScale x l + 1 :=
    (lemma6ModulusCutoff_cast_lt_scale_add_one x l).le
  have hx25' : (25 : ℝ) ≤ x := by exact_mod_cast hx25
  have h5 : (5 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ 2 := by
    have hsq : ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = x := by
      have h1 : ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 =
          (x : ℝ) ^ (((1 : ℝ) / 2) * 2) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hx0.le]
      rw [h1, show ((1 : ℝ) / 2) * 2 = 1 by norm_num, Real.rpow_one]
    have h1 : (5 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      have h2 : (25 : ℝ) ≤ ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [hsq]
        exact hx25'
      have h3 : (5 : ℝ) ^ 2 ≤ ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [show (5 : ℝ) ^ 2 = 25 by ring]
        exact h2
      exact le_of_pow_le_pow_left₀ (by norm_num)
        (Real.rpow_nonneg hx0.le _) h3
    calc
      (5 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2) ≤
          (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)
      _ = ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by ring
      _ = x := hsq
      _ ≤ (x : ℝ) ^ 2 := by
        nth_rw 1 [← Real.rpow_one (x : ℝ)]
        rw [← Real.rpow_natCast (x : ℝ) 2]
        exact Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
  have hle : 2 * (lemma6ModulusCutoff x l : ℝ) ≤ (x : ℝ) ^ 2 := by
    nlinarith [hQ2, hD, h5, Real.rpow_nonneg hx0.le ((1 : ℝ) / 2)]
  have hpos : (0 : ℝ) < 2 * (lemma6ModulusCutoff x l : ℝ) := by
    have h54 := shiftedLemma6_fiftyfour_le_dyadicScale
      (h := h) hxlog hl
    linarith [hQ]
  calc
    Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
        Real.log ((x : ℝ) ^ 2) := Real.log_le_log hpos hle
    _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_cast

theorem eventually_shifted_sum_largeConductor_pairTerm_le_H19_scalar20_majorant
    (hfourth : Lemma6DerivativeFourthMoment) (h : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ Cpair CremP CremT Cs Cd Cp C4 : ℝ,
      0 < Cpair ∧ 0 < CremP ∧ 0 < CremT ∧
      0 < Cs ∧ 0 < Cd ∧ 0 < Cp ∧ 0 < C4 ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ m : ℕ, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
          ∀ k ∈ lemma6PairBlockIndices x m,
          (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
              (fun d => d ∈ lemma6ModulusBlock x l),
            shiftedLemma6NmPairTerm h x m d k) ≤
            lemma6LargePairBlock20Majorant x l k
              (lemma6Equation19HCutoff x l)
              Cpair CremP CremT Cs Cd Cp C4 := by
  rcases eventually_shifted_sum_largeConductor_pairTerm_le_scalar20_majorant
      hfourth h ε with
    ⟨Cpair, CremP, CremT, Cs, Cd, Cp, C4,
      hCpair, hCremP, hCremT, hCs, hCd, hCp, hC4, hbound⟩
  refine ⟨Cpair, CremP, CremT, Cs, Cd, Cp, C4,
    hCpair, hCremP, hCremT, hCs, hCd, hCp, hC4, ?_⟩
  filter_upwards [hbound, eventually_three_le_log_nat,
    eventually_shifted_log_two_mul_H19sq_le h hε hε',
    eventually_shifted_log_two_mul_modulusCutoff_le h hε.le,
    eventually_two_le_rpow_thirteen_thirty] with
      x hxbound hxlog hlogHH hlogQ hYbase
  intro m l hl k hk
  have hl1 := shiftedLemma6_one_le_of_mem_largeBlockIndices
    (h := h) (by linarith) hl
  have hD54 := shiftedLemma6_fiftyfour_le_dyadicScale
    (h := h) hxlog hl
  have hD4 : 4 ≤ lemma6DyadicModulusScale x l := by linarith
  have hY : 2 ≤ lemma6PairDyadicScale x k :=
    hYbase.trans (lemma6_rpow_thirteen_thirty_le_pairScale x k)
  let H := lemma6Equation19HCutoff x l
  have hI1 := one_le_lemma6ExceptionalFactorAt (x := x) (l := l) hxlog
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 := one_le_pow₀ (by linarith)
  have hD0 : (0 : ℝ) ≤ lemma6DyadicModulusScale x l := by linarith
  have h54scale : (54 : ℝ) ≤ lemma6Equation19HScale x l := by
    unfold lemma6Equation19HScale
    calc
      (54 : ℝ) = 54 * 1 * 1 := by ring
      _ ≤ lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 100 *
          lemma6ExceptionalFactorAt x l :=
        mul_le_mul
          (mul_le_mul (by exact_mod_cast hD54) hL1 (by norm_num) hD0)
          hI1 (by norm_num) (mul_nonneg hD0 (by positivity))
  have hH54real : (54 : ℝ) ≤ (H : ℝ) :=
    h54scale.trans (lemma6Equation19HScale_le_cutoff x l)
  have hH54 : 54 ≤ H := by exact_mod_cast hH54real
  have hH2 : 2 ≤ H := by omega
  have hlogH : 1 ≤ Real.log (H : ℝ) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have h3H : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (show 3 ≤ H by omega)
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  exact hxbound m l k H hl1 hD4 hY hH2 hlogH
    (hlogHH l hl) (hlogQ l hl)

theorem eventually_shifted_sum_largeConductor_pairTerm_le_H20_scalar20_majorant
    (hfourth : Lemma6DerivativeFourthMoment) (h : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ Cpair CremP CremT Cs Cd Cp C4 : ℝ,
      0 < Cpair ∧ 0 < CremP ∧ 0 < CremT ∧
      0 < Cs ∧ 0 < Cd ∧ 0 < Cp ∧ 0 < C4 ∧
      ∀ᶠ x : ℕ in atTop,
        ∀ m : ℕ, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
          ∀ k ∈ lemma6PairBlockIndices x m,
            lemma6PairDyadicScale x k ≤ lemma6DyadicModulusScale x l →
            (∑ d ∈ (shiftedLemma6LargeSquarefreeConductors h x ε).filter
                (fun d => d ∈ lemma6ModulusBlock x l),
              shiftedLemma6NmPairTerm h x m d k) ≤
              lemma6LargePairBlock20Majorant x l k
                (lemma6Equation20HCutoff x l k ε)
                Cpair CremP CremT Cs Cd Cp C4 := by
  rcases eventually_shifted_sum_largeConductor_pairTerm_le_scalar20_majorant
      hfourth h ε with
    ⟨Cpair, CremP, CremT, Cs, Cd, Cp, C4,
      hCpair, hCremP, hCremT, hCs, hCd, hCp, hC4, hbound⟩
  refine ⟨Cpair, CremP, CremT, Cs, Cd, Cp, C4,
    hCpair, hCremP, hCremT, hCs, hCd, hCp, hC4, ?_⟩
  filter_upwards [hbound, eventually_three_le_log_nat,
    eventually_shifted_log_two_mul_H20sq_le h hε hε',
    eventually_shifted_log_two_mul_modulusCutoff_le h hε.le,
    eventually_two_le_rpow_thirteen_thirty] with
      x hxbound hxlog hlogHH hlogQ hYbase
  intro m l hl k hk hYD
  have hl1 := shiftedLemma6_one_le_of_mem_largeBlockIndices
    (h := h) (by linarith) hl
  have hD54 := shiftedLemma6_fiftyfour_le_dyadicScale
    (h := h) hxlog hl
  have hD4 : 4 ≤ lemma6DyadicModulusScale x l := by linarith
  have hD0 : (0 : ℝ) ≤ lemma6DyadicModulusScale x l := by linarith
  have hY : 2 ≤ lemma6PairDyadicScale x k :=
    hYbase.trans (lemma6_rpow_thirteen_thirty_le_pairScale x k)
  have hYpos : 0 < lemma6PairDyadicScale x k := by linarith
  let H := lemma6Equation20HCutoff x l k ε
  have hI1 := one_le_lemma6ExceptionalFactorAt (x := x) (l := l) hxlog
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 200 := one_le_pow₀ (by linarith)
  have hDdiv : lemma6DyadicModulusScale x l ≤
      lemma6DyadicModulusScale x l ^ 2 / lemma6PairDyadicScale x k := by
    rw [le_div_iff₀ hYpos]
    nlinarith
  have h54first : (54 : ℝ) ≤ lemma6Equation20HFirstScale x l k := by
    unfold lemma6Equation20HFirstScale
    calc
      (54 : ℝ) ≤ lemma6DyadicModulusScale x l := by exact_mod_cast hD54
      _ = lemma6DyadicModulusScale x l * 1 * 1 := by ring
      _ ≤ (lemma6DyadicModulusScale x l ^ 2 /
              lemma6PairDyadicScale x k) * Real.log (x : ℝ) ^ 200 *
            lemma6ExceptionalFactorAt x l :=
        mul_le_mul
          (mul_le_mul hDdiv hL1 (by norm_num) (by positivity))
          hI1 (by norm_num) (by positivity)
  have hH54real : (54 : ℝ) ≤ (H : ℝ) :=
    h54first.trans ((lemma6Equation20HFirstScale_le_HScale x l k ε).trans
      (lemma6Equation20HScale_le_cutoff x l k ε))
  have hH54 : 54 ≤ H := by exact_mod_cast hH54real
  have hH2 : 2 ≤ H := by omega
  have hlogH : 1 ≤ Real.log (H : ℝ) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have h3H : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (show 3 ≤ H by omega)
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  exact hxbound m l k H hl1 hD4 hY hH2 hlogH
    (hlogHH l hl k) (hlogQ l hl)

theorem eventually_shifted_exceptionalFactor_mul_log100_le_pairScale
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 100 ≤
        lemma6PairDyadicScale x k := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 16 := by norm_num
  have hab : (1 : ℝ) / 16 + ε / 32 < 13 / 30 := by linarith
  filter_upwards [eventually_shiftedLemma6ExceptionalFactor_le_of_mem h hε hε',
    eventually_log_pow_nat_le_rpow 100 hδ,
    eventually_const_mul_rpow_le_rpow 2 hab,
    eventually_ge_atTop 1] with x hI hlogpow hpow hx1
  intro l hl k
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hIl := hI l hl
  have hlog0 : 0 ≤ Real.log (x : ℝ) ^ 100 := by positivity
  calc
    lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 100 ≤
        (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) :=
      mul_le_mul hIl hlogpow hlog0 (by positivity)
    _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 16 + ε / 32 : ℝ) := by
      rw [show (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) =
          2 * ((x : ℝ) ^ (ε / 32) * (x : ℝ) ^ ((1 : ℝ) / 16)) by ring]
      rw [← Real.rpow_add hx0]
      congr 1
      congr 1
      ring
    _ ≤ (x : ℝ) ^ ((13 : ℝ) / 30) := hpow
    _ ≤ lemma6PairDyadicScale x k :=
      lemma6_rpow_thirteen_thirty_le_pairScale x k

theorem eventually_shifted_exceptionalFactor_mul_log100_le_threshold
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 100 ≤
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 16 := by norm_num
  have hab : (1 : ℝ) / 16 + ε / 32 < (1 : ℝ) / 2 - ε := by linarith
  filter_upwards [eventually_shiftedLemma6ExceptionalFactor_le_of_mem h hε hε',
    eventually_log_pow_nat_le_rpow 100 hδ,
    eventually_const_mul_rpow_le_rpow 2 hab,
    eventually_ge_atTop 1] with x hI hlogpow hpow hx1
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hIl := hI l hl
  have hlog0 : 0 ≤ Real.log (x : ℝ) ^ 100 := by positivity
  calc
    lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 100 ≤
        (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) :=
      mul_le_mul hIl hlogpow hlog0 (by positivity)
    _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 16 + ε / 32 : ℝ) := by
      rw [show (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) =
          2 * ((x : ℝ) ^ (ε / 32) * (x : ℝ) ^ ((1 : ℝ) / 16)) by ring]
      rw [← Real.rpow_add hx0]
      congr 1
      congr 1
      ring
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hpow

theorem eventually_shifted_log200_mul_exceptionalFactor_le_pairScale
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      Real.log (x : ℝ) ^ 200 * lemma6ExceptionalFactorAt x l ≤
        lemma6PairDyadicScale x k := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 60 := by norm_num
  have hab : (1 : ℝ) / 60 + ε / 32 < 13 / 30 := by linarith
  filter_upwards [eventually_shiftedLemma6ExceptionalFactor_le_of_mem h hε hε',
    eventually_log_pow_nat_le_rpow 200 hδ,
    eventually_const_mul_rpow_le_rpow 2 hab,
    eventually_ge_atTop 1] with x hI hlogpow hpow hx1
  intro l hl k
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hIl := hI l hl
  calc
    Real.log (x : ℝ) ^ 200 * lemma6ExceptionalFactorAt x l ≤
        (x : ℝ) ^ ((1 : ℝ) / 60) * (2 * (x : ℝ) ^ (ε / 32)) :=
      mul_le_mul hlogpow hIl (lemma6ExceptionalFactor_pos _).le
        (Real.rpow_nonneg hx0.le _)
    _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 60 + ε / 32 : ℝ) := by
      rw [show (x : ℝ) ^ ((1 : ℝ) / 60) * (2 * (x : ℝ) ^ (ε / 32)) =
          2 * ((x : ℝ) ^ ((1 : ℝ) / 60) * (x : ℝ) ^ (ε / 32)) by ring]
      rw [← Real.rpow_add hx0]
    _ ≤ (x : ℝ) ^ ((13 : ℝ) / 30) := hpow
    _ ≤ lemma6PairDyadicScale x k :=
      lemma6_rpow_thirteen_thirty_le_pairScale x k

theorem eventually_shifted_exceptionalFactor_mul_log80_le_dyadicScale
    (h : ℕ) (ε : ℝ) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 80 ≤
        lemma6DyadicModulusScale x l := by
  filter_upwards [eventually_lemma6ExceptionalFactorAt_le_rpow
      (show (0 : ℝ) < 1 / 10 by norm_num),
    eventually_three_le_log_nat] with x hI hxlog
  intro l hl
  let D := lemma6DyadicModulusScale x l
  let L := Real.log (x : ℝ)
  have hD1 : (1 : ℝ) ≤ D := by
    dsimp only [D]
    linarith [shiftedLemma6_fiftyfour_le_dyadicScale
      (h := h) hxlog hl]
  have hDpos : (0 : ℝ) < D := zero_lt_one.trans_le hD1
  have hLpos : (0 : ℝ) < L := by dsimp only [L]; linarith
  have hL100 : L ^ 100 ≤ D := by
    dsimp only [L, D]
    exact (shiftedLemma6_log_pow_hundred_lt_dyadicScale
      (h := h) (by linarith) hl).le
  have hL80 : L ^ 80 ≤ D ^ ((4 : ℝ) / 5) := by
    have hr := Real.rpow_le_rpow (by positivity) hL100
      (by norm_num : (0 : ℝ) ≤ 4 / 5)
    calc
      L ^ 80 = L ^ (80 : ℝ) := (Real.rpow_natCast L 80).symm
      _ = (L ^ (100 : ℝ)) ^ ((4 : ℝ) / 5) := by
        rw [← Real.rpow_mul hLpos.le]
        norm_num
      _ = (L ^ (100 : ℕ)) ^ ((4 : ℝ) / 5) :=
        congrArg (fun z : ℝ => z ^ ((4 : ℝ) / 5))
          (Real.rpow_natCast L 100)
      _ ≤ D ^ ((4 : ℝ) / 5) := hr
  have hprod : lemma6ExceptionalFactorAt x l * L ^ 80 ≤
      D ^ ((1 : ℝ) / 10) * D ^ ((4 : ℝ) / 5) :=
    mul_le_mul (hI l) hL80 (by positivity) (Real.rpow_nonneg hDpos.le _)
  calc
    lemma6ExceptionalFactorAt x l * Real.log (x : ℝ) ^ 80 =
        lemma6ExceptionalFactorAt x l * L ^ 80 := by rfl
    _ ≤ D ^ ((1 : ℝ) / 10) * D ^ ((4 : ℝ) / 5) := hprod
    _ = D ^ ((9 : ℝ) / 10) := by
      rw [← Real.rpow_add hDpos]
      norm_num
    _ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
    _ = lemma6DyadicModulusScale x l := by rw [Real.rpow_one]

theorem eventually_shifted_AIntegralMajorant_H19_le_log32
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100)
    {Cpair CremP CremT : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 ≤ CremP) (hCremT : 0 ≤ CremT) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      lemma6DyadicModulusScale x l ≤ lemma6PairDyadicScale x k →
      lemma6AIntegralMajorant x l k (lemma6Equation19HCutoff x l)
          Cpair CremP CremT ≤
        240 * Real.pi *
          Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) /
            Real.log (x : ℝ) ^ 32 := by
  filter_upwards [eventually_three_le_log_nat,
    eventually_shifted_log_two_mul_H19sq_le h hε hε',
    eventually_shifted_exceptionalFactor_mul_log80_le_dyadicScale h ε] with
      x hxlog hlogHH hEL80
  intro l hl k hDY
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let E := lemma6ExceptionalFactorAt x l
  let H := lemma6Equation19HCutoff x l
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hD54 : 54 ≤ D := by
    dsimp only [D]
    exact shiftedLemma6_fiftyfour_le_dyadicScale (h := h) hxlog hl
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have hE1 : (1 : ℝ) ≤ E := by
    dsimp only [E]
    exact one_le_lemma6ExceptionalFactorAt hxlog
  have hL100 : (1 : ℝ) ≤ L ^ 100 := one_le_pow₀ hL1
  have hscale1 : (1 : ℝ) ≤ lemma6Equation19HScale x l := by
    unfold lemma6Equation19HScale
    change (1 : ℝ) ≤ D * L ^ 100 * E
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ D * L ^ 100 * E :=
        mul_le_mul (mul_le_mul hD1 hL100 (by norm_num) (by linarith))
          hE1 (by norm_num) (by positivity)
  have hH1real : (1 : ℝ) ≤ (H : ℝ) :=
    hscale1.trans (by
      dsimp only [H]
      exact lemma6Equation19HScale_le_cutoff x l)
  have hHpos : (0 : ℝ) < H := zero_lt_one.trans_le hH1real
  have hlogH0 : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hH1real
  have hHleHH : (H : ℝ) ≤ ((2 * H * H : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hlogH : Real.log (H : ℝ) ≤ 8 * L := by
    calc
      Real.log (H : ℝ) ≤ Real.log ((2 * H * H : ℕ) : ℝ) :=
        Real.log_le_log hHpos hHleHH
      _ ≤ 8 * L := by simpa only [H, L] using hlogHH l hl
  have hYpos : 0 < lemma6PairDyadicScale x k :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < D) hDY
  have hcut : E * D * L ^ 100 ≤ (H : ℝ) := by
    calc
      E * D * L ^ 100 = lemma6Equation19HScale x l := by
        dsimp only [E, D, L]
        unfold lemma6Equation19HScale
        ring
      _ ≤ (H : ℝ) := by
        dsimp only [H]
        exact lemma6Equation19HScale_le_cutoff x l
  have hraw := lemma6AIntegralMajorant_le_of_D_le_Y
    hCpair hCremP hCremT hL1 hlogH0 hlogH hD1 hE1 hYpos hDY
    (by simpa only [E, D, L] using hEL80 l hl) hcut
  refine hraw.trans ?_
  have hsaved := log_eight_mul_saved_terms_le hL1
  have hcoef0 : 0 ≤ 80 * Real.pi *
      Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) := by positivity
  calc
    80 * Real.pi * Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
        L ^ 8 * (1 / L ^ 50 + 1 / L ^ 40 + 1 / L ^ 100) ≤
      80 * Real.pi * Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
        (3 / L ^ 32) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsaved hcoef0
    _ = 240 * Real.pi *
        Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) /
          L ^ 32 := by ring

theorem eventually_shifted_equation19_AContribution_le_log20
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100)
    {Cpair CremP CremT : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 ≤ CremP) (hCremT : 0 ≤ CremT) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      lemma6DyadicModulusScale x l ≤ lemma6PairDyadicScale x k →
      (1 / (2 * Real.pi)) *
          (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
            lemma6AIntegralMajorant x l k (lemma6Equation19HCutoff x l)
              Cpair CremP CremT) ≤
        480 * Real.exp 1 *
            Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
          (x : ℝ) / Real.log (x : ℝ) ^ 20 := by
  filter_upwards [eventually_shifted_AIntegralMajorant_H19_le_log32
      h hε hε' hCpair hCremP hCremT,
    eventually_three_le_log_nat] with x hA hxlog
  intro l hl k hDY
  let L := Real.log (x : ℝ)
  let K := Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2))
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have houter0 : 0 ≤ (1 / (2 * Real.pi)) *
      (4 * L ^ 2 * (Real.exp 1 * (x : ℝ))) := by positivity
  have h2030 : L ^ 20 ≤ L ^ 30 := pow_le_pow_right₀ hL1 (by norm_num)
  have hinv : 1 / L ^ 30 ≤ 1 / L ^ 20 :=
    one_div_le_one_div_of_le (pow_pos hLpos 20) h2030
  calc
    (1 / (2 * Real.pi)) *
        (4 * L ^ 2 * (Real.exp 1 * (x : ℝ)) *
          lemma6AIntegralMajorant x l k (lemma6Equation19HCutoff x l)
            Cpair CremP CremT) ≤
      (1 / (2 * Real.pi)) * (4 * L ^ 2 * (Real.exp 1 * (x : ℝ))) *
        (240 * Real.pi * K / L ^ 32) := by
      rw [show (1 / (2 * Real.pi)) *
          (4 * L ^ 2 * (Real.exp 1 * (x : ℝ)) *
            lemma6AIntegralMajorant x l k (lemma6Equation19HCutoff x l)
              Cpair CremP CremT) =
        ((1 / (2 * Real.pi)) * (4 * L ^ 2 * (Real.exp 1 * (x : ℝ)))) *
          lemma6AIntegralMajorant x l k (lemma6Equation19HCutoff x l)
            Cpair CremP CremT by ring]
      apply mul_le_mul_of_nonneg_left _ houter0
      simpa only [K] using hA l hl k hDY
    _ = 480 * Real.exp 1 * K * (x : ℝ) / L ^ 30 := by
      field_simp [Real.pi_ne_zero, hLpos.ne']
      ring
    _ ≤ 480 * Real.exp 1 * K * (x : ℝ) / L ^ 20 := by
      rw [show 480 * Real.exp 1 * K * (x : ℝ) / L ^ 30 =
          (480 * Real.exp 1 * K * (x : ℝ)) * (1 / L ^ 30) by ring,
        show 480 * Real.exp 1 * K * (x : ℝ) / L ^ 20 =
          (480 * Real.exp 1 * K * (x : ℝ)) * (1 / L ^ 20) by ring]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)

theorem eventually_shifted_AIntegralMajorant_H20_le_log92
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100)
    {Cpair CremP CremT : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 ≤ CremP) (hCremT : 0 ≤ CremT) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      lemma6PairDyadicScale x k ≤ lemma6DyadicModulusScale x l →
      lemma6AIntegralMajorant x l k (lemma6Equation20HCutoff x l k ε)
          Cpair CremP CremT ≤
        240 * Real.pi *
          Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) /
            Real.log (x : ℝ) ^ 92 := by
  filter_upwards [eventually_three_le_log_nat,
    eventually_shifted_log_two_mul_H20sq_le h hε hε',
    eventually_shifted_log200_mul_exceptionalFactor_le_pairScale h hε hε',
    eventually_two_le_rpow_thirteen_thirty,
    eventually_ge_atTop 1] with x hxlog hlogHH hEL200 hYbase hx1
  intro l hl k hYD
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  let E := lemma6ExceptionalFactorAt x l
  let H := lemma6Equation20HCutoff x l k ε
  have hx1real : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hL1 : (1 : ℝ) ≤ L := by dsimp only [L]; linarith
  have hD1 : (1 : ℝ) ≤ D := by
    dsimp only [D]
    linarith [shiftedLemma6_fiftyfour_le_dyadicScale (h := h) hxlog hl]
  have hE1 : (1 : ℝ) ≤ E := by
    dsimp only [E]
    exact one_le_lemma6ExceptionalFactorAt hxlog
  have hYpos : 0 < Y := by
    dsimp only [Y]
    linarith [hYbase.trans (lemma6_rpow_thirteen_thirty_le_pairScale x k)]
  have hT1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
    Real.one_le_rpow hx1real (by linarith)
  have hscale1 : (1 : ℝ) ≤ lemma6Equation20HScale x l k ε :=
    hT1.trans (lemma6_threshold_le_Equation20HScale x l k ε)
  have hH1real : (1 : ℝ) ≤ (H : ℝ) :=
    hscale1.trans (by
      dsimp only [H]
      exact lemma6Equation20HScale_le_cutoff x l k ε)
  have hHpos : (0 : ℝ) < H := zero_lt_one.trans_le hH1real
  have hlogH0 : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hH1real
  have hHleHH : (H : ℝ) ≤ ((2 * H * H : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hlogH : Real.log (H : ℝ) ≤ 8 * L := by
    calc
      Real.log (H : ℝ) ≤ Real.log ((2 * H * H : ℕ) : ℝ) :=
        Real.log_le_log hHpos hHleHH
      _ ≤ 8 * L := by simpa only [H, L] using hlogHH l hl k
  have hcut : E * D ^ 2 * L ^ 200 / Y ≤ (H : ℝ) := by
    calc
      E * D ^ 2 * L ^ 200 / Y = lemma6Equation20HFirstScale x l k := by
        dsimp only [E, D, L, Y]
        unfold lemma6Equation20HFirstScale
        ring
      _ ≤ lemma6Equation20HScale x l k ε :=
        lemma6Equation20HFirstScale_le_HScale x l k ε
      _ ≤ (H : ℝ) := by
        dsimp only [H]
        exact lemma6Equation20HScale_le_cutoff x l k ε
  apply lemma6AIntegralMajorant_le_of_Y_le_D hCpair hCremP hCremT
    hL1 hlogH0 hlogH hD1 hE1 hYpos
  · simpa only [Y, D] using hYD
  · simpa only [E, L, Y, mul_comm] using hEL200 l hl k
  · exact hcut

theorem eventually_shifted_equation20_AContribution_le_log20
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100)
    {Cpair CremP CremT : ℝ}
    (hCpair : 0 ≤ Cpair) (hCremP : 0 ≤ CremP) (hCremT : 0 ≤ CremT) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      lemma6PairDyadicScale x k ≤ lemma6DyadicModulusScale x l →
      (1 / (2 * Real.pi)) *
          (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
            lemma6AIntegralMajorant x l k (lemma6Equation20HCutoff x l k ε)
              Cpair CremP CremT) ≤
        480 * Real.exp 1 *
            Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2)) *
          (x : ℝ) / Real.log (x : ℝ) ^ 20 := by
  filter_upwards [eventually_shifted_AIntegralMajorant_H20_le_log92
      h hε hε' hCpair hCremP hCremT,
    eventually_three_le_log_nat] with x hA hxlog
  intro l hl k hYD
  let L := Real.log (x : ℝ)
  let K := Real.sqrt (Cpair * (36864 * CremP + 200 * CremT ^ 2))
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have houter0 : 0 ≤ (1 / (2 * Real.pi)) *
      (4 * L ^ 2 * (Real.exp 1 * (x : ℝ))) := by positivity
  have h2090 : L ^ 20 ≤ L ^ 90 := pow_le_pow_right₀ hL1 (by norm_num)
  have hinv : 1 / L ^ 90 ≤ 1 / L ^ 20 :=
    one_div_le_one_div_of_le (pow_pos hLpos 20) h2090
  calc
    (1 / (2 * Real.pi)) *
        (4 * L ^ 2 * (Real.exp 1 * (x : ℝ)) *
          lemma6AIntegralMajorant x l k (lemma6Equation20HCutoff x l k ε)
            Cpair CremP CremT) ≤
      (1 / (2 * Real.pi)) * (4 * L ^ 2 * (Real.exp 1 * (x : ℝ))) *
        (240 * Real.pi * K / L ^ 92) := by
      rw [show (1 / (2 * Real.pi)) *
          (4 * L ^ 2 * (Real.exp 1 * (x : ℝ)) *
            lemma6AIntegralMajorant x l k (lemma6Equation20HCutoff x l k ε)
              Cpair CremP CremT) =
        ((1 / (2 * Real.pi)) * (4 * L ^ 2 * (Real.exp 1 * (x : ℝ)))) *
          lemma6AIntegralMajorant x l k (lemma6Equation20HCutoff x l k ε)
            Cpair CremP CremT by ring]
      apply mul_le_mul_of_nonneg_left _ houter0
      simpa only [K] using hA l hl k hYD
    _ = 480 * Real.exp 1 * K * (x : ℝ) / L ^ 90 := by
      field_simp [Real.pi_ne_zero, hLpos.ne']
      ring
    _ ≤ 480 * Real.exp 1 * K * (x : ℝ) / L ^ 20 := by
      rw [show 480 * Real.exp 1 * K * (x : ℝ) / L ^ 90 =
          (480 * Real.exp 1 * K * (x : ℝ)) * (1 / L ^ 90) by ring,
        show 480 * Real.exp 1 * K * (x : ℝ) / L ^ 20 =
          (480 * Real.exp 1 * K * (x : ℝ)) * (1 / L ^ 20) by ring]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)

theorem eventually_shifted_equation19_mollifier_scale_le (h : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ ε : ℝ,
      ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * ((lemma6Equation19HCutoff x l *
            lemma6Equation19HCutoff x l : ℕ) : ℝ) /
              lemma6DyadicModulusScale x l ≤
        18 * lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 200 *
          lemma6ExceptionalFactorAt x l ^ 2 := by
  filter_upwards [eventually_three_le_log_nat] with x hxlog
  intro ε l hl
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let E := lemma6ExceptionalFactorAt x l
  let H := lemma6Equation19HCutoff x l
  have hL1 : (1 : ℝ) ≤ L := by dsimp only [L]; linarith
  have hD1 : (1 : ℝ) ≤ D := by
    dsimp only [D]
    linarith [shiftedLemma6_fiftyfour_le_dyadicScale (h := h) hxlog hl]
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hE1 : (1 : ℝ) ≤ E := by
    dsimp only [E]
    exact one_le_lemma6ExceptionalFactorAt hxlog
  have hL100 : (1 : ℝ) ≤ L ^ 100 := one_le_pow₀ hL1
  have hL200 : (1 : ℝ) ≤ L ^ 200 := one_le_pow₀ hL1
  have hE2 : (1 : ℝ) ≤ E ^ 2 := one_le_pow₀ hE1
  have hscale1 : (1 : ℝ) ≤ lemma6Equation19HScale x l := by
    unfold lemma6Equation19HScale
    change (1 : ℝ) ≤ D * L ^ 100 * E
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ D * L ^ 100 * E :=
        mul_le_mul (mul_le_mul hD1 hL100 (by norm_num) (by positivity))
          hE1 (by norm_num) (by positivity)
  have hHupper : (H : ℝ) ≤ 2 * D * L ^ 100 * E := by
    have hcut := lemma6Equation19HCutoff_cast_le_two_mul_scale hscale1
    dsimp only [H, D, L, E]
    simpa only [lemma6Equation19HScale, mul_assoc] using hcut
  have hHsq : (H : ℝ) ^ 2 ≤ (2 * D * L ^ 100 * E) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hHupper 2
  have hquot : 4 * (H : ℝ) ^ 2 / D ≤ 16 * D * L ^ 200 * E ^ 2 := by
    rw [div_le_iff₀ hDpos]
    calc
      4 * (H : ℝ) ^ 2 ≤ 4 * (2 * D * L ^ 100 * E) ^ 2 :=
        mul_le_mul_of_nonneg_left hHsq (by norm_num)
      _ = (16 * D * L ^ 200 * E ^ 2) * D := by ring
  have hfirst : (5 / 4 : ℝ) * D ≤ 2 * D * L ^ 200 * E ^ 2 := by
    have hprod : (1 : ℝ) ≤ L ^ 200 * E ^ 2 := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ L ^ 200 * E ^ 2 :=
          mul_le_mul hL200 hE2 (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hprod hDpos.le]
  calc
    (5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * ((lemma6Equation19HCutoff x l *
            lemma6Equation19HCutoff x l : ℕ) : ℝ) /
              lemma6DyadicModulusScale x l =
        (5 / 4 : ℝ) * D + 4 * (H : ℝ) ^ 2 / D := by
      dsimp only [D, H]
      push_cast
      ring
    _ ≤ 2 * D * L ^ 200 * E ^ 2 + 16 * D * L ^ 200 * E ^ 2 :=
      add_le_add hfirst hquot
    _ = 18 * lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 200 *
          lemma6ExceptionalFactorAt x l ^ 2 := by
      dsimp only [D, L, E]
      ring

theorem eventually_shifted_equation20_mollifier_scale_mul_D_le
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k : ℕ,
      (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * (lemma6Equation20HCutoff x l k ε : ℝ) /
            lemma6DyadicModulusScale x l) *
        lemma6DyadicModulusScale x l) ≤
      32 * ((x : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^ 2 := by
  filter_upwards [eventually_three_le_log_nat,
    eventually_shifted_log200_mul_exceptionalFactor_le_pairScale h hε hε',
    eventually_two_le_rpow_thirteen_thirty,
    eventually_ge_atTop 1] with x hxlog hEL200 hYbase hx1
  intro l hl k
  let L := Real.log (x : ℝ)
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  let E := lemma6ExceptionalFactorAt x l
  let T := (x : ℝ) ^ ((1 : ℝ) / 2 - ε)
  let F := lemma6Equation20HFirstScale x l k
  let Hs := lemma6Equation20HScale x l k ε
  let H := lemma6Equation20HCutoff x l k ε
  have hx1real : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hDpos : 0 < D := by
    dsimp only [D]
    linarith [shiftedLemma6_fiftyfour_le_dyadicScale (h := h) hxlog hl]
  have hYpos : 0 < Y := by
    dsimp only [Y]
    linarith [hYbase.trans (lemma6_rpow_thirteen_thirty_le_pairScale x k)]
  have hT1 : (1 : ℝ) ≤ T := by
    dsimp only [T]
    exact Real.one_le_rpow hx1real (by linarith)
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hFform : F = D ^ 2 * (L ^ 200 * E / Y) := by
    dsimp only [F, D, L, E, Y]
    unfold lemma6Equation20HFirstScale
    ring
  have hratio : L ^ 200 * E / Y ≤ 1 := by
    apply (div_le_one hYpos).2
    simpa only [L, E, Y] using hEL200 l hl k
  have hFle : F ≤ D ^ 2 := by
    rw [hFform]
    calc
      D ^ 2 * (L ^ 200 * E / Y) ≤ D ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hratio (sq_nonneg D)
      _ = D ^ 2 := by ring
  have hHs : Hs ≤ D ^ 2 + T := by
    dsimp only [Hs]
    unfold lemma6Equation20HScale
    exact max_le_iff.mpr
      ⟨hFle.trans (le_add_of_nonneg_right hTpos.le),
        le_add_of_nonneg_left (sq_nonneg D)⟩
  have hH : (H : ℝ) ≤ D ^ 2 + T + 1 := by
    have hc : (H : ℝ) ≤ Hs + 1 :=
      (lemma6Equation20HCutoff_cast_lt_scale_add_one x l k ε).le
    exact hc.trans (by
      simpa only [add_comm] using add_le_add_right hHs 1)
  have hDlt : D < 2 * T := by
    dsimp only [D, T]
    exact shiftedLemma6_occupied_modulusScale_lt_two_threshold
      (h := h) (by linarith) hl
  have hDsq : D ^ 2 ≤ 4 * T ^ 2 := by nlinarith
  have hTle : T ≤ T ^ 2 := by nlinarith
  have h1le : (1 : ℝ) ≤ T ^ 2 := by nlinarith
  have hH6 : (H : ℝ) ≤ 6 * T ^ 2 := by nlinarith
  calc
    (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
          4 * (lemma6Equation20HCutoff x l k ε : ℝ) /
            lemma6DyadicModulusScale x l) *
        lemma6DyadicModulusScale x l) =
      (5 / 4 : ℝ) * D ^ 2 + 4 * (H : ℝ) := by
        dsimp only [D, H]
        rw [show (((5 / 4 : ℝ) * lemma6DyadicModulusScale x l +
              4 * (lemma6Equation20HCutoff x l k ε : ℝ) /
                lemma6DyadicModulusScale x l) *
              lemma6DyadicModulusScale x l) =
            (5 / 4 : ℝ) * lemma6DyadicModulusScale x l ^ 2 +
              4 * (lemma6Equation20HCutoff x l k ε : ℝ) *
                (lemma6DyadicModulusScale x l /
                  lemma6DyadicModulusScale x l) by ring,
          div_self (by simpa only [D] using hDpos.ne')]
        ring
    _ ≤ (5 / 4 : ℝ) * (4 * T ^ 2) + 4 * (6 * T ^ 2) := by gcongr
    _ ≤ 32 * T ^ 2 := by nlinarith [sq_nonneg T]

theorem eventually_shifted_BIntegralMajorant_H19_le_shape
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100)
    {Cp Cm Cd : ℝ} (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hCd : 0 ≤ Cd) :
    ∀ᶠ x : ℕ in atTop, ∀ m : ℕ,
      ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k ∈ lemma6PairBlockIndices x m,
        lemma6BIntegralMajorant x l k (lemma6Equation19HCutoff x l)
            Cp Cm Cd ≤
          32 * Real.pi * (10368 * Cp ^ 2 * Cm * Cd) ^ ((1 : ℝ) / 4) *
            lemma6ExceptionalFactorAt x l *
            (lemma6DyadicModulusScale x l +
              Real.sqrt (lemma6PairDyadicScale x k)) *
            Real.log (x : ℝ) ^ 60 := by
  filter_upwards [eventually_three_le_log_nat,
    eventually_two_le_rpow_thirteen_thirty,
    eventually_log_pairUpperCutoff_le_log_x,
    eventually_shifted_equation19_mollifier_scale_le h,
    eventually_shifted_log_two_mul_H19sq_le h hε hε'] with
      x hxlog hYbase hlogU hmoll hlogHH
  intro m l hl k hk
  let H := lemma6Equation19HCutoff x l
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hD1 : (1 : ℝ) ≤ lemma6DyadicModulusScale x l := by
    linarith [shiftedLemma6_fiftyfour_le_dyadicScale (h := h) hxlog hl]
  have hY2 : (2 : ℝ) ≤ lemma6PairDyadicScale x k :=
    hYbase.trans (lemma6_rpow_thirteen_thirty_le_pairScale x k)
  have hYpos : 0 < lemma6PairDyadicScale x k := by linarith
  have hU2 : (2 : ℝ) ≤ lemma6PairUpperCutoff x k :=
    hY2.trans (lemma6PairScale_le_pairUpperCutoff x k)
  have hU1 : (1 : ℝ) ≤ lemma6PairUpperCutoff x k := by linarith
  have hlogU0 : 0 ≤ 1 + Real.log (lemma6PairUpperCutoff x k : ℕ) :=
    add_nonneg zero_le_one (Real.log_nonneg hU1)
  have hlogU2 : 1 + Real.log (lemma6PairUpperCutoff x k : ℕ) ≤
      2 * Real.log (x : ℝ) := by
    linarith [hlogU m k hk]
  have hscale1 : (1 : ℝ) ≤ lemma6Equation19HScale x l := by
    unfold lemma6Equation19HScale
    have hE1 := one_le_lemma6ExceptionalFactorAt (x := x) (l := l) hxlog
    have hL100 : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 := one_le_pow₀ hL1
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 100 *
          lemma6ExceptionalFactorAt x l :=
        mul_le_mul (mul_le_mul hD1 hL100 (by norm_num) (by positivity))
          hE1 (by norm_num) (by positivity)
  have hH1real : (1 : ℝ) ≤ (H : ℝ) :=
    hscale1.trans (by
      dsimp only [H]
      exact lemma6Equation19HScale_le_cutoff x l)
  have hH1 : 1 ≤ H := by exact_mod_cast hH1real
  have hlogHsq0 : 0 ≤ Real.log ((H * H : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ H * H by nlinarith)
  apply lemma6BIntegralMajorant_le_of_D_le_Y hCp hCm hCd hL1 hD1 hYpos
    hlogU0 hlogU2
  · simpa only [H] using hmoll ε l hl
  · exact hlogHsq0
  · exact log_Hsq_le_of_log_two_Hsq_le hH1
      (by simpa only [H] using hlogHH l hl)

theorem eventually_shifted_equation19_BContribution_le_log20
    (h : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100)
    {Cp Cm Cd : ℝ} (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm) (hCd : 0 ≤ Cd) :
    ∀ᶠ x : ℕ in atTop, ∀ m : ℕ,
      ∀ l ∈ shiftedLemma6LargeBlockIndices h x ε,
      ∀ k ∈ lemma6PairBlockIndices x m,
        (1 / (2 * Real.pi)) *
            ((Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
              lemma6BIntegralMajorant x l k (lemma6Equation19HCutoff x l)
                Cp Cm Cd) ≤
          (x : ℝ) / Real.log (x : ℝ) ^ 20 := by
  let Croot : ℝ := (10368 * Cp ^ 2 * Cm * Cd) ^ ((1 : ℝ) / 4)
  let C : ℝ := 96 * Real.exp 1 * Croot
  let δ : ℝ := 31 * ε / 32
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  filter_upwards [eventually_shifted_BIntegralMajorant_H19_le_shape
      h hε hε' hCp hCm hCd,
    eventually_shiftedLemma6ExceptionalFactor_le_of_mem h hε hε',
    eventually_const_mul_log_pow_le_rpow C 80 hδ,
    eventually_three_le_log_nat,
    eventually_ge_atTop 1] with x hB hI habs hxlog hx1
  intro m l hl k hk
  let L := Real.log (x : ℝ)
  let T := (x : ℝ) ^ ((1 : ℝ) / 2 - ε)
  let D := lemma6DyadicModulusScale x l
  let Y := lemma6PairDyadicScale x k
  let E := lemma6ExceptionalFactorAt x l
  have hx1real : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hL1 : (1 : ℝ) ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hD : D < 2 * T := by
    dsimp only [D, T]
    exact shiftedLemma6_occupied_modulusScale_lt_two_threshold
      (h := h) (by linarith) hl
  have hY : Y ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := by
    dsimp only [Y]
    exact lemma6_pairScale_le_of_mem_pairBlockIndices hx1 hk
  have hsqrtY : Real.sqrt Y ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    calc
      Real.sqrt Y ≤ Real.sqrt ((x : ℝ) ^ ((2 : ℝ) / 3)) :=
        Real.sqrt_le_sqrt hY
      _ = (x : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
        congr 1
        norm_num
  have hx13T : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ T := by
    dsimp only [T]
    exact Real.rpow_le_rpow_of_exponent_le hx1real (by linarith)
  have hS : D + Real.sqrt Y ≤ 3 * T := by linarith
  have hS0 : 0 ≤ D + Real.sqrt Y := by
    exact add_nonneg (lemma6DyadicModulusScale_nonneg x l)
      (Real.sqrt_nonneg Y)
  have hE : E ≤ 2 * (x : ℝ) ^ (ε / 32) := by
    dsimp only [E]
    exact hI l hl
  have hB' := hB m l hl k hk
  have houter0 : 0 ≤ (1 / (2 * Real.pi)) *
      (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) := by positivity
  have hpowid : (x : ℝ) ^ ((1 : ℝ) / 2) *
      (x : ℝ) ^ (ε / 32) * T = (x : ℝ) ^ (1 - δ) := by
    dsimp only [T, δ]
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hstep :
      (1 / (2 * Real.pi)) *
          ((Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
            lemma6BIntegralMajorant x l k (lemma6Equation19HCutoff x l)
              Cp Cm Cd) ≤
        C * (x : ℝ) ^ (1 - δ) * L ^ 60 := by
    calc
      (1 / (2 * Real.pi)) *
          ((Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
            lemma6BIntegralMajorant x l k (lemma6Equation19HCutoff x l)
              Cp Cm Cd) ≤
        (1 / (2 * Real.pi)) *
          (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (32 * Real.pi * Croot * E * (D + Real.sqrt Y) * L ^ 60) := by
        rw [show (1 / (2 * Real.pi)) *
            ((Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
              lemma6BIntegralMajorant x l k (lemma6Equation19HCutoff x l)
                Cp Cm Cd) =
          ((1 / (2 * Real.pi)) *
            (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2))) *
              lemma6BIntegralMajorant x l k (lemma6Equation19HCutoff x l)
                Cp Cm Cd by ring]
        apply mul_le_mul_of_nonneg_left _ houter0
        simpa only [Croot, E, D, Y, L] using hB'
      _ ≤ (1 / (2 * Real.pi)) *
          (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (32 * Real.pi * Croot *
            (2 * (x : ℝ) ^ (ε / 32)) * (3 * T) * L ^ 60) := by gcongr
      _ = C * (x : ℝ) ^ (1 - δ) * L ^ 60 := by
        rw [show (1 / (2 * Real.pi)) *
            (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
            (32 * Real.pi * Croot * (2 * (x : ℝ) ^ (ε / 32)) *
              (3 * T) * L ^ 60) =
          96 * Real.exp 1 * Croot *
            ((x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ (ε / 32) * T) *
              L ^ 60 by
                field_simp [Real.pi_ne_zero]
                ring]
        rw [hpowid]
  refine hstep.trans ?_
  calc
    C * (x : ℝ) ^ (1 - δ) * L ^ 60 =
        (C * L ^ 80) * (x : ℝ) ^ (1 - δ) / L ^ 20 := by
      field_simp [hLpos.ne']
    _ ≤ (x : ℝ) ^ δ * (x : ℝ) ^ (1 - δ) / L ^ 20 := by gcongr
    _ = (x : ℝ) / L ^ 20 := by
      rw [← Real.rpow_add hxpos,
        show δ + (1 - δ) = 1 by ring, Real.rpow_one]

end Chen
