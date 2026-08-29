/-
Connections between the actual character blocks in equation (19) and the
fourth-moment estimates proved for `L'` and the truncated Möbius mollifier.

This file performs the dependent-sum rewrites, replaces the squarefree
weight `|μ(d)| / d` by `1 / φ(d)`, and applies equations (15) and Lemma 3
on the exact dyadic modulus interval.
-/
import ChenTheorem.Lemma6.BlockIntegrand
import ChenTheorem.Lemma6.MollifierLargeSieve

open Real
open scoped Classical ArithmeticFunction.Moebius

namespace Chen

theorem lemma6_lDerivFourth_characterBlock_eq
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lDerivFourthTerm d (lemma6BetaPoint x ν) := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hd0 : d ≠ 0 := by omega
  rw [lDerivFourthTerm, dif_neg hd0]
  simp only [lemma6PrimitiveBaseWeight, lemma6LDerivNorm, hd0,
    ↓reduceDIte, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

theorem lemma6_lDerivFourth_characterBlock_le_inv_totient
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lDerivFourthTerm d (lemma6BetaPoint x ν) := by
  rw [lemma6_lDerivFourth_characterBlock_eq hxlog ν]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hd0 : d ≠ 0 := by omega
  have hterm : 0 ≤ lDerivFourthTerm d (lemma6BetaPoint x ν) := by
    rw [lDerivFourthTerm, dif_neg hd0, primSum, tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

noncomputable def lemma6MollifierPhase (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ s)⁻¹

theorem lemma6_mollifierAt_sq_eq
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6MollifierAt H s χ ^ 2 =
      ∑ n ∈ Finset.Icc 1 (H * H),
        ((lemma6MollifierSquareCoeff H n : ℂ) *
          lemma6MollifierPhase s n) * χ n := by
  have hpoly :
      lemma6MollifierAt H s χ =
        lemma6MollifierPolynomial H (fun n => χ n / (n : ℂ) ^ s) := by
    unfold lemma6MollifierAt lemma6MollifierPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hpoly, lemma6_mollifierPolynomial_sq]
  · apply Finset.sum_congr rfl
    intro n hn
    unfold lemma6MollifierPhase
    ring
  · intro m n hm hn
    have hχ : χ ((m * n : ℕ) : ZMod q) =
        χ (m : ZMod q) * χ (n : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    have hpow : ((m * n : ℕ) : ℂ) ^ s =
        (m : ℂ) ^ s * (n : ℂ) ^ s :=
      by simpa only [Nat.cast_mul] using
        Complex.natCast_mul_natCast_cpow m n s
    rw [hχ, hpow]
    ring

theorem lemma6_mollifierPhase_norm_sq_le
    {s : ℂ} {n : ℕ} (hn : 1 ≤ n) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖lemma6MollifierPhase s n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
  have hnpos : 0 < n := by omega
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(s.re * 2) ≤ (-1 : ℝ) := by linarith
  rw [lemma6MollifierPhase, norm_inv,
    Complex.norm_natCast_cpow_of_pos hnpos]
  calc
    ((n : ℝ) ^ s.re)⁻¹ ^ 2 = (((n : ℝ) ^ s.re) ^ 2)⁻¹ :=
      inv_pow _ _
    _ = ((n : ℝ) ^ (s.re * 2))⁻¹ := by
      rw [Real.rpow_mul hnnonneg]
      norm_num
    _ = (n : ℝ) ^ (-(s.re * 2)) := by
      rw [Real.rpow_neg hnnonneg]
    _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnone hexp
    _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _

/-- The mollifier as the ordinary Dirichlet polynomial used by the
character large sieve in equation (20). -/
theorem lemma6MollifierAt_eq_sum_phase
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6MollifierAt H s χ =
      ∑ n ∈ Finset.Icc 1 H,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          lemma6MollifierPhase s n * χ n := by
  unfold lemma6MollifierAt lemma6MollifierPhase
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Primitive-character second moment of the finite Möbius mollifier. -/
noncomputable def lemma6MollifierSecondTerm
    (H q : ℕ) (s : ℂ) : ℝ :=
  primSum q (fun χ => ‖lemma6MollifierAt H s χ‖ ^ 2)

/-- Rewrite the mollifier second moment on the dependent character block. -/
theorem lemma6_mollifierSecond_characterBlock_eq
    {x l H : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 2) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lemma6MollifierSecondTerm H d s := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6MollifierNorm,
    lemma6MollifierSecondTerm, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

/-- Replace the squarefree base weight by `1/φ(d)` in the mollifier second
moment used in equation (20). -/
theorem lemma6_mollifierSecond_characterBlock_le_inv_totient
    {x l H : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6MollifierSecondTerm H d s := by
  rw [lemma6_mollifierSecond_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ lemma6MollifierSecondTerm H d s := by
    unfold lemma6MollifierSecondTerm primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

/-- The second moment written in the exact finite-polynomial form expected
by the character large sieve. -/
theorem lemma6_mollifierSecondTerm_eq_polynomial
    (H q : ℕ) (s : ℂ) :
    lemma6MollifierSecondTerm H q s =
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖∑ n ∈ Finset.Icc 1 H,
          (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
            lemma6MollifierPhase s n) * χ n‖ ^ 2
      else 0 := by
  unfold lemma6MollifierSecondTerm primSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [← lemma6MollifierAt_eq_sum_phase]
  · simp [hp]

/-- At `Re s ≥ 1/2`, the coefficient square sum of the unsquared mollifier
is bounded by the harmonic sum. -/
theorem lemma6_mollifier_second_coeff_sum_le_harmonic
    {H : ℕ} {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    (∑ n ∈ Finset.Icc 1 H,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          lemma6MollifierPhase s n‖ ^ 2) ≤
      (harmonic H : ℝ) := by
  rw [← lemma6_sum_Icc_inv_eq_harmonic]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hμ :
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        lemma6MollifierPhase s n‖ ^ 2 =
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ^ 2 *
        ‖lemma6MollifierPhase s n‖ ^ 2 := by
      rw [norm_mul, mul_pow]
    _ ≤ 1 ^ 2 * (n : ℝ)⁻¹ := by
      gcongr
      exact lemma6_mollifierPhase_norm_sq_le hn1 hs
    _ = (n : ℝ)⁻¹ := by ring

/-- Primitive-character fourth moment of Chen's finite Möbius mollifier. -/
noncomputable def lemma6MollifierFourthTerm
    (H q : ℕ) (s : ℂ) : ℝ :=
  primSum q (fun χ => ‖lemma6MollifierAt H s χ‖ ^ 4)

theorem lemma6_mollifierFourth_characterBlock_eq
    {x l H : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 4) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lemma6MollifierFourthTerm H d s := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6MollifierNorm,
    lemma6MollifierFourthTerm, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

theorem lemma6_mollifierFourthTerm_eq_squarePolynomial
    (H q : ℕ) (s : ℂ) :
    lemma6MollifierFourthTerm H q s =
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖∑ n ∈ Finset.Icc 1 (H * H),
          ((lemma6MollifierSquareCoeff H n : ℂ) *
            lemma6MollifierPhase s n) * χ n‖ ^ 2
      else 0 := by
  unfold lemma6MollifierFourthTerm primSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [← lemma6_mollifierAt_sq_eq]
    rw [norm_pow]
    ring
  · simp [hp]

theorem lemma6_mollifierFourth_characterBlock_le_inv_totient
    {x l H : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6MollifierFourthTerm H d s := by
  rw [lemma6_mollifierFourth_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ lemma6MollifierFourthTerm H d s := by
    unfold lemma6MollifierFourthTerm primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

theorem lemma6_deriv_fourth_moment_characterBlock_of
    (hfourth : Lemma6DerivativeFourthMoment) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ∀ (l : ℕ) (ν : ℝ), 1 ≤ l →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤
          C * (2 : ℝ) ^ l * (Real.log x) ^ 110 *
            ‖lemma6BetaPoint x ν‖ ^ 2 * (1 + ν ^ 2) ^ 2 := by
  rcases hfourth with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  have hlogReal : ∀ᶠ y : ℝ in Filter.atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  have hlog : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hbound, hlog] with x hx hxl
  intro l ν hl
  exact (lemma6_lDerivFourth_characterBlock_le_inv_totient hxl ν).trans
    (hx l ν hl)

noncomputable def lemma6ModulusLowerCutoff (x l : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100⌋₊

theorem lemma6ModulusLowerCutoff_one_le
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    1 ≤ lemma6ModulusLowerCutoff x l := by
  unfold lemma6ModulusLowerCutoff
  apply Nat.le_floor
  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (l - 1) :=
    one_le_pow₀ (by norm_num)
  have hpowlog : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 :=
    one_le_pow₀ hxlog
  simpa only [Nat.cast_one, one_mul] using
    mul_le_mul hpow2 hpowlog (by positivity) (by positivity)

theorem lemma6ModulusBlock_subset_Ioc_cutoffs
    {x l : ℕ} :
    lemma6ModulusBlock x l ⊆
      Finset.Ioc (lemma6ModulusLowerCutoff x l)
        (lemma6ModulusCutoff x l) := by
  intro d hd
  have hddata := hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
  rw [Finset.mem_Ioc]
  constructor
  · apply (Nat.floor_lt (by positivity)).2
    exact hddata.2.2.1
  · have hceil :
        (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 ≤
          (lemma6ModulusCutoff x l : ℝ) := by
      unfold lemma6ModulusCutoff
      exact Nat.le_ceil _
    exact_mod_cast hddata.2.2.2.trans hceil

theorem lemma6ModulusLowerCutoff_le_cutoff (x l : ℕ) :
    lemma6ModulusLowerCutoff x l ≤ lemma6ModulusCutoff x l := by
  have hlogpow : 0 ≤ Real.log (x : ℝ) ^ 100 := by positivity
  have hlower :
      (lemma6ModulusLowerCutoff x l : ℝ) ≤
        (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 := by
    unfold lemma6ModulusLowerCutoff
    exact Nat.floor_le (by positivity)
  have hscales :
      (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 ≤
        (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 := by
    apply mul_le_mul_of_nonneg_right _ hlogpow
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le l 1)
  have hupper :
      (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 ≤
        (lemma6ModulusCutoff x l : ℝ) := by
    unfold lemma6ModulusCutoff
    exact Nat.le_ceil _
  exact_mod_cast hlower.trans (hscales.trans hupper)

/-- Equation (20)'s second moment of the unsquared mollifier, obtained by
applying the dyadic character large sieve before squaring `S`. -/
theorem lemma6_mollifier_second_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l H : ℕ) (ν : ℝ), 1 ≤ Real.log (x : ℝ) →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              (H : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
            (1 + Real.log H) := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l H ν hxlog
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  let s := lemma6BetaPoint x ν
  let a : ℕ → ℂ := fun n =>
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      lemma6MollifierPhase s n
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hinterval : Finset.Ioc 0 H = Finset.Icc 1 H := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    dsimp only [s]
    rw [lemma6BetaPoint_re]
    have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
    have hinv : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hraw := hlarge D Q 0 H a hD hDQ
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lemma6MollifierSecondTerm H d (lemma6BetaPoint x ν) :=
      lemma6_mollifierSecond_characterBlock_le_inv_totient hxlog _
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 H, a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [lemma6_mollifierSecondTerm_eq_polynomial]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 H, a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Icc 1 H, ‖a n‖ ^ 2 := by
      simpa only [zero_add, hinterval] using hraw
    _ ≤ C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) *
          (harmonic H : ℝ) := by
      gcongr
      simpa only [a] using
        lemma6_mollifier_second_coeff_sum_le_harmonic (H := H) hs
    _ ≤ C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) *
          (1 + Real.log H) := by
      gcongr
      exact harmonic_le_one_add_log H
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          (H : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
          (1 + Real.log H) := by rfl

theorem lemma6_mollifier_fourth_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l H : ℕ) (ν : ℝ),
        1 ≤ Real.log (x : ℝ) → 2 ≤ H →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              ((H * H : ℕ) : ℝ) /
                (lemma6ModulusLowerCutoff x l : ℝ)) *
            (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by
  rcases lemma6_mollifierSquare_fourthMoment with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l H ν hxlog hH
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  let s := lemma6BetaPoint x ν
  let u := lemma6MollifierPhase s
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    dsimp only [s]
    rw [lemma6BetaPoint_re]
    have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
    have hinv : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hu : ∀ n ∈ Finset.Icc 1 (H * H),
      ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
    intro n hn
    exact lemma6_mollifierPhase_norm_sq_le (Finset.mem_Icc.mp hn).1 hs
  have hraw := hlarge D Q H u hD hDQ hH hu
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lemma6MollifierFourthTerm H d (lemma6BetaPoint x ν) :=
      lemma6_mollifierFourth_characterBlock_le_inv_totient hxlog _
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 (H * H),
              ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [lemma6_mollifierFourthTerm_eq_squarePolynomial]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 (H * H),
              ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
          (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := hraw
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          ((H * H : ℕ) : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
          (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by rfl

end Chen
