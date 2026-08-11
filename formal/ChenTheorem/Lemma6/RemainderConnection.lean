/-
The exact analytic connection behind equation (14) in Chen's proof.

The finite convolution identity in `Mollifier.lean` concerns a truncated
Dirichlet polynomial.  The factor occurring in equation (16), however, is
the actual Dirichlet `L`-function.  This file separates its absolutely
convergent series into the finite part and a genuine tail, and records the
resulting exact remainder identity.  Estimating the tail is then a separate
analytic step, exactly as in the paper.
-/
import ChenTheorem.Lemma6.MomentConnection

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- The completely multiplicative Dirichlet-series phase
`χ(n) / n^s`. -/
noncomputable def lemma6DirichletPhase
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  χ n / (n : ℂ) ^ s

/-- The first `H` terms of the Dirichlet series for `L(s,χ)`. -/
noncomputable def lemma6TruncatedLAt
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H, lemma6DirichletPhase χ s n

/-- The genuine complement of the first `H` terms in the Dirichlet series.
The complement also contains `n = 0`, whose `LSeries.term` is zero. -/
noncomputable def lemma6LSeriesTail
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : {n : ℕ // n ∉ Finset.Icc 1 H},
    LSeries.term (fun n : ℕ => χ n) s n

/-- Unit-size phase which puts the real factor `1/n` in exactly the form
expected by the character large sieve in equation (14). -/
noncomputable def lemma6RemainderPhase (s : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) / (n : ℂ) ^ s

theorem norm_lemma6RemainderPhase_le_one
    {s : ℂ} (hs : 1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖lemma6RemainderPhase s n‖ ≤ 1 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lemma6RemainderPhase
  rw [norm_div, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos hnpos]
  apply (div_le_one (Real.rpow_pos_of_pos hnR _)).2
  calc
    (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    _ ≤ (n : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hnOne hs

/-- Elementary bound `|S(H,s,χ)| ≤ harmonic H` on `Re s ≥ 1`. -/
theorem norm_lemma6MollifierAt_le_harmonic
    {q H : ℕ} {s : ℂ} (hs : 1 ≤ s.re)
    (χ : DirichletCharacter ℂ q) :
    ‖lemma6MollifierAt H s χ‖ ≤ (harmonic H : ℝ) := by
  unfold lemma6MollifierAt
  calc
    ‖∑ n ∈ Finset.Icc 1 H,
        (ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ ≤
      ∑ n ∈ Finset.Icc 1 H,
        ‖(ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 H, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnNat : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : 0 < n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hnum :
          ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖χ n‖ ≤ 1 := by
        nlinarith [norm_nonneg (ArithmeticFunction.moebius n : ℂ),
          norm_nonneg (χ n), χ.norm_le_one n]
      have hden : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
        calc
          (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ (n : ℝ) ^ s.re :=
            Real.rpow_le_rpow_of_exponent_le hnOne hs
      rw [norm_div, norm_mul,
        Complex.norm_natCast_cpow_of_pos hnpos]
      calc
        ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖χ n‖ /
            (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hnR.le _)
        _ ≤ 1 / (n : ℝ) :=
          one_div_le_one_div_of_le hnR hden
        _ = (n : ℝ)⁻¹ := one_div _
    _ = (harmonic H : ℝ) := by
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- The analytic truncation estimate used, but not proved, in the paragraph
preceding equation (14).  It is a Pólya--Vinogradov/partial-summation input
and is logically independent of Chen's Lemma 3. -/
def Lemma6LFunctionTruncation : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {q H : ℕ} [NeZero q] {s : ℂ},
    1 ≤ H → 1 ≤ s.re →
    ∀ χ : DirichletCharacter ℂ q,
      ‖lemma6LSeriesTail H s χ‖ ≤
        C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H

theorem lemma6TruncatedLAt_eq_polynomial
    {q H : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6TruncatedLAt H s χ =
      lemma6TruncatedLPolynomial H (lemma6DirichletPhase χ s) := by
  rfl

theorem lemma6MollifierAt_eq_polynomial
    {q H : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6MollifierAt H s χ =
      lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) := by
  unfold lemma6MollifierAt lemma6MollifierPolynomial lemma6DirichletPhase
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The finite `C_H` polynomial is supported on `H < n ≤ H²`. -/
theorem lemma6MollifierRemainderPolynomial_eq_sum_Ioc
    {H : ℕ} (hH : 1 ≤ H) (a : ℕ → ℂ) :
    lemma6MollifierRemainderPolynomial H a =
      ∑ n ∈ Finset.Ioc H (H * H),
        (lemma6MollifierCoeff H n : ℂ) * a n := by
  unfold lemma6MollifierRemainderPolynomial
  symm
  apply Finset.sum_subset
  · intro n hn
    have hndata := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hndata.2⟩
  · intro n hnIcc hnNot
    have hndata := Finset.mem_Icc.mp hnIcc
    have hnH : n ≤ H := by
      by_contra h
      exact hnNot (Finset.mem_Ioc.mpr ⟨lt_of_not_ge h, hndata.2⟩)
    rw [lemma6MollifierCoeff_eq_zero_of_le hH hndata.1 hnH]
    simp

/-- Rewriting of the finite remainder polynomial into the exact coefficient
normalization consumed by `lemma6_mollifier_large_sieve`. -/
theorem lemma6MollifierRemainderPolynomial_eq_largeSieve_sum
    {q H : ℕ} (hH : 1 ≤ H) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s) =
      ∑ n ∈ Finset.Ioc H (H * H),
        (((lemma6MollifierCoeff H n : ℂ) *
          lemma6RemainderPhase s n / (n : ℂ)) * χ n) := by
  rw [lemma6MollifierRemainderPolynomial_eq_sum_Ioc hH]
  apply Finset.sum_congr rfl
  intro n hn
  have hndata := Finset.mem_Ioc.mp hn
  have hnpos : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  unfold lemma6DirichletPhase lemma6RemainderPhase
  field_simp

theorem lemma6DirichletPhase_one
    {q : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6DirichletPhase χ s 1 = 1 := by
  simp [lemma6DirichletPhase]

theorem lemma6DirichletPhase_mul
    {q : ℕ} (s : ℂ) (χ : DirichletCharacter ℂ q)
    (m n : ℕ) (_hm : 1 ≤ m) (_hn : 1 ≤ n) :
    lemma6DirichletPhase χ s (m * n) =
      lemma6DirichletPhase χ s m * lemma6DirichletPhase χ s n := by
  have hχ : χ ((m * n : ℕ) : ZMod q) =
      χ (m : ZMod q) * χ (n : ZMod q) := by
    rw [Nat.cast_mul, map_mul]
  have hpow : ((m * n : ℕ) : ℂ) ^ s =
      (m : ℂ) ^ s * (n : ℂ) ^ s := by
    simpa only [Nat.cast_mul] using
      Complex.natCast_mul_natCast_cpow m n s
  unfold lemma6DirichletPhase
  rw [hχ, hpow]
  ring

/-- In the half-plane of absolute convergence, the actual `L`-function is
the finite Dirichlet polynomial plus the genuine series tail. -/
theorem lemma6LFunction_eq_truncated_add_tail
    {q : ℕ} [NeZero q] (H : ℕ) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    DirichletCharacter.LFunction χ s =
      lemma6TruncatedLAt H s χ + lemma6LSeriesTail H s χ := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hsum : Summable
      (LSeries.term (fun n : ℕ => χ n) s) := by
    simpa only [LSeriesSummable] using
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hfinite :
      (∑ n ∈ Finset.Icc 1 H,
          LSeries.term (fun n : ℕ => χ n) s n) =
        lemma6TruncatedLAt H s χ := by
    unfold lemma6TruncatedLAt lemma6DirichletPhase
    apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_of_ne_zero (by
      have := (Finset.mem_Icc.mp hn).1
      omega)]
  have hsplit := hsum.sum_add_tsum_subtype_compl (Finset.Icc 1 H)
  rw [hfinite] at hsplit
  exact hsplit.symm

/-- Exact form of the first display preceding equation (14): the finite
`C_H` polynomial and the analytic truncation tail are kept separate. -/
theorem lemma6_one_sub_LFunction_mul_mollifierAt
    {q H : ℕ} [NeZero q] (hH : 1 ≤ H) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ =
      lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s) -
        lemma6LSeriesTail H s χ * lemma6MollifierAt H s χ := by
  rw [lemma6LFunction_eq_truncated_add_tail H hs χ,
    lemma6TruncatedLAt_eq_polynomial,
    lemma6MollifierAt_eq_polynomial]
  have hfinite := lemma6_one_sub_truncated_product_eq_remainder hH
    (lemma6DirichletPhase χ s)
    (lemma6DirichletPhase_one s χ)
    (lemma6DirichletPhase_mul s χ)
  calc
    1 - (lemma6TruncatedLPolynomial H (lemma6DirichletPhase χ s) +
          lemma6LSeriesTail H s χ) *
          lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) =
        (1 - lemma6TruncatedLPolynomial H (lemma6DirichletPhase χ s) *
          lemma6MollifierPolynomial H (lemma6DirichletPhase χ s)) -
          lemma6LSeriesTail H s χ *
            lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) := by ring
    _ = lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s) -
        lemma6LSeriesTail H s χ *
          lemma6MollifierPolynomial H (lemma6DirichletPhase χ s) := by
      rw [hfinite]

/-- Triangle-inequality form of the exact remainder identity.  This is the
pointwise estimate whose two square terms become the polynomial large-sieve
term and the truncation-error term in equation (14). -/
theorem norm_one_sub_LFunction_mul_mollifierAt_le
    {q H : ℕ} [NeZero q] (hH : 1 ≤ H) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ≤
      ‖lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s)‖ +
      ‖lemma6LSeriesTail H s χ‖ * ‖lemma6MollifierAt H s χ‖ := by
  rw [lemma6_one_sub_LFunction_mul_mollifierAt hH hs χ]
  exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])

/-- Squared form used after summing over primitive characters in (14). -/
theorem norm_one_sub_LFunction_mul_mollifierAt_sq_le
    {q H : ℕ} [NeZero q] (hH : 1 ≤ H) {s : ℂ} (hs : 1 < s.re)
    (χ : DirichletCharacter ℂ q) :
    ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ^ 2 ≤
      2 * ‖lemma6MollifierRemainderPolynomial H
        (lemma6DirichletPhase χ s)‖ ^ 2 +
      2 * (‖lemma6LSeriesTail H s χ‖ ^ 2 *
        ‖lemma6MollifierAt H s χ‖ ^ 2) := by
  let a := ‖lemma6MollifierRemainderPolynomial H
    (lemma6DirichletPhase χ s)‖
  let b := ‖lemma6LSeriesTail H s χ‖ * ‖lemma6MollifierAt H s χ‖
  have hab :
      ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ≤
        a + b := by
    simpa only [a, b] using
      norm_one_sub_LFunction_mul_mollifierAt_le hH hs χ
  calc
    ‖1 - DirichletCharacter.LFunction χ s * lemma6MollifierAt H s χ‖ ^ 2 ≤
        (a + b) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hab 2
    _ ≤ 2 * (a ^ 2 + b ^ 2) := add_sq_le
    _ = 2 * ‖lemma6MollifierRemainderPolynomial H
          (lemma6DirichletPhase χ s)‖ ^ 2 +
        2 * (‖lemma6LSeriesTail H s χ‖ ^ 2 *
          ‖lemma6MollifierAt H s χ‖ ^ 2) := by
      dsimp only [a, b]
      ring

/-- Equation-(14) pointwise remainder bound after inserting the explicit
Dirichlet-series truncation estimate.  The first term is ready for the
character large sieve; the second is the paper's analytic error term. -/
theorem norm_one_sub_LFunction_mul_mollifierAt_sq_le_of_truncation
    (htrunc : Lemma6LFunctionTruncation) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q H : ℕ} [NeZero q] {s : ℂ},
      1 ≤ H → 1 < s.re →
      ∀ χ : DirichletCharacter ℂ q,
        ‖1 - DirichletCharacter.LFunction χ s *
            lemma6MollifierAt H s χ‖ ^ 2 ≤
          2 * ‖lemma6MollifierRemainderPolynomial H
            (lemma6DirichletPhase χ s)‖ ^ 2 +
          2 * ((C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H) ^ 2 *
            (harmonic H : ℝ) ^ 2) := by
  rcases htrunc with ⟨C, hC, htail⟩
  refine ⟨C, hC, ?_⟩
  intro q H _ s hH hs χ
  have htail' := htail hH hs.le χ
  have hmoll := norm_lemma6MollifierAt_le_harmonic (H := H) hs.le χ
  have hharm : 0 ≤ (harmonic H : ℝ) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    positivity
  have herror :
      ‖lemma6LSeriesTail H s χ‖ ^ 2 *
          ‖lemma6MollifierAt H s χ‖ ^ 2 ≤
        (C * ‖s‖ * Real.sqrt q * Real.log (2 * q) / H) ^ 2 *
          (harmonic H : ℝ) ^ 2 := by
    gcongr
  exact (norm_one_sub_LFunction_mul_mollifierAt_sq_le hH hs χ).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left herror (by norm_num)) _)

end Chen
