/-
The analytic specialization of equation (16) in Chen's proof of Lemma 6.

On the line `α = 1 + 1 / log x`, the Dirichlet L-function is represented
by its absolutely convergent series and is nonzero.  This file instantiates
the algebraic mollifier identity with the actual L-function and records the
pointwise `A + B` norm split used in equation (17).
-/
import ChenTheorem.Lemma6.Mollifier
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- The vertical point `α + iν`, where `α = 1 + 1 / log x`. -/
noncomputable def lemma6AlphaPoint (x : ℕ) (ν : ℝ) : ℂ :=
  ((1 + 1 / Real.log x : ℝ) : ℂ) + (ν : ℂ) * Complex.I

@[simp]
theorem lemma6AlphaPoint_re (x : ℕ) (ν : ℝ) :
    (lemma6AlphaPoint x ν).re = 1 + 1 / Real.log x := by
  change
    (1 + 1 / Real.log (x : ℝ)) + (ν * 0 - 0 * 1) =
      1 + 1 / Real.log (x : ℝ)
  ring

theorem one_lt_lemma6AlphaPoint_re {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    (1 : ℝ) < (lemma6AlphaPoint x ν).re := by
  rw [lemma6AlphaPoint_re]
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hdiv : 0 < (1 : ℝ) / Real.log (x : ℝ) :=
    div_pos zero_lt_one hlog
  linarith

/-- The truncated Möbius polynomial `S(H,s,χ)` from equations (14)--(17). -/
noncomputable def lemma6MollifierAt
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H,
    (ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s

/-- Equation (16) for the actual Dirichlet L-function on Chen's
`α`-line.  Nonvanishing is discharged by absolute convergence in
`Re s > 1`. -/
theorem lemma6_equation16_at_alpha
    {q x H : ℕ} [NeZero q] (hx : 2 ≤ x)
    (ν : ℝ) (χ : DirichletCharacter ℂ q) :
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) =
      (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)) *
        (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
          lemma6MollifierAt H (lemma6AlphaPoint x ν) χ) +
      deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
        lemma6MollifierAt H (lemma6AlphaPoint x ν) χ := by
  apply lemma6_logDeriv_mollifier_identity
  have hs := one_lt_lemma6AlphaPoint_re hx ν
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs

/-- A character-independent majorant for `L'/L` in the absolutely
convergent half-plane. -/
noncomputable def lemma6LogDerivMajorant (s : ℂ) : ℝ :=
  ∑' n : ℕ,
    ‖LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖

/-- On `Re s > 1`, the logarithmic derivative is bounded termwise by the
untwisted von Mangoldt Dirichlet series.  This isolates the elementary
scalar estimate that supplies Chen's `(log x)^2` loss. -/
theorem lemma6_norm_logDeriv_le_majorant
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤
      lemma6LogDerivMajorant s := by
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let χseq : ℕ → ℂ := fun n => χ n
  let twist : ℕ → ℂ := χseq * Λ
  have htwist : LSeriesSummable twist s := by
    simpa only [twist, χseq, Λ] using
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ : LSeriesSummable Λ s := by
    simpa only [Λ] using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hidentity :
      deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s = -LSeries twist s := by
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs]
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
    change LSeries twist s =
      -deriv (LSeries χseq) s / LSeries χseq s at h
    rw [h]
    ring
  have htwistNorm : Summable (fun n => ‖LSeries.term twist s n‖) := by
    rw [summable_norm_iff]
    exact htwist
  have hΛNorm : Summable (fun n => ‖LSeries.term Λ s n‖) := by
    rw [summable_norm_iff]
    exact hΛ
  have hterm : ∀ n,
      ‖LSeries.term twist s n‖ ≤ ‖LSeries.term Λ s n‖ := by
    intro n
    apply LSeries.norm_term_le
    dsimp only [twist]
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)
  rw [hidentity, norm_neg, LSeries, lemma6LogDerivMajorant]
  exact (norm_tsum_le_tsum_norm htwistNorm).trans
    (htwistNorm.tsum_le_tsum hterm hΛNorm)

/-- Pointwise `A + B` split in equation (17).  `P` is the prime-pair
Dirichlet polynomial; its precise dyadic support is irrelevant to this
algebraic-norm step. -/
theorem lemma6_pair_mul_logDeriv_norm_le_A_add_B
    {q x H : ℕ} [NeZero q] (hx : 2 ≤ x)
    (ν : ℝ) (χ : DirichletCharacter ℂ q) (P : ℂ) :
    ‖P * (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖ ≤
      ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)‖ *
          ‖1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
            lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ +
        ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν)‖ *
          ‖lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ := by
  let A : ℂ :=
    (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)) *
      (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
        lemma6MollifierAt H (lemma6AlphaPoint x ν) χ)
  let B : ℂ :=
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
      lemma6MollifierAt H (lemma6AlphaPoint x ν) χ
  have hid :
      deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) = A + B := by
    simpa only [A, B] using lemma6_equation16_at_alpha hx ν χ
  calc
    ‖P * (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖ =
        ‖P * (A + B)‖ := congrArg (fun z : ℂ => ‖P * z‖) hid
    _ = ‖P * A + P * B‖ := by rw [mul_add]
    _ ≤ ‖P * A‖ + ‖P * B‖ := norm_add_le _ _
    _ = ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)‖ *
          ‖1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
            lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ +
        ‖P‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν)‖ *
          ‖lemma6MollifierAt H (lemma6AlphaPoint x ν) χ‖ := by
      simp only [A, B, norm_mul]
      ring

end Chen
