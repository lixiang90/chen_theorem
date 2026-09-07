import ChenTheorem.Lemma6.BiquadraticCoefficients
import ChenTheorem.Analysis.SignedTaylorSeries

open ArithmeticFunction
open scoped ComplexOrder

namespace Chen

noncomputable def biquadraticLFunction {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ s *
    DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s

theorem LSeriesSummable_charArithmetic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s (fun hn => χ.apply_eq_toArithmeticFunction_apply hn)).mp
    (ZMod.LSeriesSummable_of_one_lt_re χ hs)

theorem LSeriesSummable_biquadraticCoefficients {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (biquadraticCoefficients χ ψ) s :=
  ArithmeticFunction.LSeriesSummable_mul (χ.LSeriesSummable_zetaMul hs)
    (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_charArithmetic ψ hs)
      (LSeriesSummable_charArithmetic (χ * ψ) hs))

theorem biquadraticLFunction_eq_LSeries {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    biquadraticLFunction χ ψ s = LSeries (biquadraticCoefficients χ ψ) s := by
  have he (η : DirichletCharacter ℂ q) :
      LSeries (toArithmeticFunction (η ·)) s = DirichletCharacter.LFunction η s := by
    rw [η.LFunction_eq_LSeries hs]
    exact LSeries_congr (fun hn => (η.apply_eq_toArithmeticFunction_apply hn).symm) s
  have hz : LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s = riemannZeta s :=
    LSeries_zeta_eq_riemannZeta hs
  have hfirst : LSeries χ.zetaMul s = riemannZeta s * DirichletCharacter.LFunction χ s := by
    calc
      LSeries χ.zetaMul s =
          LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s *
            LSeries (toArithmeticFunction (χ ·)) s :=
        ArithmeticFunction.LSeries_mul' (LSeriesSummable_zeta_iff.mpr hs)
          (LSeriesSummable_charArithmetic χ hs)
      _ = _ := congrArg₂ (· * ·) hz (he χ)
  have hsecond : LSeries (toArithmeticFunction (ψ ·) *
      toArithmeticFunction ((χ * ψ) ·) : ArithmeticFunction ℂ) s =
      DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s := by
    calc
      _ = LSeries (toArithmeticFunction (ψ ·)) s *
          LSeries (toArithmeticFunction ((χ * ψ) ·) : ArithmeticFunction ℂ) s :=
        ArithmeticFunction.LSeries_mul' (LSeriesSummable_charArithmetic ψ hs)
          (LSeriesSummable_charArithmetic (χ * ψ) hs)
      _ = _ := congrArg₂ (· * ·) (he ψ) (he (χ * ψ))
  symm
  calc
    LSeries (biquadraticCoefficients χ ψ) s = LSeries χ.zetaMul s *
        LSeries (toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·) : ArithmeticFunction ℂ) s :=
      ArithmeticFunction.LSeries_mul' (χ.LSeriesSummable_zetaMul hs)
        (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_charArithmetic ψ hs)
          (LSeriesSummable_charArithmetic (χ * ψ) hs))
    _ = (riemannZeta s * DirichletCharacter.LFunction χ s) *
        (DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s) :=
      congrArg₂ (· * ·) hfirst hsecond
    _ = biquadraticLFunction χ ψ s := by unfold biquadraticLFunction; ring

theorem biquadraticLFunction_real_ge_one {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) : 1 ≤ biquadraticLFunction χ ψ (σ : ℂ) := by
  rw [biquadraticLFunction_eq_LSeries χ ψ (by simpa using hσ)]
  have hs := LSeriesSummable_biquadraticCoefficients χ ψ (s := (σ : ℂ)) (by simpa using hσ)
  have hn (n : ℕ) : 0 ≤ LSeries.term (biquadraticCoefficients χ ψ) (σ : ℂ) n :=
    LSeries.term_nonneg (biquadraticCoefficients_nonneg χ ψ hχ hψ n) σ
  have hone := (biquadraticCoefficients_isMultiplicative χ ψ).map_one
  simpa [LSeries, LSeries.term_def, hone] using hs.le_tsum 1 (fun n _ => hn n)

theorem biquadraticLSeries_iteratedDeriv_alternating {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (LSeries (biquadraticCoefficients χ ψ)) (σ : ℂ) := by
  have hab : LSeries.abscissaOfAbsConv (biquadraticCoefficients χ ψ) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun _ hs => LSeriesSummable_biquadraticCoefficients χ ψ hs)
  exact LSeries.iteratedDeriv_alternating (biquadraticCoefficients_nonneg χ ψ hχ hψ)
    (hab.trans_lt (by exact_mod_cast hσ)) n

theorem biquadraticLFunction_iteratedDeriv_alternating {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (biquadraticLFunction χ ψ) (σ : ℂ) := by
  have he : Set.EqOn (biquadraticLFunction χ ψ) (LSeries (biquadraticCoefficients χ ψ))
      {s : ℂ | 1 < s.re} := fun _ hs => biquadraticLFunction_eq_LSeries χ ψ hs
  have hopen : IsOpen {s : ℂ | 1 < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [he.iteratedDeriv_of_isOpen hopen n (by simpa using hσ)]
  exact biquadraticLSeries_iteratedDeriv_alternating χ ψ hχ hψ σ hσ n

theorem backwardTaylorCoeff_biquadratic_nonneg {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) (n : ℕ) :
    0 ≤ backwardTaylorCoeff (biquadraticLFunction χ ψ) (σ : ℂ) n :=
  backwardTaylorCoeff_nonneg_of_alternating
    (biquadraticLFunction_iteratedDeriv_alternating χ ψ hχ hψ σ hσ) n

end Chen
