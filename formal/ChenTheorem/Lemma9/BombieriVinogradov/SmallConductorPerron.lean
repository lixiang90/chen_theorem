import ChenTheorem.Lemma9.BombieriVinogradov.PerronTypeII
import ChenTheorem.Lemma6.AnalyticDecomposition
import ChenTheorem.Lemma6.Equation21

open scoped Classical Interval

namespace Chen.BombieriVinogradov

/-!
# Sharp Perron formula for the small-conductor term

This file starts the Siegel--Walfisz half of Bombieri--Vinogradov.  The
adjacent triangular kernels from `PerronTypeII` give an exact sharp cutoff
on the integer lattice on every positive vertical line.  We first record
the resulting exact finite Dirichlet-polynomial formula for `twistedPsi`.
The next layer replaces that polynomial by the absolutely convergent
von-Mangoldt L-series on `Re s > 1` and shifts a finite rectangle.
-/

/-- Scalar sharp Perron summand after separating the factor `n^{-s}`. -/
noncomputable def perronSharpScalarSummand
    (x n : ℕ) (s : ℂ) : ℂ :=
  perronSharpKernel x s * (n : ℂ) ^ (-s)

theorem perronSharpScalarSummand_eq
    (x n : ℕ) (hx : 1 ≤ x) (hn : 1 ≤ n) (s : ℂ) :
    perronSharpScalarSummand x n s =
      (perronUpperPoint x : ℂ) *
          Perron.f (perronUpperPoint x / n) s -
        (perronLowerPoint x : ℂ) *
          Perron.f (perronLowerPoint x / n) s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu := Perron.f_mul_eq_f
    (tpos := perronUpperPoint_pos x) (xpos := hnR) s
  have hl := Perron.f_mul_eq_f
    (tpos := perronLowerPoint_pos hx) (xpos := hnR) s
  have hu' : Perron.f (perronUpperPoint x) s * (n : ℂ) ^ (-s) =
      Perron.f (perronUpperPoint x / n) s := by
    simpa only [Complex.ofReal_natCast] using hu
  have hl' : Perron.f (perronLowerPoint x) s * (n : ℂ) ^ (-s) =
      Perron.f (perronLowerPoint x / n) s := by
    simpa only [Complex.ofReal_natCast] using hl
  unfold perronSharpScalarSummand perronSharpKernel
  rw [sub_mul, mul_assoc, mul_assoc, hu', hl']

/-- A line-uniform integrable majorant for one triangular Perron kernel.
The deliberately weaker second factor `sqrt (2+t²)` is the same one used
in the upstream Perron proof. -/
theorem norm_perron_f_vertical_le
    {y σ : ℝ} (hy : 0 < y) (hσ : 1 ≤ σ) (t : ℝ) :
    ‖Perron.f y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      y ^ σ *
        (1 / (Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2))) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs0 : s ≠ 0 := by
    intro hs
    apply_fun Complex.re at hs
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_self, add_zero, Complex.zero_re] at hs
    linarith
  have hs1 : s + 1 ≠ 0 := by
    intro hs
    apply_fun Complex.re at hs
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_self, add_zero, Complex.one_re, Complex.zero_re] at hs
    linarith
  have hnorm0 : Real.sqrt (1 + t ^ 2) ≤ ‖s‖ := by
    rw [← Real.sqrt_sq (norm_nonneg s)]
    apply Real.sqrt_le_sqrt
    rw [sq, Complex.sq_norm]
    simp only [s, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    nlinarith [sq_nonneg σ]
  have hnorm1 : Real.sqrt (2 + t ^ 2) ≤ ‖s + 1‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (s + 1))]
    apply Real.sqrt_le_sqrt
    have hsquare : ‖s + 1‖ ^ 2 = (σ + 1) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm]
      simp only [s, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re,
        Complex.add_im, Complex.one_im, zero_add]
      have him : ((t : ℂ) * Complex.I).im = t := by
        simp [Complex.mul_im]
      rw [him]
      ring
    rw [hsquare]
    nlinarith [sq_nonneg (σ - 1)]
  have hden :
      Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2) ≤
        ‖s‖ * ‖s + 1‖ :=
    mul_le_mul hnorm0 hnorm1 (Real.sqrt_nonneg _) (norm_nonneg s)
  have hdenpos : 0 < Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2) := by
    positivity
  unfold Perron.f
  rw [norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
    sub_self, add_zero]
  change y ^ σ / (‖s‖ * ‖s + 1‖) ≤ _
  calc
    y ^ σ / (‖s‖ * ‖s + 1‖) ≤
        y ^ σ /
          (Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2)) := by
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _)
        hdenpos hden
    _ = y ^ σ *
        (1 / (Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2))) := by ring

/-- The common vertical-line majorant is integrable. -/
theorem integrable_perronVerticalMajorant :
    MeasureTheory.Integrable (fun t : ℝ =>
      1 / (Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2))) := by
  exact MeasureTheory.Integrable.of_integral_ne_zero Perron.integralPosAux.ne'

/-- Integrated norm bound for a constant multiple of one triangular
Perron term. -/
theorem integral_norm_const_mul_perron_f_le
    (c : ℂ) {X y σ : ℝ} (hX : 0 ≤ X) (hy : 0 < y)
    (hσ : 1 ≤ σ) :
    (∫ t : ℝ,
        ‖c * (X : ℂ) *
          Perron.f y ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      ‖c‖ * X * y ^ σ *
        ∫ t : ℝ,
          1 / (Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2)) := by
  let g : ℝ → ℝ := fun t =>
    1 / (Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2))
  have hleft : MeasureTheory.Integrable (fun t : ℝ =>
      ‖c * (X : ℂ) *
        Perron.f y ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    exact ((Perron.isIntegrable hy (by linarith) (by linarith)).const_mul
      (c * (X : ℂ))).norm
  have hright : MeasureTheory.Integrable (fun t : ℝ =>
      (‖c‖ * X * y ^ σ) * g t) := by
    have hg : MeasureTheory.Integrable g := by
      simpa only [g] using integrable_perronVerticalMajorant
    exact hg.const_mul _
  calc
    (∫ t : ℝ,
        ‖c * (X : ℂ) *
          Perron.f y ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      ∫ t : ℝ, (‖c‖ * X * y ^ σ) * g t := by
        apply MeasureTheory.integral_mono hleft hright
        intro t
        dsimp only [g]
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hX]
        have h := norm_perron_f_vertical_le hy hσ t
        calc
          ‖c‖ * X * ‖Perron.f y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              ‖c‖ * X *
                (y ^ σ * (1 / (Real.sqrt (1 + t ^ 2) *
                  Real.sqrt (2 + t ^ 2)))) :=
            mul_le_mul_of_nonneg_left h
              (mul_nonneg (norm_nonneg c) hX)
          _ = _ := by ring
    _ = ‖c‖ * X * y ^ σ * ∫ t : ℝ, g t := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by rfl

/-- The sharp indicator of `[1,x]` is the scalar adjacent-endpoint Perron
integral on every positive vertical line. -/
theorem sharpIndicator_eq_perronSharpScalarVerticalIntegral
    (x n : ℕ) (hx : 1 ≤ x) (hn : 1 ≤ n)
    (σ : ℝ) (hσ : 0 < σ) :
    ((if n ≤ x then (1 : ℝ) else 0 : ℝ) : ℂ) =
      VerticalIntegral' (perronSharpScalarSummand x n) σ := by
  have hu0 : 1 ≤ x + 1 := by omega
  have hupper := perronTriangularWeight_nat_eq_verticalIntegral_at
    (x + 1) n hu0 hn σ hσ
  have hlower := perronTriangularWeight_nat_eq_verticalIntegral_at
    x n hx hn σ hσ
  have hsharp := sharpIndicator_eq_perronTriangularDifference x n hx
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hσ1 : σ ≠ -1 := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfu : MeasureTheory.Integrable (fun t : ℝ =>
      Perron.f (perronUpperPoint x / n)
        ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Perron.isIntegrable (div_pos (perronUpperPoint_pos x) hnR) hσ0 hσ1
  have hfl : MeasureTheory.Integrable (fun t : ℝ =>
      Perron.f (perronLowerPoint x / n)
        ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Perron.isIntegrable (div_pos (perronLowerPoint_pos hx) hnR) hσ0 hσ1
  have hupper' :
      (perronTriangularWeight (perronUpperPoint x) n : ℂ) =
        VerticalIntegral' (Perron.f (perronUpperPoint x / n)) σ := by
    simpa only [perronUpperPoint, Nat.cast_add, Nat.cast_one] using hupper
  have hlower' :
      (perronTriangularWeight (perronLowerPoint x) n : ℂ) =
        VerticalIntegral' (Perron.f (perronLowerPoint x / n)) σ := by
    simpa only [perronLowerPoint] using hlower
  rw [hsharp]
  push_cast
  rw [hupper', hlower']
  calc
    (perronUpperPoint x : ℂ) *
          VerticalIntegral' (Perron.f (perronUpperPoint x / n)) σ -
        (perronLowerPoint x : ℂ) *
          VerticalIntegral' (Perron.f (perronLowerPoint x / n)) σ =
      VerticalIntegral' (fun s : ℂ =>
        (perronUpperPoint x : ℂ) *
            Perron.f (perronUpperPoint x / n) s -
          (perronLowerPoint x : ℂ) *
            Perron.f (perronLowerPoint x / n) s) σ := by
      unfold VerticalIntegral' VerticalIntegral
      simp only [smul_eq_mul]
      rw [MeasureTheory.integral_sub (hfu.const_mul _) (hfl.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      ring
    _ = VerticalIntegral' (perronSharpScalarSummand x n) σ := by
      congr 1
      funext s
      exact (perronSharpScalarSummand_eq x n hx hn s).symm

/-- Finite sharp Perron integrand for the twisted Chebyshev sum. -/
noncomputable def sharpTwistedPsiFiniteIntegrand {q : ℕ}
    (x : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
      perronSharpScalarSummand x n s

theorem integrable_sharpTwistedPsiFiniteIntegrand {q : ℕ}
    (x : ℕ) (hx : 1 ≤ x) (χ : DirichletCharacter ℂ q)
    (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      sharpTwistedPsiFiniteIntegrand x χ
        ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold sharpTwistedPsiFiniteIntegrand
  apply MeasureTheory.integrable_finsetSum
  intro n hnmem
  have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hσ1 : σ ≠ -1 := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfu := (Perron.isIntegrable
    (div_pos (perronUpperPoint_pos x) hnR) hσ0 hσ1).const_mul
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        (perronUpperPoint x : ℂ))
  have hfl := (Perron.isIntegrable
    (div_pos (perronLowerPoint_pos hx) hnR) hσ0 hσ1).const_mul
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        (perronLowerPoint x : ℂ))
  apply (hfu.sub hfl).congr
  filter_upwards with t
  change
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (perronUpperPoint x : ℂ) *
            Perron.f (perronUpperPoint x / n)
              ((σ : ℂ) + (t : ℂ) * Complex.I) -
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (perronLowerPoint x : ℂ) *
            Perron.f (perronLowerPoint x / n)
              ((σ : ℂ) + (t : ℂ) * Complex.I) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        perronSharpScalarSummand x n ((σ : ℂ) + (t : ℂ) * Complex.I)
  rw [perronSharpScalarSummand_eq x n hx hn]
  ring

/-- Exact sharp Perron representation of one twisted Chebyshev sum by a
finite Dirichlet polynomial.  No asymptotic input is used here. -/
theorem twistedPsi_eq_sharpFinitePerron {q : ℕ}
    (x : ℕ) (hx : 1 ≤ x) (χ : DirichletCharacter ℂ q)
    (σ : ℝ) (hσ : 0 < σ) :
    twistedPsi x χ =
      VerticalIntegral' (sharpTwistedPsiFiniteIntegrand x χ) σ := by
  have hterm (n : ℕ) (hnmem : n ∈ Finset.Icc 1 x) :
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n =
        VerticalIntegral' (fun s : ℂ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            perronSharpScalarSummand x n s) σ := by
    have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
    have hind := sharpIndicator_eq_perronSharpScalarVerticalIntegral
      x n hx hn σ hσ
    rw [if_pos (Finset.mem_Icc.mp hnmem).2] at hind
    have hind' : (1 : ℂ) =
        VerticalIntegral' (perronSharpScalarSummand x n) σ := by
      simpa using hind
    calc
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n =
          ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n) * 1 := by ring
      _ = ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n) *
          VerticalIntegral' (perronSharpScalarSummand x n) σ := by rw [hind']
      _ = VerticalIntegral' (fun s : ℂ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            perronSharpScalarSummand x n s) σ := by
        unfold VerticalIntegral' VerticalIntegral
        simp only [smul_eq_mul]
        rw [MeasureTheory.integral_const_mul]
        ring
  rw [twistedPsi]
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) =
      ∑ n ∈ Finset.Icc 1 x,
        VerticalIntegral' (fun s : ℂ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            perronSharpScalarSummand x n s) σ := by
        exact Finset.sum_congr rfl hterm
    _ = VerticalIntegral' (sharpTwistedPsiFiniteIntegrand x χ) σ := by
      unfold VerticalIntegral' VerticalIntegral sharpTwistedPsiFiniteIntegrand
      simp only [smul_eq_mul]
      rw [MeasureTheory.integral_finsetSum]
      · simp only [Finset.mul_sum]
      · intro n hnmem
        have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
        have hσ0 : σ ≠ 0 := hσ.ne'
        have hσ1 : σ ≠ -1 := by linarith
        have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hfu := (Perron.isIntegrable
          (div_pos (perronUpperPoint_pos x) hnR) hσ0 hσ1).const_mul
            ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
              (perronUpperPoint x : ℂ))
        have hfl := (Perron.isIntegrable
          (div_pos (perronLowerPoint_pos hx) hnR) hσ0 hσ1).const_mul
            ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
              (perronLowerPoint x : ℂ))
        apply (hfu.sub hfl).congr
        filter_upwards with t
        change
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
                (perronUpperPoint x : ℂ) *
                  Perron.f (perronUpperPoint x / n)
                    ((σ : ℂ) + (t : ℂ) * Complex.I) -
              (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
                (perronLowerPoint x : ℂ) *
                  Perron.f (perronLowerPoint x / n)
                    ((σ : ℂ) + (t : ℂ) * Complex.I) =
            (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
              perronSharpScalarSummand x n
                ((σ : ℂ) + (t : ℂ) * Complex.I)
        rw [perronSharpScalarSummand_eq x n hx hn]
        ring

/-- The analytic full-series integrand used after passing from the exact
finite Perron formula to the logarithmic derivative. -/
noncomputable def sharpTwistedPsiLogDerivIntegrand {q : ℕ} [NeZero q]
    (x : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -(perronSharpKernel x s *
      (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s))

/-- Pointwise summation of the separated Perron terms gives the full
twisted von-Mangoldt L-series. -/
theorem tsum_sharpPerron_eq_kernel_mul_LSeries {q : ℕ}
    (x : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          perronSharpScalarSummand x n s) =
      perronSharpKernel x s *
        LSeries (fun n : ℕ => χ n *
          (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  let a : ℕ → ℂ := fun n => χ n *
    (ArithmeticFunction.vonMangoldt n : ℂ)
  have ha0 : a 0 = 0 := by
    dsimp only [a]
    simp
  calc
    (∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          perronSharpScalarSummand x n s) =
      ∑' n : ℕ, perronSharpKernel x s * LSeries.term a s n := by
        apply tsum_congr
        intro n
        rw [LSeries.term_def₀ ha0]
        unfold perronSharpScalarSummand
        dsimp only [a]
        ring
    _ = perronSharpKernel x s *
        ∑' n : ℕ, LSeries.term a s n := tsum_mul_left
    _ = _ := rfl

/-- On `Re s > 1`, the full Perron series is exactly the logarithmic
derivative integrand. -/
theorem tsum_sharpPerron_eq_logDeriv {q : ℕ} [NeZero q]
    (x : ℕ) (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          perronSharpScalarSummand x n s) =
      sharpTwistedPsiLogDerivIntegrand x χ s := by
  rw [tsum_sharpPerron_eq_kernel_mul_LSeries]
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hseq :
      (fun n : ℕ => χ n) *
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) =
        (fun n : ℕ => χ n *
          (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    funext n
    rfl
  rw [hseq] at h
  have hL :
      LSeries (fun n : ℕ => χ n *
          (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        -(deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s) := by
    calc
      _ = -deriv (LSeries (fun n : ℕ => χ n)) s /
          LSeries (fun n : ℕ => χ n) s := h
      _ = _ := by
        rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
          ← DirichletCharacter.LFunction_eq_LSeries χ hs]
        ring
  rw [hL]
  unfold sharpTwistedPsiLogDerivIntegrand
  ring

/-- The `n`-th full-series Perron term on Chen's original `α`-line. -/
noncomputable def sharpPerronAlphaTerm {q : ℕ}
    (x : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) (t : ℝ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
    perronSharpScalarSummand x n (Chen.lemma6AlphaPoint x t)

theorem integrable_sharpPerronAlphaTerm {q : ℕ}
    (x : ℕ) (hx : 2 ≤ x) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    MeasureTheory.Integrable (sharpPerronAlphaTerm x χ n) := by
  by_cases hn0 : n = 0
  · subst n
    have hz : sharpPerronAlphaTerm x χ 0 = 0 := by
      funext t
      simp [sharpPerronAlphaTerm]
    rw [hz]
    exact MeasureTheory.integrable_zero ℝ ℂ MeasureTheory.volume
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hσ : 0 < σ := by dsimp only [σ]; positivity
    have hσ0 : σ ≠ 0 := hσ.ne'
    have hσ1 : σ ≠ -1 := by linarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hfu := (Perron.isIntegrable
      (div_pos (perronUpperPoint_pos x) hnR) hσ0 hσ1).const_mul
        ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (perronUpperPoint x : ℂ))
    have hfl := (Perron.isIntegrable
      (div_pos (perronLowerPoint_pos (show 1 ≤ x by omega)) hnR) hσ0 hσ1).const_mul
        ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (perronLowerPoint x : ℂ))
    apply (hfu.sub hfl).congr
    filter_upwards with t
    have hpoint : Chen.lemma6AlphaPoint x t =
        (σ : ℂ) + (t : ℂ) * Complex.I := by
      unfold Chen.lemma6AlphaPoint
      dsimp only [σ]
    change
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            (perronUpperPoint x : ℂ) *
              Perron.f (perronUpperPoint x / n)
                ((σ : ℂ) + (t : ℂ) * Complex.I) -
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            (perronLowerPoint x : ℂ) *
              Perron.f (perronLowerPoint x / n)
                ((σ : ℂ) + (t : ℂ) * Complex.I) =
        sharpPerronAlphaTerm x χ n t
    unfold sharpPerronAlphaTerm
    rw [hpoint, perronSharpScalarSummand_eq x n (by omega) hn]
    ring

/-- The integrated norms of the full Perron series are summable on the
`α`-line.  This is the exact Tonelli/Bochner hypothesis needed to replace
the finite sharp sum by `-L'/L` without a tail error. -/
theorem summable_integral_norm_sharpPerronAlphaTerm {q : ℕ}
    (x : ℕ) (hx : 2 ≤ x) (χ : DirichletCharacter ℂ q) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖sharpPerronAlphaTerm x χ n t‖) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let K : ℝ := ∫ t : ℝ,
    1 / (Real.sqrt (1 + t ^ 2) * Real.sqrt (2 + t ^ 2))
  let D : ℝ :=
    (perronUpperPoint x * perronUpperPoint x ^ σ +
      perronLowerPoint x * perronLowerPoint x ^ σ) * K
  have hx1 : 1 ≤ x := by omega
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσone : 1 < σ := by
    dsimp only [σ]
    have : 0 < (1 : ℝ) / Real.log (x : ℝ) := by positivity
    linarith
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact MeasureTheory.integral_nonneg fun _ => by positivity
  have hΛsum : Summable (fun n : ℕ =>
      ‖LSeries.term Λ (σ : ℂ) n‖) := by
    rw [summable_norm_iff]
    simpa only [Λ, LSeriesSummable] using
      ArithmeticFunction.LSeriesSummable_vonMangoldt
        (s := (σ : ℂ)) (by simpa using hσone)
  have hmajor : Summable (fun n : ℕ =>
      D * ‖LSeries.term Λ (σ : ℂ) n‖) := hΛsum.mul_left D
  apply hmajor.of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg
    (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)]
  by_cases hn0 : n = 0
  · subst n
    have hz : sharpPerronAlphaTerm x χ 0 = 0 := by
      funext t
      simp [sharpPerronAlphaTerm]
    simp only [hz, Pi.zero_apply, norm_zero, MeasureTheory.integral_zero,
      LSeries.term_zero, mul_zero]
    exact le_rfl
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    let c : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
    let Fu : ℝ → ℂ := fun t =>
      c * (perronUpperPoint x : ℂ) *
        Perron.f (perronUpperPoint x / n)
          ((σ : ℂ) + (t : ℂ) * Complex.I)
    let Fl : ℝ → ℂ := fun t =>
      c * (perronLowerPoint x : ℂ) *
        Perron.f (perronLowerPoint x / n)
          ((σ : ℂ) + (t : ℂ) * Complex.I)
    have hpoint (t : ℝ) : Chen.lemma6AlphaPoint x t =
        (σ : ℂ) + (t : ℂ) * Complex.I := by
      unfold Chen.lemma6AlphaPoint
      dsimp only [σ]
    have hterm (t : ℝ) : sharpPerronAlphaTerm x χ n t = Fu t - Fl t := by
      unfold sharpPerronAlphaTerm Fu Fl c
      rw [hpoint, perronSharpScalarSummand_eq x n hx1 hn]
      ring
    have hFu : MeasureTheory.Integrable Fu := by
      dsimp only [Fu]
      exact (Perron.isIntegrable
        (div_pos (perronUpperPoint_pos x) hnR)
          (by linarith) (by linarith)).const_mul _
    have hFl : MeasureTheory.Integrable Fl := by
      dsimp only [Fl]
      exact (Perron.isIntegrable
        (div_pos (perronLowerPoint_pos hx1) hnR)
          (by linarith) (by linarith)).const_mul _
    have htriangle :
        (∫ t : ℝ, ‖sharpPerronAlphaTerm x χ n t‖) ≤
          (∫ t : ℝ, ‖Fu t‖) + ∫ t : ℝ, ‖Fl t‖ := by
      calc
        _ ≤ ∫ t : ℝ, ‖Fu t‖ + ‖Fl t‖ := by
          apply MeasureTheory.integral_mono
            (integrable_sharpPerronAlphaTerm x hx χ n).norm
            (hFu.norm.add hFl.norm)
          intro t
          change ‖sharpPerronAlphaTerm x χ n t‖ ≤ ‖Fu t‖ + ‖Fl t‖
          rw [hterm]
          exact norm_sub_le _ _
        _ = _ := MeasureTheory.integral_add hFu.norm hFl.norm
    have hupper := integral_norm_const_mul_perron_f_le c
      (perronUpperPoint_pos x).le
      (div_pos (perronUpperPoint_pos x) hnR) hσone.le
    have hlower := integral_norm_const_mul_perron_f_le c
      (perronLowerPoint_pos hx1).le
      (div_pos (perronLowerPoint_pos hx1) hnR) hσone.le
    have hcoeff : ‖c‖ ≤ ArithmeticFunction.vonMangoldt n := by
      dsimp only [c]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (χ.norm_le_one n)
    have huFactor :
        (perronUpperPoint x / (n : ℝ)) ^ σ =
          perronUpperPoint x ^ σ / (n : ℝ) ^ σ :=
      Real.div_rpow (perronUpperPoint_pos x).le hnR.le σ
    have hlFactor :
        (perronLowerPoint x / (n : ℝ)) ^ σ =
          perronLowerPoint x ^ σ / (n : ℝ) ^ σ :=
      Real.div_rpow (perronLowerPoint_pos hx1).le hnR.le σ
    have htermnorm :
        ‖LSeries.term Λ (σ : ℂ) n‖ =
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
      rw [LSeries.norm_term_eq]
      simp only [hn0, if_false, Λ, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.ofReal_re]
    calc
      (∫ t : ℝ, ‖sharpPerronAlphaTerm x χ n t‖) ≤
          (∫ t : ℝ, ‖Fu t‖) + ∫ t : ℝ, ‖Fl t‖ := htriangle
      _ ≤ ‖c‖ * perronUpperPoint x *
              (perronUpperPoint x / (n : ℝ)) ^ σ * K +
            ‖c‖ * perronLowerPoint x *
              (perronLowerPoint x / (n : ℝ)) ^ σ * K := by
        exact add_le_add (by simpa only [Fu, K] using hupper)
          (by simpa only [Fl, K] using hlower)
      _ ≤ ArithmeticFunction.vonMangoldt n * perronUpperPoint x *
              (perronUpperPoint x / (n : ℝ)) ^ σ * K +
            ArithmeticFunction.vonMangoldt n * perronLowerPoint x *
              (perronLowerPoint x / (n : ℝ)) ^ σ * K := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff
                (perronUpperPoint_pos x).le)
              (Real.rpow_nonneg
                (div_nonneg (perronUpperPoint_pos x).le hnR.le) σ)) hK0
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff
                (perronLowerPoint_pos hx1).le)
              (Real.rpow_nonneg
                (div_nonneg (perronLowerPoint_pos hx1).le hnR.le) σ)) hK0
      _ = D * ‖LSeries.term Λ (σ : ℂ) n‖ := by
        rw [huFactor, hlFactor, htermnorm]
        dsimp only [D]
        ring

/-- The full sharp Perron series may be integrated term by term on
Chen's original `α`-line. -/
theorem tsum_integral_sharpPerronAlphaTerm_eq_integral_tsum {q : ℕ}
    (x : ℕ) (hx : 2 ≤ x) (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, ∫ t : ℝ, sharpPerronAlphaTerm x χ n t) =
      ∫ t : ℝ, ∑' n : ℕ, sharpPerronAlphaTerm x χ n t := by
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (integrable_sharpPerronAlphaTerm x hx χ)
    (summable_integral_norm_sharpPerronAlphaTerm x hx χ)

/-- Terms outside the sharp interval `[1,x]` have zero integral.  Although
their integrands need not vanish pointwise, the adjacent Perron kernels
cancel after integration. -/
theorem integral_sharpPerronAlphaTerm_eq_zero_of_not_mem {q : ℕ}
    (x : ℕ) (hx : 2 ≤ x) (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hnmem : n ∉ Finset.Icc 1 x) :
    (∫ t : ℝ, sharpPerronAlphaTerm x χ n t) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [sharpPerronAlphaTerm]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnle : ¬n ≤ x := by
      intro hnx
      exact hnmem (Finset.mem_Icc.mpr ⟨hn, hnx⟩)
    let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hσ : 0 < σ := by dsimp only [σ]; positivity
    have hind := sharpIndicator_eq_perronSharpScalarVerticalIntegral
      x n (by omega) hn σ hσ
    rw [if_neg hnle] at hind
    have hV : VerticalIntegral' (perronSharpScalarSummand x n) σ = 0 := by
      simpa using hind.symm
    have hscalar :
        (∫ t : ℝ, perronSharpScalarSummand x n
          ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
      unfold VerticalIntegral' VerticalIntegral at hV
      simp only [smul_eq_mul] at hV
      rw [mul_assoc] at hV
      have hdenominator :
          (1 / (2 * ((Real.pi : ℂ) * Complex.I))) ≠ 0 := by
        apply one_div_ne_zero
        apply mul_ne_zero
        · norm_num
        · exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
            Complex.I_ne_zero
      have hI := (mul_eq_zero.mp hV).resolve_left hdenominator
      exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
    unfold sharpPerronAlphaTerm
    have hpoint (t : ℝ) : Chen.lemma6AlphaPoint x t =
        (σ : ℂ) + (t : ℂ) * Complex.I := by
      unfold Chen.lemma6AlphaPoint
      dsimp only [σ]
    simp_rw [hpoint]
    rw [MeasureTheory.integral_const_mul, hscalar, mul_zero]

/-- Exact logarithmic-derivative Perron formula for the twisted Chebyshev
sum on Chen's `α = 1 + 1 / log x` line.  This is the analytic starting
point for the finite-height small-conductor contour shift. -/
theorem twistedPsi_eq_sharpLogDerivPerron {q : ℕ} [NeZero q]
    (x : ℕ) (hx : 2 ≤ x) (χ : DirichletCharacter ℂ q) :
    twistedPsi x χ =
      VerticalIntegral' (sharpTwistedPsiLogDerivIntegrand x χ)
        (1 + 1 / Real.log (x : ℝ)) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  have hx1 : 1 ≤ x := by omega
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hpoint (t : ℝ) : Chen.lemma6AlphaPoint x t =
      (σ : ℂ) + (t : ℂ) * Complex.I := by
    unfold Chen.lemma6AlphaPoint
    dsimp only [σ]
  have hfinite :
      (∫ t : ℝ,
          sharpTwistedPsiFiniteIntegrand x χ
            (Chen.lemma6AlphaPoint x t)) =
        ∑ n ∈ Finset.Icc 1 x,
          ∫ t : ℝ, sharpPerronAlphaTerm x χ n t := by
    unfold sharpTwistedPsiFiniteIntegrand sharpPerronAlphaTerm
    rw [MeasureTheory.integral_finsetSum]
    intro n _
    exact integrable_sharpPerronAlphaTerm x hx χ n
  have hfull :
      (∫ t : ℝ,
          sharpTwistedPsiFiniteIntegrand x χ
            (Chen.lemma6AlphaPoint x t)) =
        ∫ t : ℝ,
          sharpTwistedPsiLogDerivIntegrand x χ
            (Chen.lemma6AlphaPoint x t) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 x,
          ∫ t : ℝ, sharpPerronAlphaTerm x χ n t := hfinite
      _ = ∑' n : ℕ,
          ∫ t : ℝ, sharpPerronAlphaTerm x χ n t :=
        (tsum_eq_sum (s := Finset.Icc 1 x) (fun n hnmem =>
          integral_sharpPerronAlphaTerm_eq_zero_of_not_mem
            x hx χ hnmem)).symm
      _ = ∫ t : ℝ,
          ∑' n : ℕ, sharpPerronAlphaTerm x χ n t :=
        tsum_integral_sharpPerronAlphaTerm_eq_integral_tsum x hx χ
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        unfold sharpPerronAlphaTerm
        exact tsum_sharpPerron_eq_logDeriv x χ
          (Chen.one_lt_lemma6AlphaPoint_re hx t)
  rw [twistedPsi_eq_sharpFinitePerron x hx1 χ σ hσ]
  change VerticalIntegral' (sharpTwistedPsiFiniteIntegrand x χ) σ =
    VerticalIntegral' (sharpTwistedPsiLogDerivIntegrand x χ) σ
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  simp_rw [← hpoint]
  rw [hfull]

/-- The adjacent-endpoint sharp Perron kernel is holomorphic in the right
half-plane.  In particular its two rational poles are safely to the left
of every contour used below. -/
theorem differentiableOn_perronSharpKernel_pos_re
    (x : ℕ) (hx : 1 ≤ x) :
    DifferentiableOn ℂ (perronSharpKernel x) {s : ℂ | 0 < s.re} := by
  have hperron (y : ℝ) (hy : 0 < y) :
      DifferentiableOn ℂ (Perron.f y) {s : ℂ | 0 < s.re} := by
    exact (Perron.isHolomorphicOn hy).mono (by
      intro s hs
      simp only [Set.mem_setOf_eq] at hs
      simp only [Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or]
      constructor
      · intro h
        subst s
        norm_num at hs
      · intro h
        subst s
        norm_num at hs)
  unfold perronSharpKernel
  exact ((hperron (perronUpperPoint x) (perronUpperPoint_pos x)).const_mul _).sub
    ((hperron (perronLowerPoint x) (perronLowerPoint_pos hx)).const_mul _)

/-- Cauchy--Goursat for the sharp small-conductor Perron integrand on the
finite rectangle bounded by `α` and Chen's shifted line `γ`.  The mixed
classical zero-free width is used only for heights `|t| ≤ T`. -/
theorem sharpLogDeriv_finite_rectangle_classical
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ t : ℝ, |t| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q t) :
    let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
    let α : ℝ := 1 + 1 / Real.log (x : ℝ)
    let F : ℂ → ℂ := sharpTwistedPsiLogDerivIntegrand x χ
    (∫ σ : ℝ in γ..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ σ : ℝ in γ..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • (∫ t : ℝ in (-T)..T,
        F ((α : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I • (∫ t : ℝ in (-T)..T,
        F ((γ : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  dsimp only
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let z : ℂ := (γ : ℂ) + (-T : ℂ) * Complex.I
  let w : ℂ := (α : ℂ) + (T : ℂ) * Complex.I
  let F : ℂ → ℂ := sharpTwistedPsiLogDerivIntegrand x χ
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hγα : γ ≤ α := by
    dsimp only [γ, α]
    have h1 : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) :=
      div_nonneg zero_le_one hlog.le
    linarith
  have hzre : z.re = γ := by dsimp only [z]; simp
  have hwre : w.re = α := by dsimp only [w]; simp
  have hzim : z.im = -T := by dsimp only [z]; simp
  have hwim : w.im = T := by dsimp only [w]; simp
  have hk : DifferentiableOn ℂ (perronSharpKernel x)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    (differentiableOn_perronSharpKernel_pos_re x (by omega)).mono (by
      intro s hs
      change 0 < s.re
      have hre := hs.1
      rw [hzre, hwre, Set.uIcc_of_le hγα] at hre
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (hγpos.trans hre.1))
  have hLq : DifferentiableOn ℂ
      (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro s hs
    have hre := hs.1
    have him := hs.2
    rw [hzre, hwre, Set.uIcc_of_le hγα] at hre
    rw [hzim, hwim, Set.uIcc_of_le (by linarith)] at him
    have habs : |s.im| ≤ T :=
      abs_le.mpr ⟨by linarith [him.1], him.2⟩
    have hwidths := hwidth s.im habs
    have htwoDiv : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwoDiv] at hwidths
    have hhalfwidth : 1 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q s.im / 2 := by
      linarith
    have hhalf : 1 -
        Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q s.im / 2 < γ := by
      dsimp only [γ]
      linarith
    have hregion : 1 -
        Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q s.im < s.re := by
      have hwpos := Chen.primitiveZeroFreeWidth_pos data.cHeight_pos
        data.cSiegel_pos hq s.im
      exact Chen.one_sub_width_lt_of_half_width_le hwpos
        (hhalf.le.trans hre.1)
    have hne := data.nonvanishing q inferInstance χ hq hχ s hregion
    exact ((Chen.primitiveCharacter_differentiable_LFunction_deriv hq
        hχ).differentiableAt.div
      (Chen.primitiveCharacter_differentiable_LFunction hq hχ).differentiableAt
      hne).differentiableWithinAt
  have hdiff : DifferentiableOn ℂ F
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    unfold F sharpTwistedPsiLogDerivIntegrand
    exact (hk.mul hLq).neg
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  rw [hzre, hwre, hzim, hwim] at hrect
  dsimp only [F] at hrect
  simpa only [γ, α, sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hrect

end Chen.BombieriVinogradov
