import ChenTheorem.Lemma9.BombieriVinogradov.SmallConductorSmoothing

open Filter Real
open scoped Classical Interval

namespace Chen.BombieriVinogradov

/-!
# Logarithmic-derivative form of the adjustable smoothing

This file passes from the finite Mellin representation of
`bvSmoothedTwistedPsi` to the absolutely convergent von Mangoldt
Dirichlet series on `Re s > 1`.  The resulting integrand is the one to be
moved through the finite zero-free rectangle.
-/

/-- One term of the full, separated Mellin series. -/
noncomputable def bvSmoothedFullTerm {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) (s : ℂ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
    ((x : ℂ) ^ s * (n : ℂ) ^ (-s) *
      Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s)

/-- The analytic integrand after summing the von Mangoldt series. -/
noncomputable def bvSmoothedLogDerivIntegrand {q : ℕ} [NeZero q]
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s *
      Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
    (deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s))

/-- Positive real quotients separate cleanly under complex powers. -/
theorem ofReal_div_cpow_eq_mul_cpow_neg
    {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) (s : ℂ) :
    (((x / n : ℝ) : ℂ) ^ s) =
      (x : ℂ) ^ s * (n : ℂ) ^ (-s) := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx (inv_nonneg.mpr hn.le)]
  congr 1
  rw [Complex.ofReal_inv, Complex.inv_cpow, ← Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hn.le]
  exact Real.pi_ne_zero.symm

/-- On a nonzero index, the quotient form coming from Mellin inversion
is exactly the separated full-series term. -/
theorem bvSmoothedFullTerm_eq_ratio {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n)
    (s : ℂ) :
    bvSmoothedFullTerm K x χ n s =
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
          Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x) s) := by
  rw [ofReal_div_cpow_eq_mul_cpow_neg
    (Nat.cast_nonneg x) (by exact_mod_cast (show 0 < n by omega))]
  unfold bvSmoothedFullTerm
  push_cast
  ring

/-- The full smoothed series is the expected logarithmic derivative on
the half-plane of absolute convergence. -/
theorem tsum_bvSmoothedFullTerm_eq_logDeriv
    {q : ℕ} [NeZero q] (K x : ℕ)
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, bvSmoothedFullTerm K x χ n s) =
      bvSmoothedLogDerivIntegrand K x χ s := by
  let a : ℕ → ℂ := fun n =>
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
  have ha0 : a 0 = 0 := by
    dsimp only [a]
    simp
  calc
    (∑' n : ℕ, bvSmoothedFullTerm K x χ n s) =
        ((x : ℂ) ^ s *
          Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
          (∑' n : ℕ, LSeries.term a s n) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [LSeries.term_def₀ ha0]
      unfold bvSmoothedFullTerm
      dsimp only [a]
      ring
    _ = ((x : ℂ) ^ s *
          Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
          LSeries a s := rfl
    _ = -(((x : ℂ) ^ s *
          Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
        (deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s)) := by
      have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
      have hseq :
          (fun n : ℕ => χ n) *
              (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) = a := by
        funext n
        rfl
      rw [hseq] at h
      have hL : LSeries a s =
          -(deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s) := by
        calc
          LSeries a s =
              -deriv (LSeries (fun n : ℕ => χ n)) s /
                LSeries (fun n : ℕ => χ n) s := h
          _ = _ := by
            rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
              ← DirichletCharacter.LFunction_eq_LSeries χ hs]
            ring
      rw [hL]
      ring
    _ = bvSmoothedLogDerivIntegrand K x χ s := rfl

/-- The full term restricted to Chen's standard initial line
`alpha = 1 + 1 / log x`. -/
noncomputable def bvSmoothedAlphaTerm {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) (t : ℝ) : ℂ :=
  bvSmoothedFullTerm K x χ n (Chen.lemma6AlphaPoint x t)

theorem bvSmoothedAlphaTerm_eq_ratio {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n)
    (t : ℝ) :
    bvSmoothedAlphaTerm K x χ n t =
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
            Chen.lemma6AlphaPoint x t) *
          Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x) (Chen.lemma6AlphaPoint x t)) := by
  unfold bvSmoothedAlphaTerm
  exact bvSmoothedFullTerm_eq_ratio K x χ hn _

theorem integrable_bvSmoothedAlphaTerm {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    MeasureTheory.Integrable (bvSmoothedAlphaTerm K x χ n) := by
  by_cases hn0 : n = 0
  · subst n
    have hz : bvSmoothedAlphaTerm K x χ 0 = 0 := by
      funext t
      simp [bvSmoothedAlphaTerm, bvSmoothedFullTerm]
    rw [hz]
    exact MeasureTheory.integrable_zero ℝ ℂ MeasureTheory.volume
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hσ : 0 < σ := by dsimp only [σ]; positivity
    have hy : 0 < (x : ℝ) / (n : ℝ) := by positivity
    have hbase := Chen.integrable_cpow_mul_lemma6SmoothingMellinKernel
      hy (bvSmoothingScale_pos K hlarge)
        (bvSmoothingOrder_one_le K hlarge) hσ
    exact hbase.const_mul
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n) |>.congr (by
        filter_upwards with t
        unfold bvSmoothedAlphaTerm
        rw [bvSmoothedFullTerm_eq_ratio K x χ hn]
        unfold Chen.lemma6AlphaPoint
        dsimp only [σ])

/-- The integrated norms of the full smoothed von Mangoldt series are
summable on the initial `alpha`-line.  This supplies the exact Tonelli
hypothesis needed below. -/
theorem summable_integral_norm_bvSmoothedAlphaTerm {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖bvSmoothedAlphaTerm K x χ n t‖) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let G : ℝ → ℝ := fun t =>
    ‖Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x)
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖
  let J : ℝ := ∫ t : ℝ, G t
  let D : ℝ := (x : ℝ) ^ σ * J
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσone : 1 < σ := by
    dsimp only [σ]
    have : 0 < (1 : ℝ) / Real.log (x : ℝ) := by positivity
    linarith
  have hGint : MeasureTheory.Integrable G := by
    have hk := Chen.verticalIntegrable_lemma6SmoothingMellinKernel
      (bvSmoothingScale_pos K hlarge)
      (bvSmoothingOrder_one_le K hlarge) (lt_trans zero_lt_one hσone)
    rw [Complex.VerticalIntegrable] at hk
    simpa only [G] using hk.norm
  have hJ0 : 0 ≤ J := by
    dsimp only [J]
    exact MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hJ0
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
    have hz : bvSmoothedAlphaTerm K x χ 0 = 0 := by
      funext t
      simp [bvSmoothedAlphaTerm, bvSmoothedFullTerm]
    simp only [hz, Pi.zero_apply, norm_zero, MeasureTheory.integral_zero,
      LSeries.term_zero, mul_zero]
    exact le_rfl
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    let y : ℝ := (x : ℝ) / (n : ℝ)
    let c : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
    have hy : 0 < y := by dsimp only [y]; positivity
    have hterm (t : ℝ) :
        bvSmoothedAlphaTerm K x χ n t =
          c * (((y : ℂ) ^
              ((σ : ℂ) + (t : ℂ) * Complex.I)) *
            Chen.lemma6SmoothingMellinKernel
              (bvSmoothingParameter K x)
              ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      unfold bvSmoothedAlphaTerm
      rw [bvSmoothedFullTerm_eq_ratio K x χ hn]
      unfold Chen.lemma6AlphaPoint
      dsimp only [σ, y, c]
    have hcoeff : ‖c‖ ≤ ArithmeticFunction.vonMangoldt n := by
      dsimp only [c]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (χ.norm_le_one n)
    have hpoint (t : ℝ) :
        ‖bvSmoothedAlphaTerm K x χ n t‖ ≤
          (ArithmeticFunction.vonMangoldt n * y ^ σ) * G t := by
      rw [hterm, norm_mul]
      have hinner :
          ‖(y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
              Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x)
                ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
            y ^ σ *
              ‖Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x)
                ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
          mul_one, sub_self, add_zero]
      rw [hinner]
      dsimp only [G]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff
            (Real.rpow_nonneg hy.le σ))
          (norm_nonneg (Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x)
            ((σ : ℂ) + (t : ℂ) * Complex.I))))
    have hright : MeasureTheory.Integrable (fun t : ℝ =>
        (ArithmeticFunction.vonMangoldt n * y ^ σ) * G t) :=
      hGint.const_mul _
    have htermnorm :
        ‖LSeries.term Λ (σ : ℂ) n‖ =
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
      rw [LSeries.norm_term_eq]
      simp only [hn0, if_false, Λ, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.ofReal_re]
    have hyFactor : y ^ σ =
        (x : ℝ) ^ σ / (n : ℝ) ^ σ := by
      dsimp only [y]
      exact Real.div_rpow hxpos.le hnpos.le σ
    calc
      (∫ t : ℝ, ‖bvSmoothedAlphaTerm K x χ n t‖) ≤
          ∫ t : ℝ,
            (ArithmeticFunction.vonMangoldt n * y ^ σ) * G t := by
        exact MeasureTheory.integral_mono
          (integrable_bvSmoothedAlphaTerm K hx hlarge χ n).norm
          hright hpoint
      _ = (ArithmeticFunction.vonMangoldt n * y ^ σ) * J := by
        rw [MeasureTheory.integral_const_mul]
      _ = D * ‖LSeries.term Λ (σ : ℂ) n‖ := by
        rw [hyFactor, htermnorm]
        dsimp only [D, J]
        ring

/-- The full smoothed series may be integrated term by term on the
initial line. -/
theorem tsum_integral_bvSmoothedAlphaTerm_eq_integral_tsum {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t) =
      ∫ t : ℝ, ∑' n : ℕ, bvSmoothedAlphaTerm K x χ n t := by
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (integrable_bvSmoothedAlphaTerm K hx hlarge χ)
    (summable_integral_norm_bvSmoothedAlphaTerm K hx hlarge χ)

/-- Terms outside `[1,x]` have zero Mellin integral because the adjustable
smoothing weight itself vanishes there. -/
theorem integral_bvSmoothedAlphaTerm_eq_zero_of_not_mem {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hnmem : n ∉ Finset.Icc 1 x) :
    (∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [bvSmoothedAlphaTerm, bvSmoothedFullTerm]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hxn : x ≤ n := by
      have : ¬(1 ≤ n ∧ n ≤ x) := by
        simpa only [Finset.mem_Icc] using hnmem
      omega
    let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hσ : 0 < σ := by dsimp only [σ]; positivity
    have hweight := bvSmoothingWeight_eq_smoothing_verticalIntegral
      K hx hn hlarge σ hσ
    rw [bvSmoothingWeight_eq_zero_of_le K hx hn hxn] at hweight
    have hcoef : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by
      exact one_div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    have hintegral :
        (∫ t : ℝ,
          ((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
              ((σ : ℂ) + (t : ℂ) * Complex.I) *
            Chen.lemma6SmoothingMellinKernel
              (bvSmoothingParameter K x)
              ((σ : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
      rw [Complex.real_smul] at hweight
      exact (mul_eq_zero.mp hweight.symm).resolve_left
        (Complex.ofReal_ne_zero.mpr hcoef)
    unfold bvSmoothedAlphaTerm
    simp_rw [bvSmoothedFullTerm_eq_ratio K x χ hn]
    unfold Chen.lemma6AlphaPoint
    change (∫ t : ℝ,
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n) *
        (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
            ((σ : ℂ) + (t : ℂ) * Complex.I)) *
          Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x)
            ((σ : ℂ) + (t : ℂ) * Complex.I))) = 0
    rw [MeasureTheory.integral_const_mul, hintegral, mul_zero]

/-- Exact logarithmic-derivative Perron formula for the adjustable
smoothed sum on `alpha = 1 + 1 / log x`. -/
theorem bvSmoothedTwistedPsi_eq_logDerivPerron
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    bvSmoothedTwistedPsi K x χ =
      VerticalIntegral' (bvSmoothedLogDerivIntegrand K x χ)
        (1 + 1 / Real.log (x : ℝ)) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hpoint (t : ℝ) : Chen.lemma6AlphaPoint x t =
      (σ : ℂ) + (t : ℂ) * Complex.I := by
    unfold Chen.lemma6AlphaPoint
    dsimp only [σ]
  have hfinite :
      (∫ t : ℝ,
          bvSmoothedTwistedPsiFiniteIntegrand K x χ
            (Chen.lemma6AlphaPoint x t)) =
        ∑ n ∈ Finset.Icc 1 x,
          ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t := by
    unfold bvSmoothedTwistedPsiFiniteIntegrand
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hnmem
      have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      exact (bvSmoothedAlphaTerm_eq_ratio K x χ hn t).symm
    · intro n hnmem
      have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
      exact (integrable_bvSmoothedAlphaTerm K hx hlarge χ n).congr (by
        filter_upwards with t
        exact bvSmoothedAlphaTerm_eq_ratio K x χ hn t)
  have hfull :
      (∫ t : ℝ,
          bvSmoothedTwistedPsiFiniteIntegrand K x χ
            (Chen.lemma6AlphaPoint x t)) =
        ∫ t : ℝ,
          bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6AlphaPoint x t) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 x,
          ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t := hfinite
      _ = ∑' n : ℕ,
          ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t :=
        (tsum_eq_sum (s := Finset.Icc 1 x) (fun n hnmem =>
          integral_bvSmoothedAlphaTerm_eq_zero_of_not_mem
            K hx hlarge χ hnmem)).symm
      _ = ∫ t : ℝ,
          ∑' n : ℕ, bvSmoothedAlphaTerm K x χ n t :=
        tsum_integral_bvSmoothedAlphaTerm_eq_integral_tsum
          K hx hlarge χ
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        unfold bvSmoothedAlphaTerm
        exact tsum_bvSmoothedFullTerm_eq_logDeriv K x χ
          (Chen.one_lt_lemma6AlphaPoint_re hx t)
  rw [bvSmoothedTwistedPsi_eq_finiteVerticalIntegral
    K hx hlarge χ σ hσ]
  change VerticalIntegral' (bvSmoothedTwistedPsiFiniteIntegrand K x χ) σ =
    VerticalIntegral' (bvSmoothedLogDerivIntegrand K x χ) σ
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  simp_rw [← hpoint]
  rw [hfull]

/-- Cauchy--Goursat for the adjustable smoothed logarithmic-derivative
integrand on the finite rectangle bounded by `alpha` and `gamma`.  The
mixed classical zero-free region is only required up to height `T`. -/
theorem bvSmoothedLogDeriv_finite_rectangle_classical
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ t : ℝ, |t| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q t) :
    let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
    let α : ℝ := 1 + 1 / Real.log (x : ℝ)
    let F : ℂ → ℂ := bvSmoothedLogDerivIntegrand K x χ
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
  let F : ℂ → ℂ := bvSmoothedLogDerivIntegrand K x χ
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hγα : γ ≤ α := by
    dsimp only [γ, α]
    have h1 : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by
      positivity
    have h2 : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) :=
      div_nonneg zero_le_one hlog.le
    linarith
  have hzre : z.re = γ := by dsimp only [z]; simp
  have hwre : w.re = α := by dsimp only [w]; simp
  have hzim : z.im = -T := by dsimp only [z]; simp
  have hwim : w.im = T := by dsimp only [w]; simp
  have hrectpos :
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    change 0 < s.re
    have hre := hs.1
    rw [hzre, hwre, Set.uIcc_of_le hγα] at hre
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (hγpos.trans hre.1)
  letI : NeZero (x : ℂ) := ⟨by
    exact_mod_cast (show x ≠ 0 by omega)⟩
  have hxpow : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    (differentiable_const_cpow_of_neZero (x : ℂ)).differentiableOn
  have hk : DifferentiableOn ℂ
      (Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x))
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    (Chen.differentiableOn_lemma6SmoothingMellinKernel
      (one_lt_bvSmoothingParameter K hx)).mono hrectpos
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
    unfold F bvSmoothedLogDerivIntegrand
    exact ((hxpow.mul hk).mul hLq).neg
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  rw [hzre, hwre, hzim, hwim] at hrect
  dsimp only [F] at hrect
  simpa only [γ, α, sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hrect

/-- Pointwise product bound inside the half-width classical zero-free
region.  All three analytic costs (`x^s`, the Mellin kernel, and `L'/L`)
remain explicit for later specialization to vertical and horizontal
edges. -/
theorem norm_bvSmoothedLogDerivIntegrand_le_classical
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (s : ℂ) (hspos : 0 < s.re)
    (hregion : 1 -
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q s.im / 2 ≤
        s.re) :
    ‖bvSmoothedLogDerivIntegrand K x χ s‖ ≤
      (x : ℝ) ^ s.re *
          (s.re⁻¹ *
            ((1 + (s.im /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        (data.cLogDeriv *
          ((q : ℝ) ^ ((1 : ℝ) / 300) +
            Real.log ((q : ℝ) * (|s.im| + 2)) + 1) ^ 2) := by
  have hsrepr : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := by
    apply Complex.ext <;> simp
  have hk := norm_bvSmoothingMellinKernel_le_quartic
    K hx hlarge hspos s.im
  rw [hsrepr] at hk
  have hL := data.logDeriv_bound q inferInstance χ hq hχ s hregion
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxnorm : ‖(x : ℂ) ^ s‖ = (x : ℝ) ^ s.re := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.norm_cpow_eq_rpow_re_of_pos hxpos s)
  unfold bvSmoothedLogDerivIntegrand
  simp only [norm_neg, norm_mul]
  rw [hxnorm]
  calc
    (x : ℝ) ^ s.re *
          ‖Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x) s‖ *
        ‖deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s‖ ≤
      (x : ℝ) ^ s.re *
          (s.re⁻¹ *
            ((1 + (s.im /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        ‖deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s‖ := by
      gcongr
    _ ≤ _ := by
      gcongr

/-- Uniform pointwise bound on the shifted `gamma`-line up to height
`T`. -/
theorem norm_bvSmoothedLogDerivIntegrand_gamma_le_classical
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T ν : ℝ} (hν : |ν| ≤ T)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q ν) :
    ‖bvSmoothedLogDerivIntegrand K x χ
        (Chen.lemma6Equation21Point x ν)‖ ≤
      2 * (x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.eq21ClassicalLogDerivMajorant data q T := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hγpositive : 0 < γ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hγpos
  have hhalf : 1 -
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q ν / 2 ≤ γ := by
    have htwo : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwo] at hwidth
    dsimp only [γ]
    linarith
  have hregion : 1 -
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q
        (Chen.lemma6Equation21Point x ν).im / 2 ≤
      (Chen.lemma6Equation21Point x ν).re := by
    simpa only [Chen.lemma6Equation21Point_re,
      Chen.lemma6Equation21Point_im, γ] using hhalf
  have hraw := norm_bvSmoothedLogDerivIntegrand_le_classical
    data K hq hx hlarge hχ (Chen.lemma6Equation21Point x ν)
      (by simpa only [Chen.lemma6Equation21Point_re, γ] using hγpositive)
      hregion
  have hγinv : γ⁻¹ ≤ 2 := by
    have := (inv_le_inv₀ hγpositive
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr hγpos
    rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at this
  have hquartic :
      ((1 + (ν /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤ 1 := by
    have hbase : (1 : ℝ) ≤
        (1 + (ν /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2 := by
      nlinarith [sq_nonneg
        (ν / Real.log (x : ℝ) ^ (11 * (K + 1))),
        sq_nonneg (1 +
          (ν / Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2)]
    exact inv_le_one_of_one_le₀ hbase
  have hkernel : γ⁻¹ *
      ((1 + (ν /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤ 2 := by
    calc
      γ⁻¹ *
          ((1 + (ν /
            Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤
        2 * 1 := mul_le_mul hγinv hquartic (by positivity) (by positivity)
      _ = 2 := by ring
  have hargpos : 0 < (q : ℝ) * (|ν| + 2) := by positivity
  have hargle : (q : ℝ) * (|ν| + 2) ≤ (q : ℝ) * (T + 2) := by
    gcongr
  have hlogle : Real.log ((q : ℝ) * (|ν| + 2)) ≤
      Real.log ((q : ℝ) * (T + 2)) :=
    Real.log_le_log hargpos hargle
  have hbase0 : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / 300) +
      Real.log ((q : ℝ) * (|ν| + 2)) + 1 := by
    have := Chen.primitiveZeroFreeHeightLog_pos hq ν
    positivity
  have hbasele : (q : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((q : ℝ) * (|ν| + 2)) + 1 ≤
      (q : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((q : ℝ) * (T + 2)) + 1 := by linarith
  have hM : data.cLogDeriv *
        ((q : ℝ) ^ ((1 : ℝ) / 300) +
          Real.log ((q : ℝ) * (|ν| + 2)) + 1) ^ 2 ≤
      Chen.eq21ClassicalLogDerivMajorant data q T := by
    unfold Chen.eq21ClassicalLogDerivMajorant
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbasele 2) data.cLogDeriv_pos.le
  rw [Chen.lemma6Equation21Point_re,
    Chen.lemma6Equation21Point_im] at hraw
  change ‖bvSmoothedLogDerivIntegrand K x χ
      (Chen.lemma6Equation21Point x ν)‖ ≤ 2 * (x : ℝ) ^ γ *
        Chen.eq21ClassicalLogDerivMajorant data q T
  exact hraw.trans (by
    calc
      (x : ℝ) ^ γ *
            (γ⁻¹ *
              ((1 + (ν /
                Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
          (data.cLogDeriv *
            ((q : ℝ) ^ ((1 : ℝ) / 300) +
              Real.log ((q : ℝ) * (|ν| + 2)) + 1) ^ 2) ≤
        (x : ℝ) ^ γ * 2 *
          Chen.eq21ClassicalLogDerivMajorant data q T := by
        gcongr
        exact mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _)
      _ = 2 * (x : ℝ) ^ γ *
          Chen.eq21ClassicalLogDerivMajorant data q T := by ring)

/-- The finite shifted vertical segment has the expected
`T * x^gamma * M(q,T)` bound. -/
theorem norm_intervalIntegral_bvSmoothedLogDeriv_gamma_le_classical
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ ν : ℝ, |ν| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q ν) :
    ‖∫ ν : ℝ in (-T)..T,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6Equation21Point x ν)‖ ≤
      4 * T * ((x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.eq21ClassicalLogDerivMajorant data q T) := by
  let C : ℝ := 2 * (x : ℝ) ^
      (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.eq21ClassicalLogDerivMajorant data q T
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg x) _))
      (Chen.eq21ClassicalLogDerivMajorant_nonneg data q T)
  have hmain :
      ‖∫ ν : ℝ in (-T)..T,
          bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6Equation21Point x ν)‖ ≤ C * |T - (-T)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro ν hνmem
    rw [Set.uIoc_of_le (by linarith)] at hνmem
    have hν : |ν| ≤ T := abs_le.mpr ⟨hνmem.1.le, hνmem.2⟩
    exact norm_bvSmoothedLogDerivIntegrand_gamma_le_classical
      data K hq hx hlarge hγpos hχ hν (hwidth ν hν)
  calc
    ‖∫ ν : ℝ in (-T)..T,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6Equation21Point x ν)‖ ≤ C * |T - (-T)| := hmain
    _ = 4 * T * ((x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.eq21ClassicalLogDerivMajorant data q T) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]
      dsimp only [C]
      ring

/-- Uniform pointwise bound on either horizontal edge. -/
theorem norm_bvSmoothedLogDerivIntegrand_horizontal_le_classical
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T τ σ : ℝ} (hτ : |τ| = T)
    (hσ : σ ∈ Set.Icc
      (1 - 1 / Real.sqrt (Real.log (x : ℝ)))
      (1 + 1 / Real.log (x : ℝ)))
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q τ) :
    ‖bvSmoothedLogDerivIntegrand K x χ
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (2 * Real.exp 1 * (x : ℝ) *
        Chen.eq21ClassicalLogDerivMajorant data q T) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσhalf : (1 : ℝ) / 2 ≤ σ := hγpos.trans hσ.1
  have hσpos : 0 < σ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hσhalf
  have hhalf : 1 -
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q τ / 2 ≤ σ := by
    have htwo : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwo] at hwidth
    linarith [hσ.1]
  have hraw := norm_bvSmoothedLogDerivIntegrand_le_classical
    data K hq hx hlarge hχ ((σ : ℂ) + (τ : ℂ) * Complex.I)
      (by simpa using hσpos) (by simpa using hhalf)
  have hxone : (1 : ℝ) ≤ x := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxne : (x : ℝ) ≠ 1 := by
    exact_mod_cast (show x ≠ 1 by omega)
  have hxpow : (x : ℝ) ^ σ ≤ Real.exp 1 * (x : ℝ) := by
    calc
      (x : ℝ) ^ σ ≤
          (x : ℝ) ^ (1 + 1 / Real.log (x : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hxone hσ.2
      _ = Real.exp 1 * (x : ℝ) := by
        rw [Real.rpow_add hxpos, Real.rpow_one,
          show (1 : ℝ) / Real.log (x : ℝ) =
            (Real.log (x : ℝ))⁻¹ from one_div _,
          Real.rpow_inv_log hxpos hxne]
        ring
  have hσinv : σ⁻¹ ≤ 2 := by
    have := (inv_le_inv₀ hσpos
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr hσhalf
    rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at this
  rw [show (((σ : ℂ) + (τ : ℂ) * Complex.I).re) = σ by simp,
    show (((σ : ℂ) + (τ : ℂ) * Complex.I).im) = τ by simp] at hraw
  rw [hτ] at hraw
  unfold Chen.eq21ClassicalLogDerivMajorant
  have hM0 : 0 ≤ data.cLogDeriv *
      ((q : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2 :=
    mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _)
  have hQ0 : 0 ≤
      ((1 + (τ /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
    positivity
  calc
    ‖bvSmoothedLogDerivIntegrand K x χ
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (x : ℝ) ^ σ *
          (σ⁻¹ *
            ((1 + (τ /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        (data.cLogDeriv *
          ((q : ℝ) ^ ((1 : ℝ) / 300) +
            Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2) := hraw
    _ ≤ (Real.exp 1 * (x : ℝ)) * (2 *
          ((1 + (τ /
            Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        (data.cLogDeriv *
          ((q : ℝ) ^ ((1 : ℝ) / 300) +
            Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2) := by
      gcongr
    _ = (2 * Real.exp 1 * (x : ℝ) *
          (data.cLogDeriv *
            ((q : ℝ) ^ ((1 : ℝ) / 300) +
              Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2)) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by ring

/-- Each horizontal side is its pointwise bound times the exact width
`alpha - gamma`. -/
theorem norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_le_classical
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T τ : ℝ} (hτ : |τ| = T)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q τ) :
    ‖∫ σ : ℝ in
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))..
          (1 + 1 / Real.log (x : ℝ)),
        bvSmoothedLogDerivIntegrand K x χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q T) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by
  let C : ℝ := (2 * Real.exp 1 * (x : ℝ) *
      Chen.eq21ClassicalLogDerivMajorant data q T) *
    ((1 + (τ /
      Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσmem
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hγα : 1 - 1 / Real.sqrt (Real.log (x : ℝ)) ≤
      1 + 1 / Real.log (x : ℝ) := by
    have h1 : 0 ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by positivity
    have h2 : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hσ : σ ∈ Set.Icc
      (1 - 1 / Real.sqrt (Real.log (x : ℝ)))
      (1 + 1 / Real.log (x : ℝ)) := by
    rw [← Set.uIcc_of_le hγα]
    exact Set.uIoc_subset_uIcc hσmem
  exact norm_bvSmoothedLogDerivIntegrand_horizontal_le_classical
    data K hq hx hlarge hγpos hχ hτ hσ hwidth

/-- At the chosen square-scale height, either horizontal side gains the
factor `(log x)^(-44(K+1))`. -/
theorem norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_at_height_le
    (data : Chen.PrimitiveZeroFreeRegionData)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {τ : ℝ} (hτ : |τ| = bvSmoothingContourHeight K x)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q τ) :
    ‖∫ σ : ℝ in
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))..
          (1 + 1 / Real.log (x : ℝ)),
        bvSmoothedLogDerivIntegrand K x χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by
  let a : ℝ := Real.log (x : ℝ) ^ (11 * (K + 1))
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have ha : 0 < a := by dsimp only [a]; exact pow_pos hlog _
  have hheight : bvSmoothingContourHeight K x = a ^ 2 := rfl
  have hτa : |τ| = a ^ 2 := by rwa [hheight] at hτ
  have hqtail := scaled_quartic_at_sq_le_inv_four ha hτa
  have hbase :=
    norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_le_classical
      data K hq hx hlarge hγpos hχ hτ hwidth
  apply hbase.trans
  have hC0 : 0 ≤ 2 * Real.exp 1 * (x : ℝ) *
      Chen.eq21ClassicalLogDerivMajorant data q
        (bvSmoothingContourHeight K x) := by
    unfold Chen.eq21ClassicalLogDerivMajorant
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le)
        (Nat.cast_nonneg x))
      (mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _))
  have hwidth0 : 0 ≤ |(1 + 1 / Real.log (x : ℝ)) -
      (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := abs_nonneg _
  have ha4 : a ^ 4 = Real.log (x : ℝ) ^ (44 * (K + 1)) := by
    dsimp only [a]
    rw [← pow_mul]
    congr 1
    omega
  calc
    ((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) * (a ^ 4)⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by
      gcongr
    _ = ((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by rw [ha4]

/-- On the original `alpha`-line the logarithmic derivative is controlled
by absolute convergence, so this bound is independent of every zero-free
region and of primitivity. -/
theorem norm_bvSmoothedLogDerivIntegrand_alpha_le
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) (ν : ℝ) :
    ‖bvSmoothedLogDerivIntegrand K x χ
        (Chen.lemma6AlphaPoint x ν)‖ ≤
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((1 + (ν /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  have hαpos : 0 < α := by dsimp only [α]; positivity
  have hαone : 1 ≤ α := by
    dsimp only [α]
    have : 0 ≤ (1 : ℝ) / Real.log (x : ℝ) := by positivity
    linarith
  have ex : ‖(x : ℂ) ^ Chen.lemma6AlphaPoint x ν‖ =
      Real.exp 1 * (x : ℝ) :=
    Chen.norm_nat_cpow_eq21AlphaPoint hx ν
  have ek : ‖Chen.lemma6SmoothingMellinKernel
        (bvSmoothingParameter K x) (Chen.lemma6AlphaPoint x ν)‖ ≤
      ((1 + (ν /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
    have hk := norm_bvSmoothingMellinKernel_le_quartic
      K hx hlarge hαpos ν
    have hαinv : α⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hαone
    change ‖Chen.lemma6SmoothingMellinKernel
      (bvSmoothingParameter K x)
      ((α : ℂ) + (ν : ℂ) * Complex.I)‖ ≤ _
    exact hk.trans (by
      calc
        α⁻¹ *
            ((1 + (ν /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤
          1 *
            ((1 + (ν /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hαinv (by positivity)
        _ = _ := one_mul _)
  have eL :
      ‖deriv (DirichletCharacter.LFunction χ)
            (Chen.lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ
            (Chen.lemma6AlphaPoint x ν)‖ ≤
        4 * Real.log (x : ℝ) ^ 2 :=
    (Chen.lemma6_norm_logDeriv_le_majorant χ
      (Chen.one_lt_lemma6AlphaPoint_re hx ν)).trans
        (Chen.lemma6LogDerivMajorant_alpha_le hx ν)
  unfold bvSmoothedLogDerivIntegrand
  simp only [norm_neg, norm_mul]
  have hfirst := mul_le_mul ex.le ek (norm_nonneg _) (by positivity)
  have hall := mul_le_mul hfirst eL (norm_nonneg _) (by positivity)
  exact hall.trans_eq (by ring)

/-- Direct bound for the discarded tails of the original `alpha`-line.
The right side retains the truncation factor, so choosing `T` much larger
than the Mellin scale produces an arbitrary logarithmic saving. -/
theorem norm_integral_bvSmoothedLogDeriv_alpha_compl_Ioc_le
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x ν)‖ ≤
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((1 + (T /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2)⁻¹) *
        (Real.log (x : ℝ) ^ (11 * (K + 1)) * Real.pi) := by
  let a : ℝ := Real.log (x : ℝ) ^ (11 * (K + 1))
  let C : ℝ := 4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2
  let g : ℝ → ℝ := fun ν => ((1 + (ν / a) ^ 2) ^ 2)⁻¹
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have ha : 0 < a := by
    dsimp only [a]
    exact pow_pos hlog _
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hg : MeasureTheory.Integrable g := by
    simpa only [g] using integrable_scaled_quartic ha
  have hmajor : MeasureTheory.Integrable (fun ν => C * g ν) :=
    hg.const_mul C
  have hmain :
      ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
          bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6AlphaPoint x ν)‖ ≤
        ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, C * g ν := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor.integrableOn
    filter_upwards with ν
    exact norm_bvSmoothedLogDerivIntegrand_alpha_le
      K hx hlarge χ ν
  have htail := integral_scaled_quartic_compl_Ioc_le ha hT
  calc
    ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x ν)‖ ≤
        ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, C * g ν := hmain
    _ = C * (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, g ν) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ C * ((1 + (T / a) ^ 2)⁻¹ * (a * Real.pi)) :=
      mul_le_mul_of_nonneg_left (by simpa only [g] using htail) hC0
    _ = (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((1 + (T /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2)⁻¹) *
        (Real.log (x : ℝ) ^ (11 * (K + 1)) * Real.pi) := by
      dsimp only [C, a]
      ring

/-- At the chosen square-scale contour height, the original-line tail
loses one inverse Mellin scale, namely `(log x)^(-11(K+1))`. -/
theorem norm_integral_bvSmoothedLogDeriv_alpha_tail_le
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    ‖∫ ν : ℝ in
        (Set.Ioc (-(bvSmoothingContourHeight K x))
          (bvSmoothingContourHeight K x))ᶜ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x ν)‖ ≤
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) := by
  let a : ℝ := Real.log (x : ℝ) ^ (11 * (K + 1))
  let C : ℝ := 4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have ha : 0 < a := by dsimp only [a]; exact pow_pos hlog _
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hbase := norm_integral_bvSmoothedLogDeriv_alpha_compl_Ioc_le
    K hx hlarge χ (bvSmoothingContourHeight_nonneg K x)
  have hheight : bvSmoothingContourHeight K x = a ^ 2 := by
    rfl
  have hratio : a ^ 2 / a = a := by field_simp [ha.ne']
  have hcore : (1 + a ^ 2)⁻¹ * a ≤ a⁻¹ := by
    field_simp [ha.ne']
    nlinarith [sq_nonneg a]
  have htail :
      (1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹ *
          (a * Real.pi) ≤ a⁻¹ * Real.pi := by
    rw [hheight, hratio]
    calc
      (1 + a ^ 2)⁻¹ * (a * Real.pi) =
          ((1 + a ^ 2)⁻¹ * a) * Real.pi := by ring
      _ ≤ a⁻¹ * Real.pi :=
        mul_le_mul_of_nonneg_right hcore Real.pi_pos.le
  apply hbase.trans
  change C *
      ((1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹) *
        (a * Real.pi) ≤ C * (a⁻¹ * Real.pi)
  calc
    C * ((1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹) *
          (a * Real.pi) =
        C * (((1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹) *
          (a * Real.pi)) := by ring
    _ ≤ C * (a⁻¹ * Real.pi) :=
      mul_le_mul_of_nonneg_left htail hC0

end Chen.BombieriVinogradov
