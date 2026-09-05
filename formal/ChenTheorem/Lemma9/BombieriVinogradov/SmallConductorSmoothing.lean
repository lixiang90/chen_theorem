import ChenTheorem.Lemma9.BombieriVinogradov.SmallConductorPerron

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Adjustable smoothing for the small-conductor range

The fixed smoothing parameter used in Lemma 6 has transition width
`(log x)^(-1/10)`, which is not enough for the arbitrary logarithmic saving
in Bombieri--Vinogradov.  We do not need a second Mellin-inversion proof:
the existing function `Chen.chenPhi R` accepts an arbitrary positive real
parameter `R`.  Taking

`R = exp ((log x) ^ (10 * (K + 1)))`

makes its transition width `(log x)^(-(K+1))`, while retaining the same
high-order rational Mellin kernel already formalized for Lemma 6.
-/

/-- Auxiliary real parameter fed to Chen's existing smoothing function. -/
noncomputable def bvSmoothingParameter (K x : ℕ) : ℝ :=
  Real.exp (Real.log (x : ℝ) ^ (10 * (K + 1)))

theorem log_bvSmoothingParameter (K x : ℕ) :
    Real.log (bvSmoothingParameter K x) =
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
  unfold bvSmoothingParameter
  rw [Real.log_exp]

theorem one_lt_bvSmoothingParameter
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    1 < bvSmoothingParameter K x := by
  rw [bvSmoothingParameter, Real.one_lt_exp_iff]
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  exact pow_pos hlog _

/-- The `-1/10` transition exponent of Chen's smoothing function becomes
the freely chosen logarithmic exponent `-(K+1)`. -/
theorem log_bvSmoothingParameter_rpow_neg_tenth
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    Real.log (bvSmoothingParameter K x) ^ (-(0.1 : ℝ)) =
      Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [log_bvSmoothingParameter]
  calc
    (Real.log (x : ℝ) ^ (10 * (K + 1))) ^ (-(0.1 : ℝ)) =
        (Real.log (x : ℝ) ^ ((10 * (K + 1) : ℕ) : ℝ)) ^
          (-(0.1 : ℝ)) := by
            rw [Real.rpow_natCast]
    _ = Real.log (x : ℝ) ^
          (((10 * (K + 1) : ℕ) : ℝ) * (-(0.1 : ℝ))) :=
      (Real.rpow_mul hlog.le _ _).symm
    _ = Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) := by
      congr 1
      push_cast
      norm_num
      ring

/-- The adjustable cutoff attached to the summand indexed by `n`. -/
noncomputable def bvSmoothingWeight (K x n : ℕ) : ℝ :=
  Chen.chenPhi (bvSmoothingParameter K x) ((x : ℝ) / (n : ℝ))

/-- Smoothed twisted Chebyshev sum.  The finite range is retained here so
that approximation to the original sharp sum is purely algebraic. -/
noncomputable def bvSmoothedTwistedPsi {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
      (bvSmoothingWeight K x n : ℂ)

theorem bvSmoothingWeight_nonneg
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) :
    0 ≤ bvSmoothingWeight K x n := by
  unfold bvSmoothingWeight
  exact Chen.chenPhi_nonneg _ (one_lt_bvSmoothingParameter K hx)
    (by positivity)

theorem bvSmoothingWeight_le_one
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) :
    bvSmoothingWeight K x n ≤ 1 := by
  unfold bvSmoothingWeight
  exact Chen.chenPhi_le_one _ (one_lt_bvSmoothingParameter K hx)
    (by positivity)

/-- At and to the right of the sharp endpoint the adjustable weight is
identically zero. -/
theorem bvSmoothingWeight_eq_zero_of_le
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) (hn : 1 ≤ n) (hxn : x ≤ n) :
    bvSmoothingWeight K x n = 0 := by
  unfold bvSmoothingWeight
  apply Chen.chenPhi_eq_zero (one_lt_bvSmoothingParameter K hx)
  · positivity
  · exact (div_le_one (by exact_mod_cast (show 0 < n by omega))).2
      (by exact_mod_cast hxn)

/-- Exact algebraic form of the smoothing error. -/
theorem twistedPsi_sub_bvSmoothedTwistedPsi {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedPsi x χ - bvSmoothedTwistedPsi K x χ =
      ∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (1 - bvSmoothingWeight K x n : ℂ) := by
  unfold twistedPsi bvSmoothedTwistedPsi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The character contributes no loss to the elementary smoothing error. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_le {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (χ : DirichletCharacter ℂ q) :
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
      ∑ n ∈ Finset.Icc 1 x,
        ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) := by
  rw [twistedPsi_sub_bvSmoothedTwistedPsi]
  calc
    ‖∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (1 - bvSmoothingWeight K x n : ℂ)‖ ≤
      ∑ n ∈ Finset.Icc 1 x,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (1 - bvSmoothingWeight K x n : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 x,
        ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) := by
      apply Finset.sum_le_sum
      intro n _
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hw0 := bvSmoothingWeight_nonneg K hx (n := n)
      have hw1 := bvSmoothingWeight_le_one K hx (n := n)
      have hΛnorm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
          ArithmeticFunction.vonMangoldt n := by
        rw [Complex.norm_real, Real.norm_of_nonneg hΛ]
      have hwnorm : ‖(1 - bvSmoothingWeight K x n : ℂ)‖ =
          1 - bvSmoothingWeight K x n := by
        rw [show (1 - bvSmoothingWeight K x n : ℂ) =
          ((1 - bvSmoothingWeight K x n : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real,
          Real.norm_of_nonneg (sub_nonneg.mpr hw1)]
      rw [norm_mul, norm_mul, hΛnorm, hwnorm]
      calc
        ArithmeticFunction.vonMangoldt n * ‖χ n‖ *
            (1 - bvSmoothingWeight K x n) ≤
          ArithmeticFunction.vonMangoldt n * 1 *
            (1 - bvSmoothingWeight K x n) := by
              gcongr
              exact χ.norm_le_one n
        _ = _ := by ring

/-- In the deep interior, Lemma 1 gives a power-small smoothing error.
The later asymptotic layer rewrites the displayed threshold in terms of
`(log x)^(-(K+1))`. -/
theorem one_sub_bvSmoothingWeight_le
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (bvSmoothingParameter K x))
    (hdeep : Real.exp
        (2 * Real.log (bvSmoothingParameter K x) ^ (-(0.1 : ℝ))) ≤
      (x : ℝ) / (n : ℝ)) :
    1 - bvSmoothingWeight K x n ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) := by
  unfold bvSmoothingWeight
  have hphi := Chen.chenPhi_ge
    (one_lt_bvSmoothingParameter K hx) hlarge hdeep
  linarith

/-- Same interior estimate with the transition width displayed directly
as the chosen power of `log x`. -/
theorem one_sub_bvSmoothingWeight_le_log_width
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hdeep : Real.exp
        (2 * Real.log (x : ℝ) ^ (-(K + 1 : ℝ))) ≤
      (x : ℝ) / (n : ℝ)) :
    1 - bvSmoothingWeight K x n ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) := by
  apply one_sub_bvSmoothingWeight_le K hx
  · rwa [log_bvSmoothingParameter]
  · rwa [log_bvSmoothingParameter_rpow_neg_tenth K hx]

end Chen.BombieriVinogradov
