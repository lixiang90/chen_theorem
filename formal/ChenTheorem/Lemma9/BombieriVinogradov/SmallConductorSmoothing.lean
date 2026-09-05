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

/-- Multiplicative transition width of the adjustable smoothing. -/
noncomputable def bvSmoothingBoundaryRatio (K x : ℕ) : ℝ :=
  Real.exp (2 * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)))

/-- Polylogarithmic contour height chosen as the square of the adjustable
Mellin scale. -/
noncomputable def bvSmoothingContourHeight (K x : ℕ) : ℝ :=
  (Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2

theorem bvSmoothingContourHeight_nonneg (K x : ℕ) :
    0 ≤ bvSmoothingContourHeight K x := by
  unfold bvSmoothingContourHeight
  positivity

/-- Indices in the short interval next to `x` on which Lemma 1 does not
yet force the smoothing weight to be power-close to one. -/
noncomputable def bvSmoothingBoundaryIndices (K x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n =>
    (x : ℝ) / (n : ℝ) < bvSmoothingBoundaryRatio K x

@[simp]
theorem mem_bvSmoothingBoundaryIndices {K x n : ℕ} :
    n ∈ bvSmoothingBoundaryIndices K x ↔
      n ∈ Finset.Icc 1 x ∧
        (x : ℝ) / (n : ℝ) < bvSmoothingBoundaryRatio K x := by
  simp [bvSmoothingBoundaryIndices]

/-- Smoothed twisted Chebyshev sum.  The finite range is retained here so
that approximation to the original sharp sum is purely algebraic. -/
noncomputable def bvSmoothedTwistedPsi {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
      (bvSmoothingWeight K x n : ℂ)

/-- Finite Mellin integrand whose vertical integral is the adjustable
smoothed twisted Chebyshev sum. -/
noncomputable def bvSmoothedTwistedPsiFiniteIntegrand {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
      (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
        Chen.lemma6SmoothingMellinKernel
          (bvSmoothingParameter K x) s)

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

theorem bvSmoothingScale_pos
    (K : ℕ) {x : ℕ}
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1))) :
    0 < Chen.lemma6SmoothingScale (bvSmoothingParameter K x) := by
  have hlogR : 1 ≤ Real.log (bvSmoothingParameter K x) := by
    rw [log_bvSmoothingParameter]
    exact (by norm_num : (1 : ℝ) ≤ 10 ^ 4).trans hlarge
  unfold Chen.lemma6SmoothingScale
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlogR) _

theorem bvSmoothingOrder_one_le
    (K : ℕ) {x : ℕ}
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1))) :
    1 ≤ Chen.lemma6SmoothingOrder (bvSmoothingParameter K x) := by
  have hlogR : 1 ≤ Real.log (bvSmoothingParameter K x) := by
    rw [log_bvSmoothingParameter]
    exact (by norm_num : (1 : ℝ) ≤ 10 ^ 4).trans hlarge
  unfold Chen.lemma6SmoothingOrder
  rw [Nat.one_le_floor_iff]
  exact hlogR

/-- The Mellin scale attached to the adjustable parameter is still a
plain power of `log x`; its exponent is `11 * (K+1)`. -/
theorem bvSmoothingScale_eq
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    Chen.lemma6SmoothingScale (bvSmoothingParameter K x) =
      Real.log (x : ℝ) ^ (11 * (K + 1)) := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  unfold Chen.lemma6SmoothingScale
  rw [log_bvSmoothingParameter]
  calc
    (Real.log (x : ℝ) ^ (10 * (K + 1))) ^ (1.1 : ℝ) =
        (Real.log (x : ℝ) ^ ((10 * (K + 1) : ℕ) : ℝ)) ^
          (1.1 : ℝ) := by rw [Real.rpow_natCast]
    _ = Real.log (x : ℝ) ^
          (((10 * (K + 1) : ℕ) : ℝ) * (1.1 : ℝ)) :=
      (Real.rpow_mul hlog.le _ _).symm
    _ = Real.log (x : ℝ) ^ (((11 * (K + 1) : ℕ) : ℝ)) := by
      congr 1
      push_cast
      norm_num
      ring
    _ = Real.log (x : ℝ) ^ (11 * (K + 1)) :=
      Real.rpow_natCast _ _

theorem bvSmoothingOrder_three_le
    (K : ℕ) {x : ℕ}
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1))) :
    3 ≤ Chen.lemma6SmoothingOrder (bvSmoothingParameter K x) := by
  have hlogR : (3 : ℝ) ≤ Real.log (bvSmoothingParameter K x) := by
    rw [log_bvSmoothingParameter]
    exact (by norm_num : (3 : ℝ) ≤ 10 ^ 4).trans hlarge
  unfold Chen.lemma6SmoothingOrder
  exact (Nat.le_floor_iff (show 0 ≤
    Real.log (bvSmoothingParameter K x) by linarith)).2 hlogR

/-- Quartic tail bound for the adjustable Mellin kernel, with its scale
displayed as a power of `log x`. -/
theorem norm_bvSmoothingMellinKernel_le_quartic
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) :
    ‖Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x)
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      σ⁻¹ *
        ((1 + (ν / Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
  simpa only [bvSmoothingScale_eq K hx] using
    (Chen.norm_lemma6SmoothingMellinKernel_le_quartic
      (bvSmoothingScale_pos K hlarge)
      (bvSmoothingOrder_three_le K hlarge) hσ ν)

/-- Mellin inversion for the adjustable weight.  This is a direct
specialization of the smoothing theorem already proved for Lemma 6, with
its parameter replaced by `bvSmoothingParameter K x`. -/
theorem bvSmoothingWeight_eq_smoothing_verticalIntegral
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) (hn : 1 ≤ n)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (σ : ℝ) (hσ : 0 < σ) :
    (bvSmoothingWeight K x n : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          ((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
              ((σ : ℂ) + (ν : ℂ) * Complex.I) *
            Chen.lemma6SmoothingMellinKernel
              (bvSmoothingParameter K x)
              ((σ : ℂ) + (ν : ℂ) * Complex.I)) := by
  have hy : 0 < (x : ℝ) / (n : ℝ) := by
    positivity
  unfold bvSmoothingWeight
  simpa only using
    (Chen.chenPhi_eq_smoothing_verticalIntegral
      (one_lt_bvSmoothingParameter K hx)
      (bvSmoothingScale_pos K hlarge)
      (bvSmoothingOrder_one_le K hlarge) hσ hy)

/-- Exact finite Mellin representation of the adjustable smoothed sum.
This is the bridge from the elementary smoothing-error estimates below to
the later logarithmic-derivative contour argument. -/
theorem bvSmoothedTwistedPsi_eq_finiteVerticalIntegral
    {q : ℕ} (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) (σ : ℝ) (hσ : 0 < σ) :
    bvSmoothedTwistedPsi K x χ =
      VerticalIntegral' (bvSmoothedTwistedPsiFiniteIntegrand K x χ) σ := by
  have hterm (n : ℕ) (hnmem : n ∈ Finset.Icc 1 x) :
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (bvSmoothingWeight K x n : ℂ) =
        VerticalIntegral' (fun s : ℂ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
              Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x) s)) σ := by
    have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
    rw [bvSmoothingWeight_eq_smoothing_verticalIntegral
      K hx hn hlarge σ hσ]
    unfold VerticalIntegral' VerticalIntegral
    simp only [smul_eq_mul, Complex.real_smul]
    rw [MeasureTheory.integral_const_mul]
    push_cast
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    simp only [mul_comm]
  unfold bvSmoothedTwistedPsi
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (bvSmoothingWeight K x n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 x,
        VerticalIntegral' (fun s : ℂ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
              Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x) s)) σ :=
      Finset.sum_congr rfl hterm
    _ = VerticalIntegral'
        (bvSmoothedTwistedPsiFiniteIntegrand K x χ) σ := by
      unfold bvSmoothedTwistedPsiFiniteIntegrand
      unfold VerticalIntegral' VerticalIntegral
      simp only [smul_eq_mul]
      rw [MeasureTheory.integral_finsetSum]
      · simp only [Finset.mul_sum]
      · intro n hnmem
        have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
        have hy : 0 < (x : ℝ) / (n : ℝ) := by positivity
        exact (Chen.integrable_cpow_mul_lemma6SmoothingMellinKernel
          hy (bvSmoothingScale_pos K hlarge)
          (bvSmoothingOrder_one_le K hlarge) hσ).const_mul _

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

/-- Quantitative smoothing-error split.  The deep part costs the tiny
power `R^(-1/10)` times `ψ(x)`; all remaining loss is confined to the
explicit short boundary interval. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_deep_add_boundary
    {q : ℕ} (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) * Chebyshev.psi x +
        ((bvSmoothingBoundaryIndices K x).card : ℝ) *
          Real.log (x : ℝ) := by
  let Rerr : ℝ := bvSmoothingParameter K x ^ (-(0.1 : ℝ))
  let L : ℝ := Real.log (x : ℝ)
  let S : Finset ℕ := Finset.Icc 1 x
  let B : Finset ℕ := bvSmoothingBoundaryIndices K x
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hR0 : 0 ≤ Rerr := by
    dsimp only [Rerr]
    exact Real.rpow_nonneg (Real.exp_pos _).le _
  have hpoint : ∀ n ∈ S,
      ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) ≤
        ArithmeticFunction.vonMangoldt n * Rerr +
          if n ∈ B then L else 0 := by
    intro n hn
    have hnData := Finset.mem_Icc.mp hn
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hΛL : ArithmeticFunction.vonMangoldt n ≤ L := by
      dsimp only [L]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hnData.2))
    by_cases hdeep : bvSmoothingBoundaryRatio K x ≤
        (x : ℝ) / (n : ℝ)
    · have herr : 1 - bvSmoothingWeight K x n ≤ Rerr := by
        dsimp only [Rerr]
        apply one_sub_bvSmoothingWeight_le_log_width K hx hlarge
        simpa only [bvSmoothingBoundaryRatio] using hdeep
      have hnB : n ∉ B := by
        dsimp only [B]
        rw [mem_bvSmoothingBoundaryIndices]
        exact fun h => (not_lt_of_ge hdeep) h.2
      rw [if_neg hnB, add_zero]
      exact mul_le_mul_of_nonneg_left herr hΛ0
    · have hnB : n ∈ B := by
        dsimp only [B]
        rw [mem_bvSmoothingBoundaryIndices]
        exact ⟨hn, lt_of_not_ge hdeep⟩
      rw [if_pos hnB]
      have hw0 := bvSmoothingWeight_nonneg K hx (n := n)
      have hone : 1 - bvSmoothingWeight K x n ≤ 1 := by linarith
      calc
        ArithmeticFunction.vonMangoldt n *
              (1 - bvSmoothingWeight K x n) ≤
            ArithmeticFunction.vonMangoldt n * 1 :=
          mul_le_mul_of_nonneg_left hone hΛ0
        _ ≤ ArithmeticFunction.vonMangoldt n * Rerr + L := by
          nlinarith [mul_nonneg hΛ0 hR0]
  have hbase := norm_twistedPsi_sub_bvSmoothedTwistedPsi_le K hx χ
  calc
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) := by
            simpa only [S] using hbase
    _ ≤ ∑ n ∈ S,
        (ArithmeticFunction.vonMangoldt n * Rerr +
          if n ∈ B then L else 0) := Finset.sum_le_sum hpoint
    _ = Rerr * Chebyshev.psi x + (B.card : ℝ) * L := by
      rw [Finset.sum_add_distrib]
      have hpsi : (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) =
          Chebyshev.psi x := by
        dsimp only [S]
        rw [Chebyshev.psi_eq_sum_Icc]
        simp only [Nat.floor_natCast]
        apply Finset.sum_subset
        · intro n hn
          exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hn).2⟩
        · intro n hn hnnot
          have hnData := Finset.mem_Icc.mp hn
          have hn0 : n = 0 := by
            by_contra hnne
            exact hnnot (Finset.mem_Icc.mpr
              ⟨Nat.one_le_iff_ne_zero.mpr hnne, hnData.2⟩)
          subst n
          simp
      rw [← Finset.sum_mul, hpsi]
      have hBsub : B ⊆ S := by
        intro n hn
        dsimp only [B, S] at hn ⊢
        exact (mem_bvSmoothingBoundaryIndices.mp hn).1
      have hboundary :
          (∑ n ∈ S, if n ∈ B then L else 0) = (B.card : ℝ) * L := by
        calc
          (∑ n ∈ S, if n ∈ B then L else 0) =
              ∑ n ∈ B, if n ∈ B then L else 0 := by
            symm
            apply Finset.sum_subset hBsub
            intro n _ hnB
            rw [if_neg hnB]
          _ = (B.card : ℝ) * L := by simp
      rw [hboundary]
      ring
    _ = _ := by rfl

/-- The transition layer next to `x` contains only
`O(x * (log x)^(-(K+1)))` integers.  This is the elementary counting
estimate which turns the pointwise smoothing estimate into an arbitrary
logarithmic saving. -/
theorem card_bvSmoothingBoundaryIndices_le
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    ((bvSmoothingBoundaryIndices K x).card : ℝ) ≤
      2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1 := by
  let δ : ℝ := Real.log (x : ℝ) ^ (-(K + 1 : ℝ))
  let R : ℝ := Real.exp (2 * δ)
  let a : ℕ := ⌊(x : ℝ) / R⌋₊
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    exact Real.rpow_nonneg (Real.log_pos
      (by exact_mod_cast (show 1 < x by omega))).le _
  have hRpos : 0 < R := by
    dsimp only [R]
    positivity
  have hRone : 1 ≤ R := by
    dsimp only [R]
    exact Real.one_le_exp (by positivity)
  have hquot0 : 0 ≤ (x : ℝ) / R := div_nonneg hx0 hRpos.le
  have hquotx : (x : ℝ) / R ≤ x := div_le_self hx0 hRone
  have hax : a ≤ x := by
    dsimp only [a]
    exact Nat.floor_le_of_le hquotx
  have hsubset : bvSmoothingBoundaryIndices K x ⊆ Finset.Ioc a x := by
    intro n hn
    have hnData := mem_bvSmoothingBoundaryIndices.mp hn
    have hnIcc := Finset.mem_Icc.mp hnData.1
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hratio : (x : ℝ) / (n : ℝ) < R := by
      simpa only [R, bvSmoothingBoundaryRatio, δ] using hnData.2
    have hxlt : (x : ℝ) < R * (n : ℝ) :=
      (div_lt_iff₀ hnpos).mp hratio
    have hquotlt : (x : ℝ) / R < n := by
      apply (div_lt_iff₀ hRpos).2
      simpa only [mul_comm] using hxlt
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hquot0).2 hquotlt, hnIcc.2⟩
  have hcardNat := Finset.card_le_card hsubset
  have hcard : ((bvSmoothingBoundaryIndices K x).card : ℝ) ≤
      ((Finset.Ioc a x).card : ℝ) := by exact_mod_cast hcardNat
  rw [Nat.card_Ioc, Nat.cast_sub hax] at hcard
  have hfloor : (x : ℝ) / R < (a : ℝ) + 1 := by
    dsimp only [a]
    exact Nat.lt_floor_add_one _
  have hcount : (x : ℝ) - (a : ℝ) ≤ (x : ℝ) - (x : ℝ) / R + 1 := by
    linarith
  have hexp : 1 - Real.exp (-2 * δ) ≤ 2 * δ := by
    have := Real.add_one_le_exp (-2 * δ)
    linarith
  have hRinv : R⁻¹ = Real.exp (-2 * δ) := by
    dsimp only [R]
    rw [← Real.exp_neg]
    congr 1
    ring
  have hlast : (x : ℝ) - (x : ℝ) / R + 1 ≤
      2 * (x : ℝ) * δ + 1 := by
    rw [div_eq_mul_inv, hRinv]
    have hmul := mul_le_mul_of_nonneg_left hexp hx0
    nlinarith
  exact hcard.trans (hcount.trans (by simpa only [δ] using hlast))

/-- Fully explicit adjustable smoothing error.  Its first term is
super-polynomially small in `log x`, while the second is visibly of size
`x * (log x)^(-K)` after multiplication by the endpoint logarithm. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_explicit
    {q : ℕ} (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) * Chebyshev.psi x +
        (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) := by
  have hsplit :=
    norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_deep_add_boundary
      K hx hlarge χ
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  exact hsplit.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right
      (card_bvSmoothingBoundaryIndices_le K hx) hlog0) _)

/-- Exact mass of the Cauchy envelope after rescaling its horizontal
variable. -/
theorem integral_scaled_cauchy
    {a : ℝ} (ha : 0 < a) :
    (∫ ν : ℝ, (1 + (ν / a) ^ 2)⁻¹) = a * Real.pi := by
  let g : ℝ → ℝ := fun u => (1 + u ^ 2)⁻¹
  have hscale :=
    MeasureTheory.Measure.integral_comp_mul_left g a⁻¹
  calc
    (∫ ν : ℝ, (1 + (ν / a) ^ 2)⁻¹) =
        ∫ ν : ℝ, g (a⁻¹ * ν) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ν
      dsimp only [g]
      rw [div_eq_inv_mul]
    _ = |(a⁻¹)⁻¹| * ∫ u : ℝ, g u := by
      simpa only [smul_eq_mul] using hscale
    _ = a * Real.pi := by
      rw [integral_univ_inv_one_add_sq]
      simp only [inv_inv, abs_of_pos ha]

theorem integrable_scaled_quartic
    {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun ν : ℝ =>
      ((1 + (ν / a) ^ 2) ^ 2)⁻¹) := by
  let h : ℝ → ℝ := fun ν => (1 + (ν / a) ^ 2)⁻¹
  have hh : MeasureTheory.Integrable h := by
    have hbase := integrable_inv_one_add_sq.comp_mul_left'
      (R := a⁻¹) (inv_ne_zero ha.ne')
    simpa only [h, div_eq_inv_mul] using hbase
  apply hh.mono
  · fun_prop
  · filter_upwards with ν
    have hu : 1 ≤ 1 + (ν / a) ^ 2 := by nlinarith [sq_nonneg (ν / a)]
    have huPos : 0 < 1 + (ν / a) ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by dsimp only [h]; positivity)]
    dsimp only [h]
    rw [pow_two, mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr huPos.le)
      (inv_le_one_of_one_le₀ hu)

/-- The quartic scaled kernel outside `[-T,T]` is bounded by one frozen
decay factor times the total mass of a scaled Cauchy kernel. -/
theorem integral_scaled_quartic_compl_Ioc_le
    {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        ((1 + (ν / a) ^ 2) ^ 2)⁻¹) ≤
      ((1 + (T / a) ^ 2)⁻¹) * (a * Real.pi) := by
  let g : ℝ → ℝ := fun ν => ((1 + (ν / a) ^ 2) ^ 2)⁻¹
  let h : ℝ → ℝ := fun ν => (1 + (ν / a) ^ 2)⁻¹
  let E : ℝ := (1 + (T / a) ^ 2)⁻¹
  have ha0 : a ≠ 0 := ha.ne'
  have hh : MeasureTheory.Integrable h := by
    have hbase := integrable_inv_one_add_sq.comp_mul_left'
      (R := a⁻¹) (inv_ne_zero ha0)
    simpa only [h, div_eq_inv_mul] using hbase
  have hg : MeasureTheory.Integrable g := by
    simpa only [g] using integrable_scaled_quartic ha
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hmajor : MeasureTheory.Integrable (fun ν => E * h ν) :=
    hh.const_mul E
  have hpoint : ∀ ν ∈ (Set.Ioc (-T) T)ᶜ, g ν ≤ E * h ν := by
    intro ν hνmem
    have hνlarge : T ≤ |ν| := by
      rw [Set.mem_compl_iff, Set.mem_Ioc] at hνmem
      by_cases hleft : ν ≤ -T
      · have : T ≤ -ν := by linarith
        exact this.trans_eq (abs_of_nonpos (by linarith)).symm
      · have hright : T < ν := by
          by_contra hnot
          exact hνmem ⟨lt_of_not_ge hleft, le_of_not_gt hnot⟩
        exact hright.le.trans (le_abs_self ν)
    have hsq : T ^ 2 ≤ ν ^ 2 := by
      rw [← sq_abs ν]
      nlinarith [sq_nonneg (|ν| - T)]
    have hdivsq : (T / a) ^ 2 ≤ (ν / a) ^ 2 := by
      rw [div_pow, div_pow]
      exact div_le_div_of_nonneg_right hsq (sq_nonneg a)
    have hu : 1 + (T / a) ^ 2 ≤ 1 + (ν / a) ^ 2 := by linarith
    have hinv : (1 + (ν / a) ^ 2)⁻¹ ≤
        (1 + (T / a) ^ 2)⁻¹ := by
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hu
    dsimp only [g, E, h]
    rw [pow_two, mul_inv]
    exact mul_le_mul_of_nonneg_right hinv (by positivity)
  calc
    (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, g ν) ≤
        ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, E * h ν := by
      apply MeasureTheory.integral_mono_ae hg.integrableOn
        hmajor.integrableOn
      filter_upwards [MeasureTheory.ae_restrict_mem
        measurableSet_Ioc.compl] with ν hνmem
      exact hpoint ν hνmem
    _ ≤ ∫ ν : ℝ, E * h ν := by
      exact MeasureTheory.integral_mono_measure
        MeasureTheory.Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun ν => by
          exact mul_nonneg hE0 (by dsimp only [h]; positivity))) hmajor
    _ = E * (a * Real.pi) := by
      rw [MeasureTheory.integral_const_mul, integral_scaled_cauchy ha]
    _ = ((1 + (T / a) ^ 2)⁻¹) * (a * Real.pi) := rfl

/-- At height `|tau| = a^2`, the quartic kernel contributes `a^-4`. -/
theorem scaled_quartic_at_sq_le_inv_four
    {a τ : ℝ} (ha : 0 < a) (hτ : |τ| = a ^ 2) :
    ((1 + (τ / a) ^ 2) ^ 2)⁻¹ ≤ (a ^ 4)⁻¹ := by
  have hτsq : τ ^ 2 = a ^ 4 := by
    rw [← sq_abs τ, hτ]
    ring
  have hratio : (τ / a) ^ 2 = a ^ 2 := by
    rw [div_pow, hτsq]
    field_simp [ha.ne']
  rw [hratio]
  have hden : a ^ 4 ≤ (1 + a ^ 2) ^ 2 := by
    nlinarith [sq_nonneg a, sq_nonneg (a ^ 2)]
  simpa only [one_div] using
    one_div_le_one_div_of_le (pow_pos ha 4) hden

end Chen.BombieriVinogradov
