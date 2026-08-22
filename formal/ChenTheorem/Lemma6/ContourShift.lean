/-
The finite-height contour shift for the `B` term in equation (17).

The infinite vertical-line identity used by Chen has two logically distinct
parts.  This file proves the Cauchy--Goursat identity on every finite
rectangle.  Passing to infinite height additionally requires the two
horizontal edge integrals to vanish; keeping that limit separate prevents
holomorphy alone from being mistaken for a growth estimate.
-/
import ChenTheorem.Lemma6.Parameters
import ChenTheorem.Lemma6.SmoothingMellin
import Mathlib.Analysis.Complex.CauchyIntegral

open Real Set MeasureTheory Filter Topology
open scoped Classical Interval

namespace Chen

/-- On the shifted line `β = 1/2 + 1 / log x`, the horizontal power has
constant modulus `e x^(1/2)`. -/
theorem norm_nat_cpow_lemma6BetaPoint
    {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    ‖(x : ℂ) ^ lemma6BetaPoint x ν‖ =
      Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
  have hxpos : (0 : ℝ) < x := by positivity
  have hxne : (x : ℝ) ≠ 1 := by
    exact_mod_cast (show x ≠ 1 by omega)
  change ‖((x : ℝ) : ℂ) ^ lemma6BetaPoint x ν‖ =
    Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
    lemma6BetaPoint_re, Real.rpow_add hxpos]
  have hinv : (1 : ℝ) / Real.log (x : ℝ) =
      (Real.log (x : ℝ))⁻¹ := one_div _
  rw [hinv, Real.rpow_inv_log hxpos hxne]
  ring

/-- The fourth power of Chen's smoothing scale is bounded by the fifth
integer power of `log x`. -/
theorem lemma6SmoothingScale_four_le_log_five
    {x : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6SmoothingScale (x : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ 5 := by
  let L : ℝ := Real.log (x : ℝ)
  have hL0 : 0 ≤ L := by dsimp only [L]; linarith
  have hL1 : 1 ≤ L := by exact hxlog
  calc
    lemma6SmoothingScale (x : ℝ) ^ 4 =
        (L ^ (1.1 : ℝ)) ^ (4 : ℝ) := by
      unfold lemma6SmoothingScale
      dsimp only [L]
      exact (Real.rpow_natCast _ 4).symm
    _ = L ^ ((1.1 : ℝ) * 4) :=
      (Real.rpow_mul hL0 (1.1 : ℝ) 4).symm
    _ ≤ L ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    _ = Real.log (x : ℝ) ^ 5 := by
      dsimp only [L]
      exact Real.rpow_natCast _ 5

/-- Chen's exact smoothing kernel retains a quartic tail after the contour
is moved to `β`; the factor `2` is the elementary bound `β⁻¹ ≤ 2`. -/
theorem norm_lemma6SmoothingMellinKernel_beta_le_two_mul_scale_four
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x ν)‖ ≤
      2 * lemma6SmoothingScale (x : ℝ) ^ 4 / (1 + ν ^ 4) := by
  let L : ℝ := Real.log (x : ℝ)
  let a : ℝ := lemma6SmoothingScale (x : ℝ)
  let σ : ℝ := 1 / 2 + 1 / L
  have hL : 0 < L := by dsimp only [L]; linarith
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hL _
  have ha1 : 1 ≤ a := by
    dsimp only [a, lemma6SmoothingScale, L]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hpoint : lemma6BetaPoint x ν =
      (σ : ℂ) + (ν : ℂ) * Complex.I := by
    unfold lemma6BetaPoint
    dsimp only [σ, L]
  have hk := norm_lemma6SmoothingMellinKernel_le_quartic
    ha hn hσ ν
  rw [← hpoint] at hk
  apply hk.trans
  have hσhalf : (1 / 2 : ℝ) ≤ σ := by
    dsimp only [σ]
    have : 0 ≤ (1 : ℝ) / L := by positivity
    linarith
  have hσinv : σ⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hσ (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact hσhalf
  have hdenpos : 0 < (1 + (ν / a) ^ 2) ^ 2 := by positivity
  have htargetpos : 0 < 1 + ν ^ 4 := by positivity
  have hscale :
      ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤
        a ^ 4 / (1 + ν ^ 4) := by
    rw [le_div_iff₀ htargetpos]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hdenpos).2
    field_simp [ha.ne']
    nlinarith [sq_nonneg ν, sq_nonneg (ν ^ 2),
      sq_nonneg (a ^ 2 - 1)]
  calc
    σ⁻¹ * ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤
        2 * ((1 + (ν / a) ^ 2) ^ 2)⁻¹ := by gcongr
    _ ≤ 2 * (a ^ 4 / (1 + ν ^ 4)) := by gcongr
    _ = 2 * a ^ 4 / (1 + ν ^ 4) := by ring

/-- Integer-log form of the `β`-line kernel bound used together with the
fourth-moment estimates. -/
theorem norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6BetaPoint x ν)‖ ≤
      2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4) := by
  exact
    (norm_lemma6SmoothingMellinKernel_beta_le_two_mul_scale_four hxlog ν).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (lemma6SmoothingScale_four_le_log_five (by linarith)) (by positivity))
        (by positivity))

/-- The complex `B` integrand before taking absolute values. -/
noncomputable def lemma6BContourIntegrand
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairBlockPolynomial x m k s χ *
      deriv (DirichletCharacter.LFunction χ) s *
      lemma6MollifierAt H s χ)

/-- The complex `A` integrand in equation (16), before absolute values are
taken.  It remains on the original `α`-line. -/
noncomputable def lemma6AContourIntegrand
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairBlockPolynomial x m k s χ *
      (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) *
      (1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ))

/-- The unsplit logarithmic-derivative integrand which comes directly from
Mellin inversion. -/
noncomputable def lemma6LogDerivContourIntegrand
    {d : ℕ} [NeZero d] (x m k : ℕ)
    (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairBlockPolynomial x m k s χ *
      (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s))

/-- Exact complex-valued equation-(16) split on the `α`-line.  In
particular, the contour move for `B` occurs before applying the triangle
inequality. -/
theorem lemma6LogDerivContourIntegrand_alpha_eq_A_add_B
    {d x : ℕ} [NeZero d] (hx : 2 ≤ x) (m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (ν : ℝ) :
    lemma6LogDerivContourIntegrand x m k χ (lemma6AlphaPoint x ν) =
      lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν) +
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν) := by
  let C : ℂ :=
    ((x : ℂ) ^ lemma6AlphaPoint x ν *
        lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)) *
      lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ
  let U : ℂ :=
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
      DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)
  let A : ℂ := U *
    (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
      lemma6MollifierAt H (lemma6AlphaPoint x ν) χ)
  let B : ℂ :=
    deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
      lemma6MollifierAt H (lemma6AlphaPoint x ν) χ
  have h16 : U = A + B := by
    simpa only [U, A, B] using
      lemma6_equation16_at_alpha (q := d) (H := H) hx ν χ
  have hmul : -(C * U) = -(C * (A + B)) :=
    congrArg (fun z : ℂ => -(C * z)) h16
  unfold lemma6LogDerivContourIntegrand lemma6AContourIntegrand
    lemma6BContourIntegrand
  calc
    -(↑x ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (↑x) (lemma6AlphaPoint x ν) *
          lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))) =
        -(C * U) := by rfl
    _ = -(C * (A + B)) := hmul
    _ = -(↑x ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (↑x) (lemma6AlphaPoint x ν) *
              lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
              (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
                DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)) *
              (1 - DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν) *
                lemma6MollifierAt H (lemma6AlphaPoint x ν) χ)) +
          -(↑x ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (↑x) (lemma6AlphaPoint x ν) *
              lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
              deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) *
              lemma6MollifierAt H (lemma6AlphaPoint x ν) χ) := by
      dsimp only [C, U, A, B]
      ring

/-- Pointwise norm majorant for the shifted complex `B` integrand.  This is
the exact product consumed by the pair, mollifier, and `L'` moment bounds. -/
theorem norm_lemma6BContourIntegrand_beta_le
    {d x : ℕ} [NeZero d] (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (ν : ℝ) :
    ‖lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)‖ ≤
      (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
        (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
        ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ *
        ‖deriv (DirichletCharacter.LFunction χ)
          (lemma6BetaPoint x ν)‖ *
        ‖lemma6MollifierAt H (lemma6BetaPoint x ν) χ‖ := by
  unfold lemma6BContourIntegrand
  simp only [norm_neg, norm_mul]
  rw [norm_nat_cpow_lemma6BetaPoint hx ν]
  gcongr
  exact norm_lemma6SmoothingMellinKernel_beta_le_two_mul_log_five hxlog ν

/-- For a primitive character of modulus at least two, the complete `B`
integrand is holomorphic throughout the right half-plane. -/
theorem differentiableOn_lemma6BContourIntegrand
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (m k H : ℕ) {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    DifferentiableOn ℂ (lemma6BContourIntegrand x m k H χ)
      {s : ℂ | 0 < s.re} := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 by omega)
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  have hk := differentiableOn_lemma6SmoothingMellinKernel
    (x := (x : ℝ)) (by exact_mod_cast (show 1 < x by omega))
  have hp : DifferentiableOn ℂ
      (fun s => lemma6PairBlockPolynomial x m k s χ) {s : ℂ | 0 < s.re} :=
    (differentiable_lemma6PairBlockPolynomial x m k χ).differentiableOn
  have hL : DifferentiableOn ℂ
      (fun s => deriv (DirichletCharacter.LFunction χ) s) {s : ℂ | 0 < s.re} :=
    (primitiveCharacter_differentiable_LFunction_deriv hd hχ).differentiableOn
  have hM : DifferentiableOn ℂ
      (fun s => lemma6MollifierAt H s χ) {s : ℂ | 0 < s.re} :=
    (differentiable_lemma6MollifierAt H χ).differentiableOn
  unfold lemma6BContourIntegrand
  exact ((((hxpow.differentiableOn.mul hk).mul hp).mul hL).mul hM).neg

/-- Cauchy--Goursat on the finite rectangle with vertical sides `β` and
`α` and heights `[-T,T]`.  This is the rigorous finite precursor of the
contour move in equation (17). -/
theorem lemma6BContour_finite_rectangle
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (T : ℝ) :
    let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
    let α : ℝ := 1 + 1 / Real.log (x : ℝ)
    let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
    (∫ σ : ℝ in β..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ σ : ℝ in β..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((α : ℂ) + (ν : ℂ) * Complex.I)) -
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((β : ℂ) + (ν : ℂ) * Complex.I)) = 0 := by
  dsimp only
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let z : ℂ := (β : ℂ) + (-T : ℂ) * Complex.I
  let w : ℂ := (α : ℂ) + (T : ℂ) * Complex.I
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  have hlog : 0 < Real.log (x : ℝ) := by linarith
  have hβpos : 0 < β := by
    dsimp only [β]
    positivity
  have hβα : β ≤ α := by
    dsimp only [β, α]
    norm_num
  have hzre : z.re = β := by
    dsimp only [z]
    simp
  have hwre : w.re = α := by
    dsimp only [w]
    simp
  have hzim : z.im = -T := by
    dsimp only [z]
    simp
  have hwim : w.im = T := by
    dsimp only [w]
    simp
  have hdiff : DifferentiableOn ℂ F
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    apply (differentiableOn_lemma6BContourIntegrand hd hx m k H hχ).mono
    intro s hs
    change 0 < s.re
    have hre := hs.1
    rw [hzre, hwre, uIcc_of_le hβα] at hre
    exact hβpos.trans_le hre.1
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  rw [hzre, hwre, hzim, hwim] at hrect
  dsimp only [F] at hrect
  simpa only [β, α, sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hrect

/-- The precise growth condition omitted when the paper lets the height of
the finite rectangle tend to infinity.  It is intentionally stated for the
two horizontal integrals themselves, rather than being hidden inside the
phrase "move the contour". -/
def Lemma6BHorizontalEdgesVanish
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) : Prop :=
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α, F ((σ : ℂ) - (T : ℂ) * Complex.I))
      atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α, F ((σ : ℂ) + (T : ℂ) * Complex.I))
      atTop (𝓝 0)

/-- A pointwise, uniform-in-the-strip sufficient condition for the two
horizontal edges to disappear.  This is the precise form in which a
vertical-growth estimate for `L'` can be combined with decay of the rational
Mellin kernel. -/
def Lemma6BHorizontalPointwiseDecay
    {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) : Prop :=
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
    ∀ T σ : ℝ, σ ∈ Icc β α →
      ‖F ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤ g T ∧
      ‖F ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ g T

/-- Uniform pointwise decay across the compact horizontal segment implies
the horizontal-edge limit needed by the contour shift. -/
theorem lemma6BHorizontalEdgesVanish_of_pointwiseDecay
    {d : ℕ} [NeZero d] {x m k H : ℕ}
    {χ : DirichletCharacter ℂ d}
    (hdecay : Lemma6BHorizontalPointwiseDecay x m k H χ) :
    Lemma6BHorizontalEdgesVanish x m k H χ := by
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  rcases hdecay with ⟨g, hg, hbound⟩
  have hβα : β ≤ α := by
    dsimp only [β, α]
    norm_num
  have hwidth : Tendsto (fun T : ℝ => g T * |α - β|)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hg.mul_const |α - β|
  have hbotBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in β..α,
          F ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤
        g T * |α - β| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc β α := by
      rw [← uIcc_of_le hβα]
      exact uIoc_subset_uIcc hσ
    exact (hbound T σ (by simpa only [β, α] using hσ')).1
  have htopBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in β..α,
          F ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        g T * |α - β| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc β α := by
      rw [← uIcc_of_le hβα]
      exact uIoc_subset_uIcc hσ
    exact (hbound T σ (by simpa only [β, α] using hσ')).2
  have hbot : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α,
        F ((σ : ℂ) - (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      hbotBound hwidth
  have htop : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in β..α,
        F ((σ : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      htopBound hwidth
  simpa only [Lemma6BHorizontalEdgesVanish, β, α, F] using And.intro hbot htop

/-- Once the two horizontal edges vanish and both boundary restrictions
are integrable, the finite rectangle identity gives equality of the two
improper vertical integrals. -/
theorem lemma6BContour_verticalIntegral_eq
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hhor : Lemma6BHorizontalEdgesVanish x m k H χ)
    (hα : Integrable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)))
    (hβ : Integrable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    (∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) =
      ∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν) := by
  let β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ)
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := lemma6BContourIntegrand x m k H χ
  let bot : ℝ → ℂ := fun T =>
    ∫ σ : ℝ in β..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)
  let top : ℝ → ℂ := fun T =>
    ∫ σ : ℝ in β..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)
  let va : ℝ → ℂ := fun T =>
    ∫ ν : ℝ in (-T)..T, F ((α : ℂ) + (ν : ℂ) * Complex.I)
  let vb : ℝ → ℂ := fun T =>
    ∫ ν : ℝ in (-T)..T, F ((β : ℂ) + (ν : ℂ) * Complex.I)
  have hpointα : (fun ν : ℝ => F ((α : ℂ) + (ν : ℂ) * Complex.I)) =
      fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν) := by
    funext ν
    rfl
  have hpointβ : (fun ν : ℝ => F ((β : ℂ) + (ν : ℂ) * Complex.I)) =
      fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν) := by
    funext ν
    rfl
  have hva : Tendsto va atTop
      (𝓝 (∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν))) := by
    have ht := intervalIntegral_tendsto_integral hα
      tendsto_neg_atTop_atBot
      (show Tendsto (fun T : ℝ => T) atTop atTop from tendsto_id)
    simpa only [va, hpointα, id_eq] using ht
  have hvb : Tendsto vb atTop
      (𝓝 (∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) := by
    have ht := intervalIntegral_tendsto_integral hβ
      tendsto_neg_atTop_atBot
      (show Tendsto (fun T : ℝ => T) atTop atTop from tendsto_id)
    simpa only [vb, hpointβ, id_eq] using ht
  have hhor' : Tendsto bot atTop (𝓝 0) ∧ Tendsto top atTop (𝓝 0) := by
    simpa only [Lemma6BHorizontalEdgesVanish, bot, top, F, β, α] using hhor
  have hcalc := (hhor'.1.sub hhor'.2).add
    ((hva.const_smul Complex.I).sub (hvb.const_smul Complex.I))
  have heq : ∀ T : ℝ,
      bot T - top T + (Complex.I • va T - Complex.I • vb T) = 0 := by
    intro T
    simpa only [bot, top, va, vb, F, β, α, sub_eq_add_neg,
      add_assoc] using
      lemma6BContour_finite_rectangle hd hx hxlog m k H hχ T
  have hzero : Tendsto
      (fun T : ℝ => bot T - top T +
        (Complex.I • va T - Complex.I • vb T))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun T => (heq T).symm)
  have hlim :
      (0 : ℂ) - 0 +
        (Complex.I •
            (∫ ν : ℝ,
              lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) -
          Complex.I •
            (∫ ν : ℝ,
              lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) = 0 :=
    tendsto_nhds_unique hcalc hzero
  have hmul : Complex.I *
      ((∫ ν : ℝ,
          lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) -
        ∫ ν : ℝ,
          lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)) = 0 := by
    simpa only [zero_sub, zero_add, neg_zero, smul_eq_mul, mul_sub] using hlim
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero)

/-- The contour shift commutes with the finite primitive-character sum and
with Chen's unit-modulus conjugate character factor.  All analytic limit
hypotheses remain explicit character by character. -/
theorem lemma6BContour_primComplexSum_verticalIntegral_eq
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (hhor : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Lemma6BHorizontalEdgesVanish x m k H χ)
    (hα : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)))
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (x : ZMod d)) *
          ∫ ν : ℝ,
            lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) =
      primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (x : ZMod d)) *
          ∫ ν : ℝ,
            lemma6BContourIntegrand x m k H χ
              (lemma6BetaPoint x ν)) := by
  unfold primComplexSum
  apply tsum_congr
  intro χ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [lemma6BContour_verticalIntegral_eq hd hx hxlog m k H hp
      (hhor χ hp) (hα χ hp) (hβ χ hp)]
  · simp [hp]

end Chen
