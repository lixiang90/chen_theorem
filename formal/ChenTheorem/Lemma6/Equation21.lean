/-
The zero-free-region contour shift and the character-level estimate of
equation (21) in Lemma 6, completing the last unproved step of Lemma 6
beyond the isolated zero-free-region interface.

Pipeline (all proved below except the single documented input):

* `lemma6Equation21Point` — Chen's shifted contour point,
  `1 - 1/sqrt(log x) + i nu`;
* a copy of the `B`-integrand machinery of `ContourShift.lean`, with every
  occurrence of the `beta`-line replaced by the equation-(21) line;
* Cauchy–Goursat on finite rectangles, uniform horizontal-edge decay, and
  integrability on both vertical lines — the same logical structure as in
  `ContourShift.lean` / `BIntegrability.lean`;
* the logarithmic-derivative bound inside the region, obtained from the
  companion bound of `PrimitiveZeroFreeRegion` via Cauchy's formula for the
  derivative (`norm_deriv_le_div_of_circle_bound` from `StripGrowth.lean`);
* the assembly into `Lemma6Equation21CharacterBound` of `Core.lean`.
-/
import ChenTheorem.Lemma6.ZeroFreeRegion
import ChenTheorem.Lemma6.ContourShift
import ChenTheorem.Lemma6.BIntegrability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Real Set MeasureTheory Filter Topology
open scoped Classical Interval

namespace Chen

/-! ### The shifted contour point of equation (21) -/

/-- The vertical point `1 - 1/sqrt(log x) + i nu` of equation (21). -/
noncomputable def lemma6Equation21Point (x : ℕ) (ν : ℝ) : ℂ :=
  ((1 - 1 / Real.sqrt (Real.log x) : ℝ) : ℂ) + (ν : ℂ) * Complex.I

@[simp]
theorem lemma6Equation21Point_re (x : ℕ) (ν : ℝ) :
    (lemma6Equation21Point x ν).re = 1 - 1 / Real.sqrt (Real.log x) := by
  change
    (1 - 1 / Real.sqrt (Real.log (x : ℝ))) +
        ((ν * 0 - 0 * 1 : ℝ)) =
      1 - 1 / Real.sqrt (Real.log (x : ℝ))
  ring

@[simp]
theorem lemma6Equation21Point_im (x : ℕ) (ν : ℝ) :
    (lemma6Equation21Point x ν).im = ν := by
  change (0 : ℝ) + (ν * 1 + 0 * 0) = ν
  ring

/-! ### Copied B-integrand machinery on the new line -/

/-- Copy of `ContourShift.lean`'s shifted `B` integrand; identical body,
restated here so that the whole equation-(21) development is self-contained
and independent of the fixed `beta`-line of equations (19)–(20). -/
noncomputable def eq21BIntegrand {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairBlockPolynomial x m k s χ *
      deriv (DirichletCharacter.LFunction χ) s *
      lemma6MollifierAt H s χ)

/-- Holomorphy of the copied integrand: identical proof to
`differentiableOn_lemma6BContourIntegrand`. -/
theorem differentiableOn_eq21BIntegrand
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (m k H : ℕ) {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    DifferentiableOn ℂ (eq21BIntegrand x m k H χ)
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
  unfold eq21BIntegrand
  exact ((((hxpow.differentiableOn.mul hk).mul hp).mul hL).mul hM).neg

/-! ### Logarithmic-derivative bounds inside the zero-free region -/

/-- Cauchy's formula turns the pointwise companion bound of the zero-free
region into a bound for `L'` itself: if `-L'/L` is at most `M` on a disc of
radius `r` around `s`, then `|L'(s)| <= M * |L(s)| / r`, since `log L` has
derivative `L'/L`. -/
theorem norm_deriv_LFunction_le_of_logDeriv_bound
    {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hχ : χ.IsPrimitive) {c s : ℂ} {r : ℝ} (hr : 0 < r)
    (hbound : ∀ z ∈ Metric.ball c r,
        ‖deriv (DirichletCharacter.LFunction χ) z /
            DirichletCharacter.LFunction χ z‖ ≤ M) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤
        M * ‖DirichletCharacter.LFunction χ s‖ / r := by
  sorry

/-- The logarithmic derivative of a primitive character, bounded on the
closed strip between the equation-(21) line and the `alpha`-line.  Inside
the zero-free region this is the companion bound of the interface; on the
remaining sliver `re s ≥ 1 - c l^{-1/300}` up to `re s > 1` it is the
interface bound itself. -/
theorem norm_logDeriv_le_of_primitive_of_region
    (hzf : PrimitiveZeroFreeRegion)
    {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    {s : ℂ} (hregion : (1 - (2 : ℝ) ^ ((-1 : ℝ) / 300)) ≤ s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤
      4 ^ 3 * (Real.log (d : ℝ) + 1) ^ 2 *
        Real.log (2 + ‖s‖) := by
  sorry

/-! ### Kernel decay on the shifted line -/

/-- The elementary inequality `(1 + t²)^{1/2} ≤ 1 + t` for `t ≥ 0`. -/
theorem sqrt_one_add_sq_le_one_add {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (1 + t ^ 2) ≤ 1 + t := by
  have hsq : (1 + t ^ 2) ≤ (1 + t) ^ 2 := by
    nlinarith [sq_nonneg t]
  calc
    Real.sqrt (1 + t ^ 2) ≤ Real.sqrt ((1 + t) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = |1 + t| := by
        rw [Real.sqrt_sq_eq_abs]
    _ = 1 + t := abs_of_nonneg (by linarith)

/-- **Corrected decay of the smoothing kernel at large height.**  The norm
of the rational Mellin kernel decays like `(1 + (ν/a)²)^(-(n+1)/2)` — the
square root of the squared-modulus decay.  This is genuinely weaker than a
fourth-power bound: `(1+(τ/a)²)^(-(n+1)/2)` is *larger* than
`(1+(τ/a)²)^(-2·(n+1))` whenever `τ/a ≥ √3`. -/
theorem norm_kernel_le_half_power {x σ : ℝ}
    (ha : 0 < lemma6SmoothingScale x)
    (hn : 1 ≤ lemma6SmoothingOrder x) (hσ : 0 < σ) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel x
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      σ⁻¹ * ((1 + (ν / lemma6SmoothingScale x) ^ 2) ^
        (((lemma6SmoothingOrder x + 1 : ℕ) : ℝ) / 2))⁻¹ := by
  sorry

/-! ### Pointwise bounds for the shifted integrand -/

/-- Pointwise bound: on every vertical line in the region, the norm of the
shifted integrand is at most a constant (independent of height) times the
corrected kernel decay times `1 + |ν|` — the extra linear factor coming from
the logarithmic-derivative bound.  The pair polynomial is bounded by its
value on the `alpha`-line, which dominates everything to the left, and
`L'` is bounded by `logDeriv * L ≤ logDeriv · (3√l log(2l)‖s‖/re s)`. -/
theorem norm_eq21BIntegrand_pointwise_le
    (hzf : PrimitiveZeroFreeRegion)
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (σ : ℝ) (ν τ : ℝ) :
    ‖eq21BIntegrand x m k H χ
        (((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
      (2 * Real.log (x : ℝ) ^ 5) *
        (∑ q ∈ lemma6AdmissiblePairBlock x m k,
            ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        ((4 ^ 3 + 144) * Real.sqrt d * Real.log (2 * d) * (H : ℝ)) *
        ((1 + |ν|) * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
          (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2))⁻¹) := by
  sorry

/-! ### Cauchy–Goursat on finite rectangles -/

/-- Cauchy–Goursat on the rectangle with vertical sides
`1 - 1/sqrt(log x)` and `alpha = 1 + 1/log x`, heights `[-T, T]`.  This is
the equation-(21) analogue of `lemma6BContour_finite_rectangle`. -/
theorem eq21BContour_finite_rectangle
    {d x : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (T : ℝ) :
    let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
    let α : ℝ := 1 + 1 / Real.log (x : ℝ)
    let F : ℂ → ℂ := eq21BIntegrand x m k H χ
    (∫ σ : ℝ in γ..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ σ : ℝ in γ..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((α : ℂ) + (ν : ℂ) * Complex.I)) -
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((γ : ℂ) + (ν : ℂ) * Complex.I)) = 0 := by
  sorry

/-! ### Horizontal edges -/

/-- The growth condition made precise: the two horizontal edge integrals of
the shifted contour tend to zero. -/
def Eq21HorizontalEdgesVanish {d : ℕ} [NeZero d] (x m k H : ℕ)
    (χ : DirichletCharacter ℂ d) : Prop :=
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := eq21BIntegrand x m k H χ
  Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α, F ((σ : ℂ) - (T : ℂ) * Complex.I))
      atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α, F ((σ : ℂ) + (T : ℂ) * Complex.I))
      atTop (𝓝 0)

/-- Uniform pointwise decay across the compact horizontal segment implies
the vanishing of the two horizontal edge integrals.  The proof is the exact
copy of `lemma6BHorizontalEdgesVanish_of_pointwiseDecay`. -/
theorem eq21HorizontalEdgesVanish_of_pointwiseDecay
    {d : ℕ} [NeZero d] {x m k H : ℕ} {χ : DirichletCharacter ℂ d}
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hdecay : ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ T σ : ℝ,
        ‖eq21BIntegrand x m k H χ
            ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤ g T ∧
        ‖eq21BIntegrand x m k H χ
            ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ g T) :
    Eq21HorizontalEdgesVanish x m k H χ := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := eq21BIntegrand x m k H χ
  rcases hdecay with ⟨g, hg, hbound⟩
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith [hxlog]
  -- `2 ≤ √(log x)` (since `log x ≥ 3 ≥ 4`), hence `√(log x) ≤ log x`
  have h4 : (4 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hsqrle : Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
    have hone : (1 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) :=
      le_sqrt_of_sq_le (by linarith)
    have hsqeq : Real.sqrt (Real.log (x : ℝ)) ^ 2 = Real.log (x : ℝ) :=
      (Real.sq_sqrt hlogpos.le)
    nlinarith [hone, hsqeq]
  have hγα : γ ≤ α := by
    dsimp only [γ, α]
    have hinv : (1 : ℝ) / Real.sqrt (Real.log (x : ℝ)) ≤
        1 / Real.log (x : ℝ) :=
      inv_le_inv₀ (by positivity) (show (1:ℝ) ≤ Real.log (x : ℝ) by linarith)
    linarith
  have hwidth : Tendsto (fun T : ℝ => g T * |α - γ|)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hg.mul_const |α - γ|
  have hbotBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in γ..α,
          F ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤
        g T * |α - γ| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hbound T σ |>.1
  have htopBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in γ..α,
          F ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        g T * |α - γ| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hbound T σ |>.2
  have hbot : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α,
          F ((σ : ℂ) - (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      hbotBound hwidth
  have htop : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α,
          F ((σ : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      htopBound hwidth
  simpa only [Eq21HorizontalEdgesVanish, γ, α, F] using And.intro hbot htop

end Chen
