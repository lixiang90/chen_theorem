/-
Gallagher's Sobolev-type inequality (centered form), the analytic core of the
large sieve (Lemma 2 of Chen's paper).

For a continuously differentiable `f : ℝ → ℂ` and the arc of radius `δ/2`
centered at `x`,

  `‖f x‖² ≤ δ⁻¹ ∫_{x-δ/2}^{x+δ/2} ‖f‖² + ∫_{x-δ/2}^{x+δ/2} ‖f‖·‖f'‖`.

The proof is the standard one: integrate the pointwise bound
`‖f x‖² - ‖f t‖² ≤ 2 ∫_t^x ‖f f'‖` (from FTC applied to `‖f‖²`, whose
derivative `2⟪f, f'⟫` is bounded by `2‖f‖‖f'‖` via Cauchy–Schwarz) over each
half of the arc separately; the centering of the arc at `x` is what makes the
coefficient of the cross term `1` rather than `2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open Set MeasureTheory intervalIntegral
open scoped RealInnerProductSpace

namespace Chen.LargeSieve

variable {f : ℝ → ℂ} {f' : ℝ → ℂ}

private lemma continuous_of_hasDerivAt (hf : ∀ t, HasDerivAt f (f' t) t) : Continuous f :=
  continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt

/-- `‖f x‖² ≤ ‖f t‖² + 2 ∫_{uIoc t x} ‖f‖ ‖f'‖`, from FTC applied to
`u ↦ ‖f u‖²` (whose derivative `2⟪f u, f' u⟫` has absolute value at most
`2‖f u‖‖f' u‖`). -/
private lemma norm_sq_le (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') (t x : ℝ) :
    ‖f x‖ ^ 2 ≤ ‖f t‖ ^ 2 + 2 * ∫ u in Set.uIoc t x, ‖f u‖ * ‖f' u‖ := by
  have hfcont : Continuous f := continuous_of_hasDerivAt hf
  have hgcont : Continuous fun u => 2 * ⟪f u, f' u⟫ :=
    continuous_const.mul (hfcont.inner hf')
  have hff' : Continuous fun u => ‖f u‖ * ‖f' u‖ := hfcont.norm.mul hf'.norm
  have hpt : ∀ u, |2 * ⟪f u, f' u⟫| ≤ 2 * (‖f u‖ * ‖f' u‖) := by
    intro u
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left ((le_of_eq (Real.norm_eq_abs _).symm).trans
      (norm_inner_le_norm _ _)) (by norm_num)
  rcases le_total t x with htx | htx
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := t) (b := x)
      (fun u _ => (hf u).norm_sq) (hgcont.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    have habs := (intervalIntegral.abs_integral_le_integral_abs htx).trans
      (intervalIntegral.integral_mono_on_of_le_Ioo htx
        (hgcont.abs.intervalIntegrable (μ := MeasureTheory.volume) _ _) ((hff'.const_mul 2).intervalIntegrable (μ := MeasureTheory.volume) _ _)
        fun u _ => hpt u)
    have h1 : ‖f x‖ ^ 2 - ‖f t‖ ^ 2 ≤ ∫ u in t..x, 2 * (‖f u‖ * ‖f' u‖) :=
      hftc ▸ (le_abs_self _).trans habs
    rw [intervalIntegral.integral_const_mul] at h1
    rw [Set.uIoc_of_le htx, ← intervalIntegral.integral_of_le htx]
    linarith [h1]
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := t)
      (fun u _ => (hf u).norm_sq) (hgcont.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    have habs := (intervalIntegral.abs_integral_le_integral_abs htx).trans
      (intervalIntegral.integral_mono_on_of_le_Ioo htx
        (hgcont.abs.intervalIntegrable (μ := MeasureTheory.volume) _ _) ((hff'.const_mul 2).intervalIntegrable (μ := MeasureTheory.volume) _ _)
        fun u _ => hpt u)
    have h1 : -(‖f t‖ ^ 2 - ‖f x‖ ^ 2) ≤ ∫ u in x..t, 2 * (‖f u‖ * ‖f' u‖) :=
      hftc ▸ (neg_le_abs _).trans habs
    rw [intervalIntegral.integral_const_mul] at h1
    rw [Set.uIoc_comm, Set.uIoc_of_le htx, ← intervalIntegral.integral_of_le htx]
    linarith [h1]

/-- **Gallagher's inequality**, centered form: for `f : ℝ → ℂ` everywhere
differentiable with continuous derivative `f'`, and `δ > 0`,
`‖f x‖² ≤ δ⁻¹ ∫_{x-δ/2}^{x+δ/2} ‖f‖² + ∫_{x-δ/2}^{x+δ/2} ‖f‖ ‖f'‖`.

The arc is centered at `x`: integrating the pointwise FTC bound
`‖f x‖² ≤ ‖f t‖² + 2 ∫ ‖f‖‖f'‖` over each half-arc of length `δ/2`
gives a factor `δ/2 · 2 = δ` on the cross term. -/
theorem gallagher_centered (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖f x‖ ^ 2 ≤ δ⁻¹ * (∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ ^ 2) +
      ∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ * ‖f' t‖ := by
  have hfcont : Continuous f := continuous_of_hasDerivAt hf
  have hfnorm : Continuous fun t => ‖f t‖ ^ 2 := hfcont.norm.pow 2
  have hff' : Continuous fun t => ‖f t‖ * ‖f' t‖ := hfcont.norm.mul hf'.norm
  -- Half-interval bound: integrate `‖f x‖² ≤ ‖f t‖² + 2∫ ‖f‖‖f'‖` over an
  -- interval `[c, d]` of length `δ/2` containing `x`.
  have hhalf : ∀ {c d : ℝ}, c ≤ x → x ≤ d → d - c = δ / 2 →
      (δ / 2) * ‖f x‖ ^ 2 ≤
        (∫ t in c..d, ‖f t‖ ^ 2) + δ * ∫ t in c..d, ‖f t‖ * ‖f' t‖ := by
    intro c d hc hd hcd
    have hcd' : c ≤ d := hc.trans hd
    have hsub : ∀ t ∈ Ioo c d, Set.uIoc t x ⊆ Set.Ioc c d := by
      intro t ht
      rcases le_total t x with htx | htx
      · rw [Set.uIoc_of_le htx]
        exact Set.Ioc_subset_Ioc ht.1.le hd
      · rw [Set.uIoc_comm, Set.uIoc_of_le htx]
        exact Set.Ioc_subset_Ioc hc ht.2.le
    have hC : 2 * ∫ u in Set.Ioc c d, ‖f u‖ * ‖f' u‖ =
        2 * ∫ u in c..d, ‖f u‖ * ‖f' u‖ := by
      rw [intervalIntegral.integral_of_le hcd']
    have hpt : ∀ t ∈ Ioo c d, ‖f x‖ ^ 2 ≤
        ‖f t‖ ^ 2 + 2 * ∫ u in Set.Ioc c d, ‖f u‖ * ‖f' u‖ := by
      intro t ht
      have hmono : (∫ u in Set.uIoc t x, ‖f u‖ * ‖f' u‖) ≤
          ∫ u in Set.Ioc c d, ‖f u‖ * ‖f' u‖ :=
        MeasureTheory.setIntegral_mono_set (hff'.integrableOn_Ioc)
          (ae_of_all _ fun u => mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (hsub t ht).eventuallyLE
      linarith [norm_sq_le hf hf' t x, hmono]
    calc (δ / 2) * ‖f x‖ ^ 2
        = ∫ t in c..d, ‖f x‖ ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hcd]
      _ ≤ ∫ t in c..d, (‖f t‖ ^ 2 + 2 * ∫ u in Set.Ioc c d, ‖f u‖ * ‖f' u‖) := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo hcd'
            intervalIntegral.intervalIntegrable_const ?_ hpt
          exact (hfnorm.intervalIntegrable (μ := MeasureTheory.volume) _ _).add intervalIntegral.intervalIntegrable_const
      _ = (∫ t in c..d, ‖f t‖ ^ 2) + δ * ∫ t in c..d, ‖f t‖ * ‖f' t‖ := by
          rw [intervalIntegral.integral_add (hfnorm.intervalIntegrable (μ := MeasureTheory.volume) _ _)
            intervalIntegral.intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, hcd, hC]
          ring
  have hleft := hhalf (by linarith : x - δ/2 ≤ x) (le_refl x) (by ring)
  have hright := hhalf (le_refl x) (by linarith : x ≤ x + δ/2) (by ring)
  have hsum := add_le_add hleft hright
  rw [← add_mul, show δ / 2 + δ / 2 = δ by ring] at hsum
  have hjoin1 : (∫ t in (x - δ/2)..x, ‖f t‖ ^ 2) + (∫ t in x..(x + δ/2), ‖f t‖ ^ 2) =
      ∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hfnorm.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hfnorm.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have hjoin2 : (∫ t in (x - δ/2)..x, ‖f t‖ * ‖f' t‖) +
      (∫ t in x..(x + δ/2), ‖f t‖ * ‖f' t‖) =
      ∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ * ‖f' t‖ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hff'.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hff'.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have hsum' : δ * ‖f x‖ ^ 2 ≤
      (∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ ^ 2) +
        δ * ∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ * ‖f' t‖ := by
    rw [← hjoin1, ← hjoin2, mul_add]
    linarith [hsum]
  have h3 : δ * (δ⁻¹ * (∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ ^ 2) +
        ∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ * ‖f' t‖) =
      (∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ ^ 2) +
        δ * ∫ t in (x - δ/2)..(x + δ/2), ‖f t‖ * ‖f' t‖ := by
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
  rw [← h3] at hsum'
  exact (mul_le_mul_iff_of_pos_left hδ).mp hsum'

end Chen.LargeSieve
