/-
The zero-free-region interface for equation (21) in Lemma 6.

Chen moves the logarithmic-derivative contour from his `alpha`-line to
`Re s = 1 - 1 / sqrt(log x)`.  The classical input behind this step is not
a fixed-width strip uniform in the imaginary part.  Its width has two
independent restrictions:

* the de la Vallee-Poussin region shrinks like
  `1 / log(q (|Im s| + 2))` with the height;
* a possible exceptional real zero is excluded only by an ineffective
  Siegel bound.  At the fixed exponent used by Chen, this contributes a
  width of the shape `q^(-1/300)`.

The uniform region valid for every primitive character is therefore the
minimum of these two widths.  The logarithmic derivative is requested only
in the region with half that width, leaving quantitative distance from all
zeros.  Its deliberately generous bound includes the possible
`q^(1/300)` cost of a nearby exceptional zero.

Mathlib currently proves only nonvanishing in `re s >= 1`.  The definition
`PrimitiveZeroFreeRegion` below records the missing classical package as a
proposition, and `primitive_zero_free_region` is the single `sorry` in the
equation-(21) pipeline.  The contour argument consuming it must use a finite
height; no claim of height-uniform fixed-width nonvanishing is made here.
-/
import ChenTheorem.Lemma6.StripGrowth
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open scoped Classical

namespace Chen

/-- The height-dependent width common to the classical nonexceptional
zero-free region and the ineffective fixed-exponent Siegel bound. -/
noncomputable def primitiveZeroFreeWidth
    (cHeight cSiegel : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  min
    (cHeight / Real.log ((q : ℝ) * (|t| + 2)))
    (cSiegel * (q : ℝ) ^ ((-1 : ℝ) / 300))

/-- The classical primitive-Dirichlet-`L` input needed for equation (21).

The nonvanishing assertion uses a strict boundary.  The companion
logarithmic-derivative estimate is required only in the half-width region;
this automatically lies strictly inside the nonvanishing region once the
width is positive.  Constants are absolute, while `cSiegel` is generally
ineffective. -/
structure PrimitiveZeroFreeRegionData where
  cHeight : ℝ
  cSiegel : ℝ
  cLogDeriv : ℝ
  cHeight_pos : 0 < cHeight
  cSiegel_pos : 0 < cSiegel
  cLogDeriv_pos : 0 < cLogDeriv
  nonvanishing :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidth cHeight cSiegel q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0
  logDeriv_bound :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidth cHeight cSiegel q s.im / 2 ≤ s.re →
          ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ ≤
            cLogDeriv *
              ((q : ℝ) ^ ((1 : ℝ) / 300) +
                Real.log ((q : ℝ) * (|s.im| + 2)) + 1) ^ 2

/-- Existence of a classical mixed zero-free-region package. -/
def PrimitiveZeroFreeRegion : Prop :=
  Nonempty PrimitiveZeroFreeRegionData

/-- **The single unresolved analytic input of the equation-(21) pipeline.**

Discharging this theorem requires a classical height-dependent zero-free
region for primitive Dirichlet `L`-functions, an ineffective Siegel bound
at exponent `1/300`, and the associated logarithmic-derivative estimate in
a strictly smaller region. -/
theorem primitive_zero_free_region : PrimitiveZeroFreeRegion := by
  sorry

end Chen
