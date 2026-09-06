/-
The zero-free-region interface for equation (21) in Lemma 6.

Chen moves the logarithmic-derivative contour from his `alpha`-line to
`Re s = 1 - 1 / sqrt(log x)`.  The classical input behind this step is not
a fixed-width strip uniform in the imaginary part.  Its width has two
independent restrictions:

* the de la Vallee-Poussin region shrinks like
  `1 / log(q (|Im s| + 2))` with the height;
* a possible exceptional real zero is excluded only by an ineffective
  Siegel bound.  For every fixed positive denominator `N`, this contributes
  a width of the shape `q^(-1/N)`; Chen's equation (21) uses `N = 300`.

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
import ChenTheorem.Lemma6.RealZeroFreeReduction

namespace Chen

/-- **The single unresolved analytic input of the equation-(21) pipeline.**

The nonreal-character case is proved in `NonrealZeroFreeRegion`.
Discharging the remaining goal requires the height-dependent zero-free region
for primitive real characters and the ineffective Siegel bound at every fixed
positive exponent. The derivative estimate and the nonreal case are supplied
by `primitiveZeroFreeRegion_of_real_nonvanishing`. -/
theorem primitive_zero_free_region : PrimitiveZeroFreeRegion := by
  apply primitiveZeroFreeRegion_of_real_nonvanishing
  intro N hN
  sorry

end Chen
