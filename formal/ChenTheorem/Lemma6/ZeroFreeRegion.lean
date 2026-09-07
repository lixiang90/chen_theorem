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

The classical package is proved locally from mathlib: the logarithmic
nonexceptional region, the ineffective real Siegel bound, and the companion
logarithmic-derivative estimate. The contour argument consuming it uses a
finite height; no height-uniform fixed-width nonvanishing is asserted.
-/
import ChenTheorem.Lemma6.RealSiegelReduction
import ChenTheorem.Lemma6.RealCharacterSiegel

namespace Chen

/-- The mixed Dirichlet zero-free region and its half-width logarithmic
derivative bound, including Siegel's ineffective exceptional-zero estimate. -/
theorem primitive_zero_free_region : PrimitiveZeroFreeRegion := by
  apply primitiveZeroFreeRegion_of_real_siegel
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨c, hc, hsiegel⟩ := exists_real_character_siegel_region (by positivity : 0 < 1 / (N : ℝ))
  refine ⟨c, hc, ?_⟩
  intro q inst χ hq hχ hsq β hβ
  apply hsiegel q χ hq (primitiveCharacter_ne_one hq hχ) hsq β
  simpa only [neg_div] using hβ

end Chen
