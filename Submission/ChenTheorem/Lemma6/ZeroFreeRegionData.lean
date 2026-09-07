import Submission.ChenTheorem.Lemma6.StripGrowth
import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option autoImplicit true

open scoped Classical

namespace Chen

/-- The height-dependent width common to the classical nonexceptional
zero-free region and an ineffective Siegel bound with exponent `1 / N`. -/
noncomputable def primitiveZeroFreeWidthAt
    (N : ℕ) (cHeight cSiegel : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  min
    (cHeight / Real.log ((q : ℝ) * (|t| + 2)))
    (cSiegel * (q : ℝ) ^ ((-1 : ℝ) / N))

/-- The `N = 300` specialization used throughout the equation-(21)
development. -/
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

/-- The same classical package with an arbitrary fixed positive Siegel
exponent denominator.  This family is needed for the arbitrary logarithmic
saving in the standalone Bombieri--Vinogradov theorem. -/
structure PrimitiveZeroFreeRegionDataAt (N : ℕ) where
  cHeight : ℝ
  cSiegel : ℝ
  cLogDeriv : ℝ
  cHeight_pos : 0 < cHeight
  cSiegel_pos : 0 < cSiegel
  cLogDeriv_pos : 0 < cLogDeriv
  nonvanishing :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N cHeight cSiegel q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0
  logDeriv_bound :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N cHeight cSiegel q s.im / 2 ≤ s.re →
          ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ ≤
            cLogDeriv *
              ((q : ℝ) ^ ((1 : ℝ) / N) +
                Real.log ((q : ℝ) * (|s.im| + 2)) + 1) ^ 2

/-- Height-uniform logarithmic-derivative majorant for a finite rectangle,
at an arbitrary fixed Siegel exponent. -/
noncomputable def primitiveLogDerivMajorantAt
    {N : ℕ} (data : PrimitiveZeroFreeRegionDataAt N)
    (q : ℕ) (T : ℝ) : ℝ :=
  data.cLogDeriv *
    ((q : ℝ) ^ ((1 : ℝ) / N) +
      Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2

theorem primitiveLogDerivMajorantAt_nonneg
    {N : ℕ} (data : PrimitiveZeroFreeRegionDataAt N)
    (q : ℕ) (T : ℝ) :
    0 ≤ primitiveLogDerivMajorantAt data q T := by
  unfold primitiveLogDerivMajorantAt
  exact mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _)

/-- Existence of a classical mixed zero-free-region package. -/
def PrimitiveZeroFreeRegion : Prop :=
  Nonempty PrimitiveZeroFreeRegionData ∧
    ∀ N : ℕ, 1 ≤ N → Nonempty (PrimitiveZeroFreeRegionDataAt N)

theorem primitiveZeroFreeHeightLog_pos
    {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := by
  apply Real.log_pos
  have hqcast : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  nlinarith

theorem primitiveZeroFreeWidth_pos
    {cHeight cSiegel : ℝ} (hcHeight : 0 < cHeight)
    (hcSiegel : 0 < cSiegel) {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < primitiveZeroFreeWidth cHeight cSiegel q t := by
  unfold primitiveZeroFreeWidth
  apply lt_min
  · exact div_pos hcHeight (primitiveZeroFreeHeightLog_pos hq t)
  · exact mul_pos hcSiegel (Real.rpow_pos_of_pos (by positivity) _)

/-- Positivity of the mixed width for an arbitrary fixed Siegel exponent. -/
theorem primitiveZeroFreeWidthAt_pos
    {N : ℕ} {cHeight cSiegel : ℝ} (hcHeight : 0 < cHeight)
    (hcSiegel : 0 < cSiegel) {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < primitiveZeroFreeWidthAt N cHeight cSiegel q t := by
  unfold primitiveZeroFreeWidthAt
  apply lt_min
  · exact div_pos hcHeight (primitiveZeroFreeHeightLog_pos hq t)
  · exact mul_pos hcSiegel (Real.rpow_pos_of_pos (by positivity) _)

end Chen
