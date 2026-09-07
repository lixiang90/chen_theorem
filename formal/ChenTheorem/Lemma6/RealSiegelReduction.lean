import ChenTheorem.Lemma6.PrimitiveExceptionalRegion
import ChenTheorem.Lemma6.ZeroFreeRegionAssembly

namespace Chen

/-- The full mixed zero-free-region package now requires only the ineffective
Siegel bound for real primitive characters on the real axis. The logarithmic
nonexceptional region and its derivative bounds are already proved. -/
theorem primitiveZeroFreeRegion_of_real_siegel
    (h : ∀ N : ℕ, 1 ≤ N → ∃ cS : ℝ, 0 < cS ∧
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ β : ℝ,
          1 - cS * (q : ℝ) ^ ((-1 : ℝ) / N) < β →
            DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) : PrimitiveZeroFreeRegion := by
  obtain ⟨cH, hcH, hregion⟩ := exists_primitive_exceptional_zero_region
  apply primitiveZeroFreeRegion_of_nonvanishing
  intro N hN
  obtain ⟨cS, hcS, hsiegel⟩ := h N hN
  refine ⟨cH, cS, hcH, hcS, ?_⟩
  intro q inst χ hq hχ s hs hz
  have hheight : primitiveZeroFreeWidthAt N cH cS q s.im ≤
      cH / Real.log ((q : ℝ) * (|s.im| + 2)) := min_le_left _ _
  have h := (hregion q χ hq hχ).2 s (by linarith) hz
  have hwidth : primitiveZeroFreeWidthAt N cH cS q s.im ≤
      cS * (q : ℝ) ^ ((-1 : ℝ) / N) := min_le_right _ _
  have he : (s.re : ℂ) = s := by apply Complex.ext <;> simp [h.2.1]
  have hne := hsiegel q inst χ hq hχ h.1 s.re (by linarith)
  rw [he] at hne
  exact hne hz

end Chen
