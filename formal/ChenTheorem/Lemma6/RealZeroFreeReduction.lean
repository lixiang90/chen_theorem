import ChenTheorem.Lemma6.NonrealZeroFreeRegion
import ChenTheorem.Lemma6.ZeroFreeRegionAssembly

namespace Chen

/-- The original full analytic package follows from its mixed nonvanishing
statement restricted to primitive characters whose square is principal. -/
theorem primitiveZeroFreeRegion_of_real_nonvanishing
    (h : ∀ N : ℕ, 1 ≤ N → ∃ cH cS : ℝ, 0 < cH ∧ 0 < cS ∧
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 → ∀ s : ℂ,
          1 - primitiveZeroFreeWidthAt N cH cS q s.im < s.re →
            DirichletCharacter.LFunction χ s ≠ 0) : PrimitiveZeroFreeRegion := by
  obtain ⟨c, hc, hnonreal⟩ := exists_primitive_nonreal_zero_free_region
  apply primitiveZeroFreeRegion_of_nonvanishing
  intro N hN
  obtain ⟨cH, cS, hcH, hcS, hreal⟩ := h N hN
  refine ⟨min cH c, cS, lt_min hcH hc, hcS, ?_⟩
  intro q inst χ hq hχ s hs
  have hL := primitiveZeroFreeHeightLog_pos hq s.im
  by_cases hsq : χ ^ 2 = 1
  · apply hreal q inst χ hq hχ hsq s
    have hw : primitiveZeroFreeWidthAt N (min cH c) cS q s.im ≤
        primitiveZeroFreeWidthAt N cH cS q s.im :=
      min_le_min (div_le_div_of_nonneg_right (min_le_left _ _) hL.le) le_rfl
    linarith
  · apply hnonreal q χ hq hχ hsq s
    have hw : primitiveZeroFreeWidthAt N (min cH c) cS q s.im ≤
        c / Real.log ((q : ℝ) * (|s.im| + 2)) :=
      (min_le_left _ _).trans (div_le_div_of_nonneg_right (min_le_right _ _) hL.le)
    linarith

end Chen
