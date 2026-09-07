import ChenTheorem.Lemma6.RealNonexceptionalRegion

namespace Chen

/-- A uniform logarithmic region for every primitive character contains at most
one zero. Any zero there belongs to a real character and is real and simple. -/
theorem exists_primitive_exceptional_zero_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive →
      (Set.Subsingleton {s : ℂ | 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re ∧
        DirichletCharacter.LFunction χ s = 0}) ∧
      ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
        DirichletCharacter.LFunction χ s = 0 →
        χ ^ 2 = 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨cN, hcN, hN⟩ := exists_primitive_nonreal_zero_free_region
  obtain ⟨cR, hcR, hR⟩ := exists_primitive_real_exceptional_zero_region
  refine ⟨min cN cR, lt_min hcN hcR, ?_⟩
  intro q inst χ hq hχ
  by_cases hsq : χ ^ 2 = 1
  · have hreal := hR q χ hq hχ hsq
    have hwidth : ∀ t : ℝ,
        min cN cR / Real.log ((q : ℝ) * (|t| + 2)) ≤
          cR / Real.log ((q : ℝ) * (|t| + 2)) := by
      intro t
      exact div_le_div_of_nonneg_right (min_le_right _ _) (primitiveZeroFreeHeightLog_pos hq t).le
    constructor
    · intro s hs t ht
      exact hreal.1 ⟨by linarith [hwidth s.im, hs.1], hs.2⟩
        ⟨by linarith [hwidth t.im, ht.1], ht.2⟩
    · intro s hs hz
      have h := hreal.2 s (by linarith [hwidth s.im]) hz
      exact ⟨hsq, h⟩
  · have hne : ∀ s : ℂ, 1 - min cN cR / Real.log ((q : ℝ) * (|s.im| + 2)) < s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
      intro s hs
      have hw := div_le_div_of_nonneg_right (min_le_left cN cR)
        (primitiveZeroFreeHeightLog_pos hq s.im).le
      exact hN q χ hq hχ hsq s (by linarith)
    constructor
    · intro s hs t ht
      exact False.elim (hne s hs.1 hs.2)
    · intro s hs hz
      exact False.elim (hne s hs hz)

end Chen
