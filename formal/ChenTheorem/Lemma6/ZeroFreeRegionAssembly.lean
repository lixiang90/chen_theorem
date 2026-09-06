import ChenTheorem.Lemma6.ZeroFreeLogDerivativeBound

namespace Chen

/-- The logarithmic-derivative field of the classical package is redundant:
a mixed nonvanishing region supplies it after reducing the height constant. -/
theorem primitiveZeroFreeRegionDataAt_of_nonvanishing (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcS : 0 < cS)
    (hne : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N cH cS q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0) :
    Nonempty (PrimitiveZeroFreeRegionDataAt N) := by
  let H := min cH (1 / 8)
  let K := 1 / H + 1 / cS
  have hH : 0 < H := lt_min hcH (by norm_num)
  have hHsmall : H ≤ 1 / 8 := min_le_right _ _
  have hK : 0 < K := by dsimp [K]; positivity
  have hnv : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N H cS q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0 := by
    intro q hqInst χ hq hχ s hs
    have hw : primitiveZeroFreeWidthAt N H cS q s.im ≤ primitiveZeroFreeWidthAt N cH cS q s.im :=
      min_le_min (div_le_div_of_nonneg_right (min_le_left _ _) (primitiveZeroFreeHeightLog_pos hq s.im).le) le_rfl
    exact hne q hqInst χ hq hχ s (by linarith)
  refine ⟨{
    cHeight := H
    cSiegel := cS
    cLogDeriv := 224 * (100 + K) * K + 4 * K ^ 2
    cHeight_pos := hH
    cSiegel_pos := hcS
    cLogDeriv_pos := by positivity
    nonvanishing := hnv
    logDeriv_bound := ?_ }⟩
  intro q hqInst χ hq hχ s hs
  exact norm_LFunction_logDeriv_le_scale_sq N H cS hH hHsmall hcS hq hχ
    (hnv q hqInst χ hq hχ) s hs

theorem primitiveZeroFreeRegionData_of_dataAt (data : PrimitiveZeroFreeRegionDataAt 300) :
    Nonempty PrimitiveZeroFreeRegionData := by
  refine ⟨{
    cHeight := data.cHeight
    cSiegel := data.cSiegel
    cLogDeriv := data.cLogDeriv
    cHeight_pos := data.cHeight_pos
    cSiegel_pos := data.cSiegel_pos
    cLogDeriv_pos := data.cLogDeriv_pos
    nonvanishing := ?_
    logDeriv_bound := ?_ }⟩
  · simpa only [primitiveZeroFreeWidth, primitiveZeroFreeWidthAt, Nat.cast_ofNat] using data.nonvanishing
  · simpa only [primitiveZeroFreeWidth, primitiveZeroFreeWidthAt, Nat.cast_ofNat] using data.logDeriv_bound

/-- To finish the zero-free-region package it suffices to prove the mixed
nonvanishing region at each fixed Siegel exponent. The companion derivative
estimate is now a consequence of the proved disk and scale estimates. -/
theorem primitiveZeroFreeRegion_of_nonvanishing
    (h : ∀ N : ℕ, 1 ≤ N → ∃ cH cS : ℝ, 0 < cH ∧ 0 < cS ∧
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
          1 - primitiveZeroFreeWidthAt N cH cS q s.im < s.re →
            DirichletCharacter.LFunction χ s ≠ 0) : PrimitiveZeroFreeRegion := by
  have hdata : ∀ N : ℕ, 1 ≤ N → Nonempty (PrimitiveZeroFreeRegionDataAt N) := by
    intro N hN
    obtain ⟨cH, cS, hcH, hcS, hnv⟩ := h N hN
    exact primitiveZeroFreeRegionDataAt_of_nonvanishing N cH cS hcH hcS hnv
  obtain ⟨data⟩ := hdata 300 (by norm_num)
  exact ⟨primitiveZeroFreeRegionData_of_dataAt data, hdata⟩

end Chen
