import ChenTheorem.Analysis.CompactZeroFreeStrip
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import ChenTheorem.Lemma6.ZeroFreeWidthScale

namespace Chen

/-- All nonprincipal characters of one modulus share a zero-free strip at
each bounded height. The width may depend on the modulus and height bound. -/
theorem exists_LFunction_common_compact_strip (q : ℕ) [NeZero q] (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 - δ ≤ s.re → |s.im| ≤ T → DirichletCharacter.LFunction χ s ≠ 0 := by
  classical
  let ι := {χ : DirichletCharacter ℂ q // χ ≠ 1}
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_compact_zeroFree_strip
    (fun χ : ι => DirichletCharacter.LFunction χ.val)
    (fun χ => (DirichletCharacter.differentiable_LFunction χ.property).continuous)
    (fun χ s hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.val
      (Or.inl χ.property) hs) T
  exact ⟨δ, hδ, fun χ hχ => hb ⟨χ, hχ⟩⟩

/-- Finitely many moduli and bounded heights can be absorbed by a common
positive width. This does not assert any asymptotic lower bound on that width. -/
theorem exists_LFunction_bounded_conductor_strip (Q : ℕ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → q ≤ Q → χ ≠ 1 → ∀ s : ℂ,
        1 - δ ≤ s.re → |s.im| ≤ T → DirichletCharacter.LFunction χ s ≠ 0 := by
  induction Q with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro q hqInst χ hq hqQ
    omega
  | succ Q ih =>
    by_cases hQ : 2 ≤ Q + 1
    · letI : NeZero (Q + 1) := ⟨by omega⟩
      obtain ⟨δ₀, hδ₀, hb₀⟩ := ih
      obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_LFunction_common_compact_strip (Q + 1) T
      refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
      intro q hqInst χ hq hqQ hχ s hs ht
      by_cases hle : q ≤ Q
      · exact hb₀ q hqInst χ hq hle hχ s (by linarith [min_le_left δ₀ δ₁]) ht
      · have he : q = Q + 1 := by omega
        subst q
        exact hb₁ χ hχ s (by linarith [min_le_right δ₀ δ₁]) ht
    · refine ⟨1, by norm_num, ?_⟩
      intro q hqInst χ hq hqQ
      omega

/-- A mixed region proved outside a bounded conductor-height box extends
to every primitive character after decreasing its height constant. -/
theorem exists_mixed_region_of_nonvanishing_outside_compact
    (N Q : ℕ) (T cH cS : ℝ) (hcH : 0 < cH)
    (hne : ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ, Q < q ∨ T < |s.im| →
        1 - primitiveZeroFreeWidthAt N cH cS q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ cH' : ℝ, 0 < cH' ∧ cH' ≤ cH ∧ ∀ (q : ℕ) (_ : NeZero q)
      (χ : DirichletCharacter ℂ q), 2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidthAt N cH' cS q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨δ, hδ, hb⟩ := exists_LFunction_bounded_conductor_strip Q T
  let H := min cH (δ / 2)
  have hH : 0 < H := lt_min hcH (by positivity)
  have hHc : H ≤ cH := min_le_left _ _
  have hHδ : H ≤ δ / 2 := min_le_right _ _
  refine ⟨H, hH, hHc, ?_⟩
  intro q hqInst χ hq hχ s hs
  by_cases hout : Q < q ∨ T < |s.im|
  · apply hne q hqInst χ hq hχ s hout
    have hw : primitiveZeroFreeWidthAt N H cS q s.im ≤
        primitiveZeroFreeWidthAt N cH cS q s.im :=
      min_le_min (div_le_div_of_nonneg_right hHc (primitiveZeroFreeHeightLog_pos hq s.im).le) le_rfl
    linarith
  · have hχne : χ ≠ 1 := by
      intro hχone
      have hcond : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
      rw [DirichletCharacter.isPrimitive_def] at hχ
      omega
    have hw : primitiveZeroFreeWidthAt N H cS q s.im ≤ δ := by
      apply (min_le_left _ _).trans
      apply (div_le_iff₀ (primitiveZeroFreeHeightLog_pos hq s.im)).mpr
      have hl := conductor_height_log_ge_threeQuarters q hq s.im
      nlinarith
    push Not at hout
    exact hb q hqInst χ hq hout.1 hχne s (by linarith) hout.2

end Chen
