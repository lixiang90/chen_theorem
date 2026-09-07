import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit true

open Set Metric
open scoped Classical

namespace Chen

/-- On every bounded height range, a continuous function that is nonzero
on the closed right half-plane is also nonzero in some slightly wider strip. -/
theorem exists_compact_zeroFree_strip (f : ℂ → ℂ) (hf : Continuous f)
    (hne : ∀ s : ℂ, 1 ≤ s.re → f s ≠ 0) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, 1 - δ ≤ s.re → |s.im| ≤ T → f s ≠ 0 := by
  let S : Set ℂ := (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) '' Icc (-T) T
  have hcompact : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hopen : IsOpen {s : ℂ | f s ≠ 0} := (isClosed_eq hf continuous_const).isOpen_compl
  have hsub : S ⊆ {s : ℂ | f s ≠ 0} := by
    rintro s ⟨t, ht, rfl⟩
    exact hne _ (by simp)
  obtain ⟨δ, hδ, hthick⟩ := hcompact.exists_cthickening_subset_open hopen hsub
  refine ⟨δ, hδ, ?_⟩
  intro s hs hT
  by_cases hright : 1 ≤ s.re
  · exact hne s hright
  · apply hthick
    apply mem_cthickening_of_dist_le s ((1 : ℂ) + (s.im : ℂ) * Complex.I) δ S
    · exact ⟨s.im, abs_le.mp hT, rfl⟩
    · have heq : s - ((1 : ℂ) + (s.im : ℂ) * Complex.I) = ((s.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith

/-- Finitely many functions admit a common strip at every bounded height. -/
theorem exists_uniform_compact_zeroFree_strip {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (hf : ∀ i, Continuous (f i))
    (hne : ∀ i (s : ℂ), 1 ≤ s.re → f i s ≠ 0) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i (s : ℂ), 1 - δ ≤ s.re → |s.im| ≤ T → f i s ≠ 0 := by
  have hcont : Continuous (fun s => ∏ i, f i s) := continuous_finsetProd _ (fun i _ => hf i)
  have hprod : ∀ s : ℂ, 1 ≤ s.re → (∏ i, f i s) ≠ 0 := by
    intro s hs
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hne i s hs)
  obtain ⟨δ, hδ, hb⟩ := exists_compact_zeroFree_strip _ hcont hprod T
  exact ⟨δ, hδ, fun i s hs ht => Finset.prod_ne_zero_iff.mp (hb s hs ht) i (Finset.mem_univ i)⟩

/-- This unconditional local strip will absorb fixed characters and bounded
height ranges when establishing the uniform zero-free-region theorem. -/
theorem exists_LFunction_compact_zeroFree_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, 1 - δ ≤ s.re → |s.im| ≤ T →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  exact exists_compact_zeroFree_strip _ (DirichletCharacter.differentiable_LFunction hχ).continuous
    (fun s hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs) T

end Chen
