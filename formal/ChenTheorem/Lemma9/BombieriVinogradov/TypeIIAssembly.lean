import ChenTheorem.Lemma9.BombieriVinogradov.DyadicTypeII
import ChenTheorem.Lemma9.BombieriVinogradov.MeanValue

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Final assembly interface for Vaughan's Type-II mean

The sharp hyperbola is split into rectangles wholly below the boundary and
rectangles crossed by it.  The former use the direct bilinear large sieve;
the latter use Mellin separation plus an explicit sharp-to-smooth correction.
This file connects that decomposition to `primitiveTypeIIMean`.
-/

noncomputable def primitiveTypeIIInteriorMean
    (x U V D Q : ℕ) : ℝ :=
  ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i * ‖sharpTypeIIInteriorSum x U V i.2‖

noncomputable def primitiveTypeIISmoothedBoundaryMean
    (x U V D Q : ℕ) : ℝ :=
  ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i * ‖smoothedTypeIIBoundarySum x U V i.2‖

noncomputable def primitiveTypeIIBoundaryRemainderMean
    (x U V D Q : ℕ) : ℝ :=
  ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i * ‖typeIIBoundaryRemainderSum x U V i.2‖

theorem primitiveTypeIIInteriorMean_nonneg (x U V D Q : ℕ) :
    0 ≤ primitiveTypeIIInteriorMean x U V D Q := by
  unfold primitiveTypeIIInteriorMean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)

theorem primitiveTypeIISmoothedBoundaryMean_nonneg (x U V D Q : ℕ) :
    0 ≤ primitiveTypeIISmoothedBoundaryMean x U V D Q := by
  unfold primitiveTypeIISmoothedBoundaryMean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)

theorem primitiveTypeIIBoundaryRemainderMean_nonneg (x U V D Q : ℕ) :
    0 ≤ primitiveTypeIIBoundaryRemainderMean x U V D Q := by
  unfold primitiveTypeIIBoundaryRemainderMean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)

/-- Exact structural reduction of the primitive Type-II mean.  The first
two terms now have proved large-sieve/Mellin bounds; only the explicitly
named boundary correction still needs a global estimate. -/
theorem primitiveTypeIIMean_le_interior_add_smoothedBoundary_add_remainder
    (x U V D Q : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    primitiveTypeIIMean x U V D Q ≤
      primitiveTypeIIInteriorMean x U V D Q +
        primitiveTypeIISmoothedBoundaryMean x U V D Q +
          primitiveTypeIIBoundaryRemainderMean x U V D Q := by
  rw [primitiveTypeIIMean_eq_characterIndicesIoc]
  unfold primitiveTypeIIInteriorMean primitiveTypeIISmoothedBoundaryMean
    primitiveTypeIIBoundaryRemainderMean
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hdecomp :=
    vaughanTypeIISum_eq_interior_add_smoothedBoundary_add_remainder
      x U V i.2 hU hV
  have hnorm :
      ‖vaughanTypeIISum x U V i.2‖ ≤
        ‖sharpTypeIIInteriorSum x U V i.2‖ +
          ‖smoothedTypeIIBoundarySum x U V i.2‖ +
            ‖typeIIBoundaryRemainderSum x U V i.2‖ := by
    rw [hdecomp]
    calc
      ‖sharpTypeIIInteriorSum x U V i.2 +
          smoothedTypeIIBoundarySum x U V i.2 +
            typeIIBoundaryRemainderSum x U V i.2‖ ≤
          ‖sharpTypeIIInteriorSum x U V i.2 +
            smoothedTypeIIBoundarySum x U V i.2‖ +
              ‖typeIIBoundaryRemainderSum x U V i.2‖ := norm_add_le _ _
      _ ≤ ‖sharpTypeIIInteriorSum x U V i.2‖ +
            ‖smoothedTypeIIBoundarySum x U V i.2‖ +
              ‖typeIIBoundaryRemainderSum x U V i.2‖ := by
        gcongr
        exact norm_add_le _ _
  calc
    primitiveDyadicWeight i * ‖vaughanTypeIISum x U V i.2‖ ≤
        primitiveDyadicWeight i *
          (‖sharpTypeIIInteriorSum x U V i.2‖ +
            ‖smoothedTypeIIBoundarySum x U V i.2‖ +
              ‖typeIIBoundaryRemainderSum x U V i.2‖) :=
      mul_le_mul_of_nonneg_left hnorm (primitiveDyadicWeight_nonneg i)
    _ = primitiveDyadicWeight i * ‖sharpTypeIIInteriorSum x U V i.2‖ +
          primitiveDyadicWeight i * ‖smoothedTypeIIBoundarySum x U V i.2‖ +
            primitiveDyadicWeight i *
              ‖typeIIBoundaryRemainderSum x U V i.2‖ := by ring

/-- Existing direct-rectangle assembly restated for the named interior mean. -/
theorem primitiveTypeIIInteriorMean_le_directMajorants :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          primitiveTypeIIInteriorMean x U V D Q ≤
            ∑ p ∈ typeIIInteriorPairs x U V,
              Real.sqrt
                (typeIIDirectRectangleMajorant C₀ C₁ D Q
                  (2 ^ p.1 * U) (2 ^ p.1 * U)
                  (2 ^ p.2 * V) (2 ^ p.2 * V)) := by
  rcases sharpTypeIIInteriorSumMean_le_directMajorants with
    ⟨C₀, C₁, hC₀, hC₁, hbound⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hU hV hD hDQ
  simpa only [primitiveTypeIIInteriorMean] using
    hbound x U V D Q hU hV hD hDQ

/-- The direct interior assembly restated with the common conductor scale. -/
theorem primitiveTypeIIInteriorMean_le_common :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          primitiveTypeIIInteriorMean x U V D Q ≤
            ((typeIIInteriorPairs x U V).card : ℝ) *
              Real.sqrt
                (2 * C₀ ^ 2 * C₁ * (x : ℝ) ^ 2 *
                  typeIIBoundaryConductorScale D Q U V x *
                  Real.log (2 * (x : ℝ)) ^ 5) := by
  rcases sharpTypeIIInteriorSumMean_le_common with
    ⟨C₀, C₁, hC₀, hC₁, hbound⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hU hV hD hDQ
  simpa only [primitiveTypeIIInteriorMean] using
    hbound x U V D Q hU hV hD hDQ

/-- Existing boundary Mellin assembly restated for the named mean. -/
theorem primitiveTypeIISmoothedBoundaryMean_le_common :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 3 ≤ Real.log (x : ℝ) →
          1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          primitiveTypeIISmoothedBoundaryMean x U V D Q ≤
            ((typeIIBoundaryPairs x U V).card : ℝ) *
              ((Real.exp 1 * (x : ℝ)) *
                Real.sqrt
                  (2 * C₀ ^ 2 * C₁ *
                    typeIIBoundaryConductorScale D Q U V x *
                    Real.log (2 * (x : ℝ)) ^ 5) *
                Real.log (x : ℝ) ^ 5) := by
  rcases smoothedTypeIIBoundarySumMean_le_common with
    ⟨C₀, C₁, hC₀, hC₁, hbound⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hxlog hU hV hD hDQ
  simpa only [primitiveTypeIISmoothedBoundaryMean] using
    hbound x U V D Q hx hxlog hU hV hD hDQ

end Chen.BombieriVinogradov
