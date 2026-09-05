import ChenTheorem.Lemma9.BombieriVinogradov.PerronTypeII
import ChenTheorem.Lemma9.BombieriVinogradov.MeanValue

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Final assembly interface for Vaughan's Type-II mean

The sharp hyperbola is split into rectangles wholly below the boundary and
rectangles crossed by it.  The former use the direct bilinear large sieve;
the latter use the exact adjacent-endpoint Perron representation, so no
sharp-to-smooth correction remains.  This file connects that decomposition
to `primitiveTypeIIMean`.
-/

noncomputable def primitiveTypeIIInteriorMean
    (x U V D Q : ℕ) : ℝ :=
  ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i * ‖sharpTypeIIInteriorSum x U V i.2‖

noncomputable def primitiveTypeIISharpBoundaryMean
    (x U V D Q : ℕ) : ℝ :=
  ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i * ‖sharpTypeIIBoundarySum x U V i.2‖

theorem primitiveTypeIIInteriorMean_nonneg (x U V D Q : ℕ) :
    0 ≤ primitiveTypeIIInteriorMean x U V D Q := by
  unfold primitiveTypeIIInteriorMean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)

theorem primitiveTypeIISharpBoundaryMean_nonneg (x U V D Q : ℕ) :
    0 ≤ primitiveTypeIISharpBoundaryMean x U V D Q := by
  unfold primitiveTypeIISharpBoundaryMean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)

/-- Exact structural reduction of the primitive Type-II mean into the direct
interior and the sharp Perron boundary. -/
theorem primitiveTypeIIMean_le_interior_add_sharpBoundary
    (x U V D Q : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    primitiveTypeIIMean x U V D Q ≤
      primitiveTypeIIInteriorMean x U V D Q +
        primitiveTypeIISharpBoundaryMean x U V D Q := by
  rw [primitiveTypeIIMean_eq_characterIndicesIoc]
  unfold primitiveTypeIIInteriorMean primitiveTypeIISharpBoundaryMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hdecomp :
      vaughanTypeIISum x U V i.2 =
        sharpTypeIIInteriorSum x U V i.2 +
          sharpTypeIIBoundarySum x U V i.2 := by
    rw [vaughanTypeIISum_eq_sharpTypeIISum,
      sharpTypeIISum_eq_interior_add_boundary x U V i.2 hU hV]
  have hnorm :
      ‖vaughanTypeIISum x U V i.2‖ ≤
        ‖sharpTypeIIInteriorSum x U V i.2‖ +
          ‖sharpTypeIIBoundarySum x U V i.2‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  calc
    primitiveDyadicWeight i * ‖vaughanTypeIISum x U V i.2‖ ≤
        primitiveDyadicWeight i *
          (‖sharpTypeIIInteriorSum x U V i.2‖ +
            ‖sharpTypeIIBoundarySum x U V i.2‖) :=
      mul_le_mul_of_nonneg_left hnorm (primitiveDyadicWeight_nonneg i)
    _ = primitiveDyadicWeight i * ‖sharpTypeIIInteriorSum x U V i.2‖ +
          primitiveDyadicWeight i *
            ‖sharpTypeIIBoundarySum x U V i.2‖ := by ring

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

/-- The exact sharp Perron boundary assembly restated for the named mean. -/
theorem primitiveTypeIISharpBoundaryMean_le_common :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          primitiveTypeIISharpBoundaryMean x U V D Q ≤
            ((typeIIBoundaryPairs x U V).card : ℝ) *
              ((1 / (2 * Real.pi)) *
                Real.sqrt
                  (2 * C₀ ^ 2 * C₁ *
                    typeIIBoundaryConductorScale D Q U V x *
                    Real.log (2 * (x : ℝ)) ^ 5) *
                (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
                  2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
                    (x : ℝ))) := by
  rcases sharpTypeIIBoundarySumMean_le_common with
    ⟨C₀, C₁, hC₀, hC₁, hbound⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro x U V D Q hx hU hV hD hDQ
  simpa only [primitiveTypeIISharpBoundaryMean] using
    hbound x U V D Q hx hU hV hD hDQ

/-- Vaughan's three primitive-character means assembled with the exact
sharp-boundary Type-II estimate.  This is the quantitative analytic core
before choosing the cutoffs `U,V` and simplifying logarithmic powers. -/
theorem primitiveAdjustedMean_le_explicit_vaughan_majorants :
    ∃ C₂ Cᵢ₀ Cᵢ₁ Cᵦ₀ Cᵦ₁ : ℝ,
      0 < C₂ ∧ 0 < Cᵢ₀ ∧ 0 < Cᵢ₁ ∧ 0 < Cᵦ₀ ∧ 0 < Cᵦ₁ ∧
      ∀ (x U V D Q : ℕ),
        2 ≤ x → 1 ≤ U → 1 ≤ V → 1 ≤ D → D ≤ Q →
          2 ≤ U * V → U * V ≤ x →
          primitiveAdjustedMean x D Q ≤
            6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
                Real.log (2 * Q) * Real.log x +
              (Q : ℝ) *
                ((V : ℝ) * Real.log x +
                  3 * (C₂ * ((U * V : ℕ) : ℝ) *
                        Real.log ((U * V : ℕ) : ℝ) ^ 5 +
                          ((U * V : ℕ) : ℝ)) *
                    Real.sqrt Q * Real.log (2 * Q)) +
              ((typeIIInteriorPairs x U V).card : ℝ) *
                Real.sqrt
                  (2 * Cᵢ₀ ^ 2 * Cᵢ₁ * (x : ℝ) ^ 2 *
                    typeIIBoundaryConductorScale D Q U V x *
                    Real.log (2 * (x : ℝ)) ^ 5) +
              ((typeIIBoundaryPairs x U V).card : ℝ) *
                ((1 / (2 * Real.pi)) *
                  Real.sqrt
                    (2 * Cᵦ₀ ^ 2 * Cᵦ₁ *
                      typeIIBoundaryConductorScale D Q U V x *
                      Real.log (2 * (x : ℝ)) ^ 5) *
                  (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
                    2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
                      (x : ℝ))) := by
  rcases primitiveTypeITwoMean_le with ⟨C₂, hC₂, htypeITwo⟩
  rcases primitiveTypeIIInteriorMean_le_common with
    ⟨Cᵢ₀, Cᵢ₁, hCᵢ₀, hCᵢ₁, hinterior⟩
  rcases primitiveTypeIISharpBoundaryMean_le_common with
    ⟨Cᵦ₀, Cᵦ₁, hCᵦ₀, hCᵦ₁, hboundary⟩
  refine ⟨C₂, Cᵢ₀, Cᵢ₁, Cᵦ₀, Cᵦ₁,
    hC₂, hCᵢ₀, hCᵢ₁, hCᵦ₀, hCᵦ₁, ?_⟩
  intro x U V D Q hx hU hV hD hDQ hUV hUVx
  have hdecompose := primitiveAdjustedMean_le_vaughanTypeMeans
    x U V D Q hD
  have htypeIOne := primitiveTypeIOneMean_le x U D Q hx hD hDQ
  have htypeITwo' := htypeITwo x U V D Q hx hD hDQ hUV hUVx
  have htypeII := primitiveTypeIIMean_le_interior_add_sharpBoundary
    x U V D Q hU hV
  have hinterior' := hinterior x U V D Q hU hV hD hDQ
  have hboundary' := hboundary x U V D Q hx hU hV hD hDQ
  calc
    primitiveAdjustedMean x D Q ≤
        primitiveTypeIOneMean x U D Q +
          primitiveTypeITwoMean x U V D Q +
            primitiveTypeIIMean x U V D Q := hdecompose
    _ ≤
        (6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
            Real.log (2 * Q) * Real.log x) +
          ((Q : ℝ) *
            ((V : ℝ) * Real.log x +
              3 * (C₂ * ((U * V : ℕ) : ℝ) *
                    Real.log ((U * V : ℕ) : ℝ) ^ 5 +
                      ((U * V : ℕ) : ℝ)) *
                Real.sqrt Q * Real.log (2 * Q))) +
          (primitiveTypeIIInteriorMean x U V D Q +
            primitiveTypeIISharpBoundaryMean x U V D Q) := by
      exact add_le_add (add_le_add htypeIOne htypeITwo') htypeII
    _ ≤
        (6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
            Real.log (2 * Q) * Real.log x +
          (Q : ℝ) *
            ((V : ℝ) * Real.log x +
              3 * (C₂ * ((U * V : ℕ) : ℝ) *
                    Real.log ((U * V : ℕ) : ℝ) ^ 5 +
                      ((U * V : ℕ) : ℝ)) *
                Real.sqrt Q * Real.log (2 * Q))) +
          (((typeIIInteriorPairs x U V).card : ℝ) *
              Real.sqrt
                (2 * Cᵢ₀ ^ 2 * Cᵢ₁ * (x : ℝ) ^ 2 *
                  typeIIBoundaryConductorScale D Q U V x *
                  Real.log (2 * (x : ℝ)) ^ 5) +
            ((typeIIBoundaryPairs x U V).card : ℝ) *
              ((1 / (2 * Real.pi)) *
                Real.sqrt
                  (2 * Cᵦ₀ ^ 2 * Cᵦ₁ *
                    typeIIBoundaryConductorScale D Q U V x *
                    Real.log (2 * (x : ℝ)) ^ 5) *
                (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
                  2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
                    (x : ℝ)))) := by
      exact add_le_add le_rfl (add_le_add hinterior' hboundary')
    _ =
        6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
            Real.log (2 * Q) * Real.log x +
          (Q : ℝ) *
            ((V : ℝ) * Real.log x +
              3 * (C₂ * ((U * V : ℕ) : ℝ) *
                    Real.log ((U * V : ℕ) : ℝ) ^ 5 +
                      ((U * V : ℕ) : ℝ)) *
                Real.sqrt Q * Real.log (2 * Q)) +
          ((typeIIInteriorPairs x U V).card : ℝ) *
            Real.sqrt
              (2 * Cᵢ₀ ^ 2 * Cᵢ₁ * (x : ℝ) ^ 2 *
                typeIIBoundaryConductorScale D Q U V x *
                Real.log (2 * (x : ℝ)) ^ 5) +
          ((typeIIBoundaryPairs x U V).card : ℝ) *
            ((1 / (2 * Real.pi)) *
              Real.sqrt
                (2 * Cᵦ₀ ^ 2 * Cᵦ₁ *
                  typeIIBoundaryConductorScale D Q U V x *
                  Real.log (2 * (x : ℝ)) ^ 5) *
              (4 * perronUpperPoint x * Real.log (1 + (x : ℝ)) +
                2 * (perronUpperPoint x ^ 2 + perronLowerPoint x ^ 2) /
                  (x : ℝ))) := by ring

end Chen.BombieriVinogradov
