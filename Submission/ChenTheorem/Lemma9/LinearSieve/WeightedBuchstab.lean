import Submission.ChenTheorem.Lemma9.LinearSieve.AbelTail
import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabMeasure
import Submission.ChenTheorem.Lemma9.LinearSieve.DensityReal

set_option autoImplicit true
open Finset MeasureTheory
open scoped Classical

namespace Chen.LinearSieve

/-- The atoms of the Buchstab measure, normalized at the terminal cutoff. -/
noncomputable def buchstabCoefficient (P : Finset ℕ) (z p : ℕ) : ℝ :=
  if p ∈ P then primeDensity p *
    (sieveProduct P primeDensity p / sieveProduct P primeDensity (z + 1)) else 0

theorem sum_buchstabCoefficient_prefix (P : Finset ℕ) (z m : ℕ) :
    (∑ p ∈ Icc 0 m, buchstabCoefficient P z p) =
      (1 - sieveProduct P primeDensity (m + 1)) /
        sieveProduct P primeDensity (z + 1) := by
  have hset : Icc 0 m = Ico 0 (m + 1) := by
    ext p
    simp only [mem_Icc, mem_Ico]
    omega
  calc
    _ = (∑ p ∈ Icc 0 m, if p ∈ P then
        primeDensity p * sieveProduct P primeDensity p else 0) /
          sieveProduct P primeDensity (z + 1) := by
      rw [sum_div]
      apply sum_congr rfl
      intro p _
      unfold buchstabCoefficient
      split_ifs <;> ring
    _ = _ := by
      rw [hset, sum_buchstab_mass_Ico P primeDensity 0 (m + 1) (by omega)]
      simp [sieveProduct]

/-- Exact tail at a real cutoff, including the floor convention. -/
theorem coefficientTail_buchstab (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z : ℕ) (t : ℝ) :
    coefficientTail (buchstabCoefficient P z) z t =
      sieveProduct P primeDensity (⌊t⌋₊ + 1) /
        sieveProduct P primeDensity (z + 1) - 1 := by
  unfold coefficientTail
  rw [Nat.floor_natCast, sum_buchstabCoefficient_prefix, sum_buchstabCoefficient_prefix]
  have hz0 := ne_of_gt (primeDensity_sieveProduct_pos P hP hodd (z + 1))
  field_simp
  ring

/-- Weighted Buchstab summation with an exact continuous tail integral. -/
theorem sum_weighted_buchstab_eq_integral (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (w : ℝ) (z : ℕ) (hw : 0 ≤ w) (hwz : w ≤ z) (f : ℝ → ℝ)
    (hfd : ∀ t ∈ Set.Icc w (z : ℝ), DifferentiableAt ℝ f t)
    (hfi : IntegrableOn (deriv f) (Set.Icc w (z : ℝ))) :
    (∑ p ∈ Ioc ⌊w⌋₊ z, f p * buchstabCoefficient P z p) =
      f w * (sieveProduct P primeDensity (⌊w⌋₊ + 1) /
        sieveProduct P primeDensity (z + 1) - 1) +
      ∫ t in Set.Ioc w (z : ℝ), deriv f t *
        (sieveProduct P primeDensity (⌊t⌋₊ + 1) /
          sieveProduct P primeDensity (z + 1) - 1) := by
  simpa only [Nat.floor_natCast, coefficientTail_buchstab P hP hodd] using
    sum_mul_eq_coefficientTail_integral (buchstabCoefficient P z) w z hw hwz f hfd hfi

/-- The continuous dimension-one majorant for the normalized prime tail. -/
noncomputable def buchstabTailMajorant (K z t : ℝ) : ℝ :=
  (1 + K / Real.log t) * (Real.log z / Real.log t) - 1

theorem continuousOn_buchstabTailMajorant (K w z : ℝ) (hw : 2 ≤ w) :
    ContinuousOn (buchstabTailMajorant K z) (Set.Icc w z) := by
  have hlog : ContinuousOn Real.log (Set.Icc w z) :=
    continuousOn_id.log (fun t ht => ne_of_gt (show 0 < id t by dsimp; linarith [ht.1]))
  have hnz : ∀ t ∈ Set.Icc w z, Real.log t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  exact (continuousOn_const.add (continuousOn_const.div hlog hnz)).mul
    (continuousOn_const.div hlog hnz) |>.sub continuousOn_const

/-- Quantitative weighted comparison against the actual prime sieve
measure, uniform in every finite set of odd primes. -/
theorem weighted_buchstab_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ f : ℝ → ℝ,
        (∀ t ∈ Set.Icc w (z : ℝ), DifferentiableAt ℝ f t) →
        IntegrableOn (deriv f) (Set.Icc w (z : ℝ)) → 0 ≤ f w →
        (∀ t ∈ Set.Icc w (z : ℝ), 0 ≤ deriv f t) →
        (∑ p ∈ Ioc ⌊w⌋₊ z, f p * buchstabCoefficient P z p) ≤
          f w * buchstabTailMajorant K z w +
            ∫ t in Set.Ioc w (z : ℝ), deriv f t * buchstabTailMajorant K z t := by
  obtain ⟨K, hK, hbound⟩ := primeDensity_sieveProduct_real_dimension_one
  refine ⟨K, hK, ?_⟩
  intro w z hw hwz P hP hodd f hfd hfi hfw hfderiv
  have htail : ∀ t ∈ Set.Icc w (z : ℝ),
      coefficientTail (buchstabCoefficient P z) z t ≤ buchstabTailMajorant K z t := by
    intro t ht
    rw [coefficientTail_buchstab P hP hodd]
    have hb := hbound t z (hw.trans ht.1) ht.2 P hP hodd
    simpa only [Nat.floor_natCast, buchstabTailMajorant] using sub_le_sub_right hb 1
  have hMi := hfi.mul_continuousOn (continuousOn_buchstabTailMajorant K w z hw) isCompact_Icc
  simpa only [Nat.floor_natCast] using
    sum_mul_le_coefficientTail_majorant (buchstabCoefficient P z) w z (by linarith) hwz
      f (buchstabTailMajorant K z) hfd hfi hfw hfderiv htail hMi

end Chen.LinearSieve
