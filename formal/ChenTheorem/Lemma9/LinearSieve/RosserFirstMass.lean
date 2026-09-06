import ChenTheorem.Lemma9.LinearSieve.RosserStoppingParity

open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem cube_stop_iff_rosserCubeCutoff_lt (D : ℝ) (hD : 0 < D) (p : ℕ) :
    D ≤ (p : ℝ) ^ 3 ↔ rosserCubeCutoff D < p := by
  have hcube := rosserCubeCutoff_cube_bounds D hD
  constructor
  · intro hp
    by_contra h
    have hpm : p ≤ rosserCubeCutoff D := by omega
    have hpow : (p : ℝ) ^ 3 ≤ (rosserCubeCutoff D : ℝ) ^ 3 := by
      gcongr
    linarith
  · intro hp
    apply hcube.2.trans
    have hmp : rosserCubeCutoff D + 1 ≤ p := by omega
    gcongr

/-- The first upper stopping contribution is exactly the finite
Buchstab mass above the strict cube-root cutoff. -/
theorem rosserStoppingMass_one_eq_tail (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (z : ℕ) (D : ℝ) (hD : 0 < D) :
    rosserStoppingMass P 1 (z + 1) true D =
      ∑ p ∈ Ioc (rosserCubeCutoff D) z,
        if p ∈ P then primeDensity p * sieveProduct P primeDensity p else 0 := by
  rw [rosserStoppingMass]
  simp only [Bool.true_eq_false, false_and, if_false, Bool.not_true]
  have hsum : (∑ p : Fin (z + 1), if (p : ℕ) ∈ P then primeDensity p *
      rosserStoppingMass P 0 p false (D / p) else 0) =
      ∑ p ∈ range (z + 1), if p ∈ P then primeDensity p *
        rosserStoppingMass P 0 p false (D / p) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hsum]
  have hpoint : ∀ p ∈ range (z + 1),
      (if p ∈ P then primeDensity p * rosserStoppingMass P 0 p false (D / p) else 0) =
      if rosserCubeCutoff D < p then
        (if p ∈ P then primeDensity p * sieveProduct P primeDensity p else 0) else 0 := by
    intro p _
    by_cases hp : p ∈ P
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      have hstop : D / p ≤ (p : ℝ) ^ 2 ↔ rosserCubeCutoff D < p := by
        rw [div_le_iff₀ hp0]
        have heq : (p : ℝ) ^ 2 * p = (p : ℝ) ^ 3 := by ring
        rw [heq]
        exact cube_stop_iff_rosserCubeCutoff_lt D hD p
      simp only [hp, if_true, rosserStoppingMass, true_and, hstop]
      split_ifs <;> simp
    · simp [hp]
  rw [sum_congr rfl hpoint, ← sum_filter]
  have hset : (range (z + 1)).filter (fun p => rosserCubeCutoff D < p) =
      Ioc (rosserCubeCutoff D) z := by
    ext p
    simp only [mem_filter, mem_range, mem_Ioc]
    omega
  rw [hset]

theorem rosserStoppingMass_one_eq_product_sub (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (z : ℕ) (D : ℝ) (hD : 0 < D)
    (hmz : rosserCubeCutoff D ≤ z) :
    rosserStoppingMass P 1 (z + 1) true D =
      sieveProduct P primeDensity (rosserCubeCutoff D + 1) - sieveProduct P primeDensity (z + 1) := by
  rw [rosserStoppingMass_one_eq_tail P hP z D hD]
  have hset : Ioc (rosserCubeCutoff D) z = Ico (rosserCubeCutoff D + 1) (z + 1) := by
    ext p
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hset, sum_buchstab_mass_Ico P primeDensity _ _ (by omega)]

theorem rosserStoppingMass_one_eq_zero_below_cube (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (z : ℕ) (D : ℝ) (hD : 0 < D)
    (hzm : z ≤ rosserCubeCutoff D) : rosserStoppingMass P 1 (z + 1) true D = 0 := by
  rw [rosserStoppingMass_one_eq_tail P hP z D hD, Ioc_eq_empty_of_le hzm, sum_empty]

theorem rosserRelativeStoppingMass_one_eq_ratio (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (D : ℝ) (hD : 0 < D) (hmz : rosserCubeCutoff D ≤ z) :
    rosserRelativeStoppingMass P 1 (z + 1) true D =
      sieveProduct P primeDensity (rosserCubeCutoff D + 1) /
        sieveProduct P primeDensity (z + 1) - 1 := by
  unfold rosserRelativeStoppingMass
  rw [rosserStoppingMass_one_eq_product_sub P hP z D hD hmz, sub_div,
    div_self (primeDensity_sieveProduct_pos P hP hodd (z + 1)).ne']

end Chen.LinearSieve
