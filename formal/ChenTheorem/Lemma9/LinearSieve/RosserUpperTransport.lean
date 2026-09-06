import ChenTheorem.Lemma9.LinearSieve.RosserContinuousStep

open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem buchstabCoefficient_rescale (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z m p : ℕ) :
    buchstabCoefficient P z p =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        buchstabCoefficient P m p := by
  have hm0 := (primeDensity_sieveProduct_pos P hP hodd (m + 1)).ne'
  have hz0 := (primeDensity_sieveProduct_pos P hP hodd (z + 1)).ne'
  unfold buchstabCoefficient
  split_ifs
  · field_simp
  · ring

theorem rosserDefectPrefix_rescale (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z m : ℕ) (upper : Bool) (D : ℝ) :
    rosserDefectPrefix P z upper D m =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserDefectPrefix P m upper D m := by
  unfold rosserDefectPrefix
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  rw [buchstabCoefficient_rescale P hP hodd z m p]
  ring

theorem rosserDefectPrefix_upper_eq (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z m : ℕ) (D : ℝ) :
    rosserDefectPrefix P z true D m =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserRelativeDefect P (m + 1) true D := by
  have h := rosserRelativeDefect_split P hP hodd m m le_rfl true D (by simp)
  simp only [Ioc_self, sum_empty, add_zero] at h
  rw [rosserDefectPrefix_rescale P hP hodd z m true D, ← h]

theorem rosserRelativeDefect_lower_stopped (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (p : ℕ) (D : ℝ) (hD : D ≤ (p : ℝ) ^ 2) :
    rosserRelativeDefect P p false D = 1 := by
  rw [rosserRelativeDefect_recursion P hP hodd, if_pos ⟨rfl, hD⟩]

/-- Once all later lower branches stop, changing the upper cutoff only
rescales the normalized defect by the exact sieve-product ratio. -/
theorem rosserRelativeDefect_upper_transport (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (m z : ℕ) (hmz : m ≤ z) (D : ℝ)
    (hstop : ∀ p ∈ Ioc m z, p ∈ P → D ≤ (p : ℝ) ^ 3) :
    rosserRelativeDefect P (z + 1) true D =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        (1 + rosserRelativeDefect P (m + 1) true D) - 1 := by
  rw [rosserRelativeDefect_split P hP hodd z m hmz true D (by simp),
    rosserDefectPrefix_upper_eq P hP hodd z m D]
  have htail : (∑ p ∈ Ioc m z, buchstabCoefficient P z p *
      rosserRelativeDefect P p (!true) (D / p)) =
        sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1) - 1 := by
    calc
      _ = ∑ p ∈ Ioc m z, buchstabCoefficient P z p := by
        apply sum_congr rfl
        intro p hp
        by_cases hpP : p ∈ P
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).pos
          have hlevel : D / p ≤ (p : ℝ) ^ 2 := by
            apply (div_le_iff₀ hp0).mpr
            nlinarith [hstop p hp hpP]
          rw [Bool.not_true, rosserRelativeDefect_lower_stopped P hP hodd p (D / p) hlevel, mul_one]
        · simp [buchstabCoefficient, hpP]
      _ = _ := sum_normalized_buchstab_mass P hP hodd m z hmz
  rw [htail]
  ring

theorem rosserRelativeDefect_upper_transport_of_cube (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (m z : ℕ) (hmz : m ≤ z) (D : ℝ) (hD : D ≤ ((m + 1 : ℕ) : ℝ) ^ 3) :
    rosserRelativeDefect P (z + 1) true D =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        (1 + rosserRelativeDefect P (m + 1) true D) - 1 := by
  apply rosserRelativeDefect_upper_transport P hP hodd m z hmz D
  intro p hp _
  apply hD.trans
  have hmp : ((m + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast (show m + 1 ≤ p by have := (mem_Ioc.mp hp).1; omega)
  gcongr

/-- The unnormalized upper Rosser polynomial is exactly constant beyond
the cube-root stopping cutoff. -/
theorem rosserEval_upper_eq_of_cube (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (m z : ℕ) (hmz : m ≤ z) (D : ℝ) (hD : D ≤ ((m + 1 : ℕ) : ℝ) ^ 3) :
    rosserEval P primeDensity (z + 1) true D = rosserEval P primeDensity (m + 1) true D := by
  rw [(rosserEval_eq_product_mul_relativeDefect P hP hodd (z + 1) D).2,
    (rosserEval_eq_product_mul_relativeDefect P hP hodd (m + 1) D).2,
    rosserRelativeDefect_upper_transport_of_cube P hP hodd m z hmz D hD]
  have hz0 := (primeDensity_sieveProduct_pos P hP hodd (z + 1)).ne'
  field_simp
  ring

end Chen.LinearSieve
