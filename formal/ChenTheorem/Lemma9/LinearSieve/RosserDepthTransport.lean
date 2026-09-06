import ChenTheorem.Lemma9.LinearSieve.RosserSecondUniform

open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem rosserStoppingPrefix_rescale (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z m : ℕ) (upper : Bool) (D : ℝ) :
    rosserStoppingPrefix P n z upper D m =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserStoppingPrefix P n m upper D m := by
  unfold rosserStoppingPrefix
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  rw [buchstabCoefficient_rescale P hP hodd z m p]
  ring

theorem rosserStoppingPrefix_upper_eq (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z m : ℕ) (D : ℝ) :
    rosserStoppingPrefix P n z true D m =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserRelativeStoppingMass P (n + 1) (m + 1) true D := by
  have h := rosserRelativeStoppingMass_split P hP hodd n m m le_rfl true D (by simp)
  simp only [Ioc_self, sum_empty, add_zero] at h
  rw [rosserStoppingPrefix_rescale P hP hodd n z m true D, ← h]

/-- Stopping immediately contributes only to depth zero; every positive
depth contribution of a stopped lower branch vanishes. -/
theorem rosserRelativeStoppingMass_lower_stopped (P : Finset ℕ)
    (n p : ℕ) (D : ℝ) (hD : D ≤ (p : ℝ) ^ 2) :
    rosserRelativeStoppingMass P (n + 1) p false D = 0 := by
  simp [rosserRelativeStoppingMass, rosserStoppingMass, hD]

/-- Beyond the cube stopping cutoff, each upper depth at least two
changes only by the exact density-product normalization. -/
theorem rosserRelativeStoppingMass_upper_transport (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n m z : ℕ) (hmz : m ≤ z) (D : ℝ)
    (hstop : ∀ p ∈ Ioc m z, p ∈ P → D ≤ (p : ℝ) ^ 3) :
    rosserRelativeStoppingMass P (n + 2) (z + 1) true D =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserRelativeStoppingMass P (n + 2) (m + 1) true D := by
  rw [rosserRelativeStoppingMass_split P hP hodd (n + 1) z m hmz true D (by simp),
    rosserStoppingPrefix_upper_eq P hP hodd (n + 1) z m D]
  have htail : (∑ p ∈ Ioc m z, buchstabCoefficient P z p *
      rosserRelativeStoppingMass P (n + 1) p (!true) (D / p)) = 0 := by
    apply sum_eq_zero
    intro p hp
    by_cases hpP : p ∈ P
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).pos
      have hlevel : D / p ≤ (p : ℝ) ^ 2 := by
        apply (div_le_iff₀ hp0).mpr
        nlinarith [hstop p hp hpP]
      rw [Bool.not_true, rosserRelativeStoppingMass_lower_stopped P n p (D / p) hlevel,
        mul_zero]
    · simp [buchstabCoefficient, hpP]
  rw [htail, add_zero]

theorem rosserRelativeStoppingMass_upper_transport_of_cube (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n m z : ℕ) (hmz : m ≤ z) (D : ℝ) (hD : D ≤ ((m + 1 : ℕ) : ℝ) ^ 3) :
    rosserRelativeStoppingMass P (n + 2) (z + 1) true D =
      (sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1)) *
        rosserRelativeStoppingMass P (n + 2) (m + 1) true D := by
  apply rosserRelativeStoppingMass_upper_transport P hP hodd n m z hmz D
  intro p hp _
  apply hD.trans
  have hmp : ((m + 1 : ℕ) : ℝ) ≤ p := by
    exact_mod_cast (show m + 1 ≤ p by have := (mem_Ioc.mp hp).1; omega)
  gcongr

/-- A bound for the weighted numerator at the stopping cutoff transfers
to any later cutoff with the same density constant at every depth. -/
theorem rosser_depth_transport_numerator_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ D : ℝ, ∀ m z : ℕ,
      1 < D → 2 ≤ m → m ≤ z → D ≤ ((m + 1 : ℕ) : ℝ) ^ 3 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ B : ℝ, sieveParameter D m * rosserRelativeStoppingMass P (n + 2) (m + 1) true D ≤ B →
        rosserRelativeStoppingMass P (n + 2) (z + 1) true D ≤ B / sieveParameter D z +
          K * B / (Real.log m * sieveParameter D z) := by
  obtain ⟨K, hK, hb⟩ := primeDensity_sieveProduct_dimension_one
  refine ⟨K, hK, ?_⟩
  intro n D m z hD hm hmz hcube P hP hodd B hnum
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hzR : (1 : ℝ) < z := hmR.trans_le (by exact_mod_cast hmz)
  have hsz := sieveParameter_pos hD hzR
  have hlm := Real.log_pos hmR
  have hfac : 0 ≤ 1 + K / Real.log m := by positivity
  have hmain := rosserRelativeStoppingMass_nonneg P hP hodd (n + 2) (m + 1) true D
  have hratio := hb m z hm hmz P hP hodd
  rw [← sieveParameter_ratio D m z hD hmR hzR] at hratio
  rw [rosserRelativeStoppingMass_upper_transport_of_cube P hP hodd n m z hmz D hcube]
  calc
    _ ≤ ((1 + K / Real.log m) * (sieveParameter D m / sieveParameter D z)) *
        rosserRelativeStoppingMass P (n + 2) (m + 1) true D :=
      mul_le_mul_of_nonneg_right hratio hmain
    _ = (1 + K / Real.log m) / sieveParameter D z *
        (sieveParameter D m * rosserRelativeStoppingMass P (n + 2) (m + 1) true D) := by ring
    _ ≤ (1 + K / Real.log m) / sieveParameter D z * B :=
      mul_le_mul_of_nonneg_left hnum (div_nonneg hfac hsz.le)
    _ = _ := by ring

end Chen.LinearSieve
