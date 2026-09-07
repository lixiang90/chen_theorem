import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabParameter

set_option autoImplicit true
open Finset MeasureTheory
open scoped Classical

namespace Chen.LinearSieve

/-- The small-prime portion of the exact normalized Rosser recursion.
The terminal normalization is at `z+1`; primes up to `m` are retained. -/
noncomputable def rosserDefectPrefix (P : Finset ℕ) (z : ℕ) (upper : Bool)
    (D : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ range (m + 1), buchstabCoefficient P z p *
    rosserRelativeDefect P p (!upper) (D / p)

theorem rosserDefectPrefix_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (upper : Bool) (D : ℝ) (m : ℕ) :
    0 ≤ rosserDefectPrefix P z upper D m := by
  apply sum_nonneg
  intro p _
  exact mul_nonneg (normalized_buchstab_mass_nonneg P hP hodd (z + 1) p)
    (rosserRelativeDefect_nonneg P hP hodd p (!upper) (D / p))

/-- Split an active Rosser recursion at an arbitrary intermediate prime
cutoff, retaining the small-prime contribution exactly. -/
theorem rosserRelativeDefect_split (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z m : ℕ) (hmz : m ≤ z) (upper : Bool) (D : ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) :
    rosserRelativeDefect P (z + 1) upper D = rosserDefectPrefix P z upper D m +
      ∑ p ∈ Ioc m z, buchstabCoefficient P z p *
        rosserRelativeDefect P p (!upper) (D / p) := by
  rw [rosserRelativeDefect_recursion P hP hodd, if_neg hactive]
  have hsum : (∑ p : Fin (z + 1), if (p : ℕ) ∈ P then
      primeDensity p * (sieveProduct P primeDensity p / sieveProduct P primeDensity (z + 1)) *
        rosserRelativeDefect P p (!upper) (D / p) else 0) =
      ∑ p ∈ range (z + 1), buchstabCoefficient P z p *
        rosserRelativeDefect P p (!upper) (D / p) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro p _
    unfold buchstabCoefficient
    split_ifs <;> simp
  rw [hsum]
  have hset : Ioc m z = Ico (m + 1) (z + 1) := by
    ext p
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hset, rosserDefectPrefix]
  exact (sum_range_add_sum_Ico _ (show m + 1 ≤ z + 1 by omega)).symm

/-- A pointwise upper envelope for the later recursion states bounds
the large-prime part without changing the small-prime remainder. -/
theorem rosserRelativeDefect_le_prefix_add_weighted (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z m : ℕ) (hmz : m ≤ z) (upper : Bool) (D : ℝ) (f : ℝ → ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2))
    (hmajor : ∀ p ∈ Ioc m z, p ∈ P → rosserRelativeDefect P p (!upper) (D / p) ≤ f p) :
    rosserRelativeDefect P (z + 1) upper D ≤ rosserDefectPrefix P z upper D m +
      ∑ p ∈ Ioc m z, f p * buchstabCoefficient P z p := by
  rw [rosserRelativeDefect_split P hP hodd z m hmz upper D hactive]
  apply _root_.add_le_add le_rfl
  apply sum_le_sum
  intro p hp
  by_cases hpP : p ∈ P
  · calc
      _ ≤ buchstabCoefficient P z p * f p :=
        mul_le_mul_of_nonneg_left (hmajor p hp hpP)
          (normalized_buchstab_mass_nonneg P hP hodd (z + 1) p)
      _ = _ := mul_comm _ _
  · simp [buchstabCoefficient, hpP]

/-- One rigorous discrete-to-continuous Rosser step. Only the explicit
small-prime remainder and the envelope hypothesis on later states remain
to be controlled in the subsequent iteration argument. -/
theorem rosserRelativeDefect_step_le_parameter_integral :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ upper : Bool, ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2) →
      ∀ H : ℝ → ℝ,
        (∀ s ∈ Set.Icc (sieveParameter D z) (sieveParameter D w), DifferentiableAt ℝ H s) →
        ContinuousOn (deriv H) (Set.Icc (sieveParameter D z) (sieveParameter D w)) →
        (∀ s ∈ Set.Icc (sieveParameter D z) (sieveParameter D w), 0 ≤ H s) →
        (∀ s ∈ Set.Icc (sieveParameter D z) (sieveParameter D w), deriv H s ≤ 0) →
        AntitoneOn (fun s => s * H s) (Set.Icc (sieveParameter D z) (sieveParameter D w)) →
        (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P → rosserRelativeDefect P p (!upper) (D / p) ≤
          H (sieveParameter D p)) →
        rosserRelativeDefect P (z + 1) upper D ≤ rosserDefectPrefix P z upper D ⌊w⌋₊ +
          (1 / sieveParameter D z) *
            (∫ s in Set.Ioc (sieveParameter D z) (sieveParameter D w), H s) +
              2 * K * H (sieveParameter D z) / Real.log w := by
  obtain ⟨K, hK, hbound⟩ := weighted_buchstab_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz P hP hodd upper hactive H hHd hHc hH0 hHderiv hHshape hmajor
  have hmz : ⌊w⌋₊ ≤ z := by
    simpa only [Nat.floor_natCast] using Nat.floor_mono hwz
  have hstep := rosserRelativeDefect_le_prefix_add_weighted P hP hodd z ⌊w⌋₊ hmz upper D
    (fun t => H (sieveParameter D t)) hactive hmajor
  have hb := hbound D w z hD hw hwz P hP hodd H hHd hHc hH0 hHderiv hHshape
  linarith

end Chen.LinearSieve
