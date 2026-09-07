import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousBuchstab

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem rosserRelativeDefect_le_prefix_add_scaled_weighted (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z m : ℕ) (hmz : m ≤ z) (upper : Bool) (D M : ℝ) (f : ℝ → ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2))
    (hmajor : ∀ p ∈ Ioc m z, p ∈ P →
      rosserRelativeDefect P p (!upper) (D / p) ≤ M * f p) :
    rosserRelativeDefect P (z + 1) upper D ≤ rosserDefectPrefix P z upper D m +
      M * ∑ p ∈ Ioc m z, f p * buchstabCoefficient P z p := by
  have h := rosserRelativeDefect_le_prefix_add_weighted P hP hodd z m hmz upper D
    (fun t => M * f t) hactive hmajor
  simpa only [mul_assoc, mul_sum] using h

/-- A concrete upper/lower Rosser recursion step with the constructed
continuous error series. The same constant works for both bounds. A
nonnegative factor `M` is retained for propagation of iterative errors.
The induction hypotheses on the child states are explicit. -/
theorem rosser_step_continuous_errors_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ M : ℝ, 0 ≤ M →
      (3 < sieveParameter D z →
        (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P → rosserRelativeDefect P p false (D / p) ≤
          M * lowerContinuousError (sieveParameter (D / p) p)) →
        rosserRelativeDefect P (z + 1) true D ≤ rosserDefectPrefix P z true D ⌊w⌋₊ +
          M * upperContinuousError (sieveParameter D z) +
            M * (2 * K * lowerContinuousError (sieveParameter D z - 1) / Real.log w)) ∧
      (2 < sieveParameter D z → ((z + 1 : ℕ) : ℝ) ^ 2 < D →
        (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P → rosserRelativeDefect P p true (D / p) ≤
          M * upperContinuousError (sieveParameter (D / p) p)) →
        rosserRelativeDefect P (z + 1) false D ≤ rosserDefectPrefix P z false D ⌊w⌋₊ +
          M * lowerContinuousError (sieveParameter D z) +
            M * (2 * K * upperContinuousError (sieveParameter D z - 1) / Real.log w)) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_continuous_errors_bound
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz P hP hodd M hM
  have hmz : ⌊w⌋₊ ≤ z := by
    simpa only [Nat.floor_natCast] using Nat.floor_mono hwz
  have hparam : ∀ p ∈ P, sieveParameter (D / p) p = sieveParameter D p - 1 := by
    intro p hp
    apply sieveParameter_div_self D p (by linarith)
    have hp2 : (2 : ℝ) < p := by exact_mod_cast hodd p hp
    linarith
  obtain ⟨hupper, hlower⟩ := hb D w z hD hw hwz P hP hodd
  constructor
  · intro hs hmajor
    have hstep := rosserRelativeDefect_le_prefix_add_scaled_weighted P hP hodd z ⌊w⌋₊ hmz
      true D M (fun t => lowerContinuousError (sieveParameter D t - 1)) (by simp)
      (fun p hp hpP => by
        simpa only [Bool.not_true, ← hparam p hpP] using hmajor p hp hpP)
    have hbound := mul_le_mul_of_nonneg_left (hupper hs) hM
    calc
      _ ≤ _ := hstep
      _ ≤ rosserDefectPrefix P z true D ⌊w⌋₊ +
          M * (upperContinuousError (sieveParameter D z) +
            2 * K * lowerContinuousError (sieveParameter D z - 1) / Real.log w) :=
        _root_.add_le_add le_rfl hbound
      _ = _ := by ring
  · intro hs hactive hmajor
    have hstep := rosserRelativeDefect_le_prefix_add_scaled_weighted P hP hodd z ⌊w⌋₊ hmz
      false D M (fun t => upperContinuousError (sieveParameter D t - 1))
      (by simpa using not_le.mpr hactive)
      (fun p hp hpP => by
        simpa only [Bool.not_false, ← hparam p hpP] using hmajor p hp hpP)
    have hbound := mul_le_mul_of_nonneg_left (hlower hs) hM
    calc
      _ ≤ _ := hstep
      _ ≤ rosserDefectPrefix P z false D ⌊w⌋₊ +
          M * (lowerContinuousError (sieveParameter D z) +
            2 * K * upperContinuousError (sieveParameter D z - 1) / Real.log w) :=
        _root_.add_le_add le_rfl hbound
      _ = _ := by ring

/-- Once the fixed-prefix exact level is reached, the concrete Rosser
step has only the continuous main bound and its explicit density error. -/
theorem rosser_step_continuous_errors_bound_of_exact_prefix :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z →
      rosserExactLevel (⌊w⌋₊ + 1) < D →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ M : ℝ, 0 ≤ M →
      (3 < sieveParameter D z →
        (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P → rosserRelativeDefect P p false (D / p) ≤
          M * lowerContinuousError (sieveParameter (D / p) p)) →
        rosserRelativeDefect P (z + 1) true D ≤ M * upperContinuousError (sieveParameter D z) +
          M * (2 * K * lowerContinuousError (sieveParameter D z - 1) / Real.log w)) ∧
      (2 < sieveParameter D z → ((z + 1 : ℕ) : ℝ) ^ 2 < D →
        (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P → rosserRelativeDefect P p true (D / p) ≤
          M * upperContinuousError (sieveParameter (D / p) p)) →
        rosserRelativeDefect P (z + 1) false D ≤ M * lowerContinuousError (sieveParameter D z) +
          M * (2 * K * upperContinuousError (sieveParameter D z - 1) / Real.log w)) := by
  obtain ⟨K, hK, hb⟩ := rosser_step_continuous_errors_bound
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz hlevel P hP hodd M hM
  simpa only [rosserDefectPrefix_eq_zero_of_level P hP hodd z true D ⌊w⌋₊ hlevel,
    rosserDefectPrefix_eq_zero_of_level P hP hodd z false D ⌊w⌋₊ hlevel, zero_add] using
      hb D w z hD hw hwz P hP hodd M hM

end Chen.LinearSieve
