import Submission.ChenTheorem.Lemma9.LinearSieve.RosserFullErrorParentStep
import Submission.ChenTheorem.Lemma9.LinearSieve.RosserStoppedError

set_option autoImplicit true
open Filter Finset

namespace Chen.LinearSieve

/-- The full finite Rosser defect satisfies the contracted parent step.
No depth truncation or continuous partial sum remains in the statement. -/
theorem rosserRelativeDefect_fullError_upper_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ,
      growingPrefixCutoff d D ≤ z → 3 ≤ sieveParameter D (z + 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) z, p ∈ P →
        rosserRelativeDefect P p false (D / p) ≤
          lowerContinuousError (sieveParameter (D / p) p) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) →
      rosserRelativeDefect P (z + 1) true D ≤
        upperContinuousError (sieveParameter D (z + 1)) +
        M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError) := by
  filter_upwards [rosserPartialDefect_fullError_upper_parent_step d δ hd hδ hδ1 hgap,
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hb hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro M hM z hwz hs P hP hodd hchild
  have hactive : ¬(true = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2) := by
    simp
  have h := hb (z + 1) M hM z hwz hs P hP hodd hactive (by
    intro p hp hpP
    have hpz : p ≤ z := (mem_Ioc.mp hp).2
    rw [rosserPartialDefect_eq_defect P (z + 1) p false (D / p) (by omega)]
    have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hodd p hpP; omega)
    simpa only [sieveParameter_div_self D p (by linarith : 0 < D) hpR] using hchild p hp hpP)
  rwa [rosserPartialDefect_eq_defect P (z + 1 + 1) (z + 1) true D (by omega)] at h

/-- The full finite Rosser defect satisfies the contracted parent step.
No depth truncation or continuous partial sum remains in the statement. -/
theorem rosserRelativeDefect_fullError_lower_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ,
      growingPrefixCutoff d D ≤ z → 2 < sieveParameter D (z + 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) z, p ∈ P →
        rosserRelativeDefect P p true (D / p) ≤
          upperContinuousError (sieveParameter (D / p) p) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError) →
      rosserRelativeDefect P (z + 1) false D ≤
        lowerContinuousError (sieveParameter D (z + 1)) +
        M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError) := by
  filter_upwards [rosserPartialDefect_fullError_lower_parent_step d δ hd hδ hδ1 hgap,
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hb hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro M hM z hwz hs P hP hodd hchild
  have hactive : ¬(false = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2) := by
    rintro ⟨_, hstop⟩
    have hz : 1 < ((z + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h := sieveParameter_le_two_of_stop hD hz hstop
    simp only [Nat.cast_add, Nat.cast_one] at h
    linarith
  have h := hb (z + 1) M hM z hwz hs P hP hodd hactive (by
    intro p hp hpP
    have hpz : p ≤ z := (mem_Ioc.mp hp).2
    rw [rosserPartialDefect_eq_defect P (z + 1) p true (D / p) (by omega)]
    have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hodd p hpP; omega)
    simpa only [sieveParameter_div_self D p (by linarith : 0 < D) hpR] using hchild p hp hpP)
  rwa [rosserPartialDefect_eq_defect P (z + 1 + 1) (z + 1) false D (by omega)] at h

end Chen.LinearSieve
