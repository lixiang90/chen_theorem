import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousPartialLimits
import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabPartials

set_option autoImplicit true
open Filter Finset
open scoped Topology

namespace Chen.LinearSieve

/-- Passage to the convergent continuous error through the finite prime sum.
The density constant is inherited unchanged from the finite partial sums. -/
theorem weighted_buchstab_lowerContinuousError_auxiliary :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Ioc ⌊w⌋₊ z, lowerContinuousError (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        upperContinuousError (sieveParameter D z) +
          2 * K * ((sieveParameter D z - 1) * lowerAuxiliaryError (sieveParameter D z - 1)) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_lowerContinuousPartial_auxiliary
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz hs P hP hodd
  have hchild : ∀ p ∈ Ioc ⌊w⌋₊ z, 2 ≤ sieveParameter D p - 1 := by
    intro p hp
    have hpw : w < (p : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ w)).mp (mem_Ioc.mp hp).1
    have hpz : (p : ℝ) ≤ z := by exact_mod_cast (mem_Ioc.mp hp).2
    have ha := sieveParameter_antitone hD (show 1 < (p : ℝ) by linarith)
      (show 1 < (z : ℝ) by linarith) hpz
    linarith
  have hsum := tendsto_finsetSum (Ioc ⌊w⌋₊ z) (fun p hp =>
    (tendsto_lowerContinuousPartial (sieveParameter D p - 1) (hchild p hp)).mul_const (buchstabCoefficient P z p))
  have hmain := tendsto_upperContinuousPartial (sieveParameter D z) (by linarith)
  exact le_of_tendsto_of_tendsto hsum (hmain.add_const _) (Filter.Eventually.of_forall
    (fun N => hb N D w z hD hw hwz hs P hP hodd))

/-- Passage to the convergent continuous error through the finite prime sum.
The density constant is inherited unchanged from the finite partial sums. -/
theorem weighted_buchstab_upperContinuousError_auxiliary :
    ∃ K : ℝ, 0 < K ∧ ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 2 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Ioc ⌊w⌋₊ z, upperContinuousError (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        lowerContinuousError (sieveParameter D z) +
          2 * K * ((sieveParameter D z - 1) * upperAuxiliaryError (sieveParameter D z - 1)) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_upperContinuousPartial_auxiliary
  refine ⟨K, hK, ?_⟩
  intro D w z hD hw hwz hs P hP hodd
  have hchild : ∀ p ∈ Ioc ⌊w⌋₊ z, 1 < sieveParameter D p - 1 := by
    intro p hp
    have hpw : w < (p : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ w)).mp (mem_Ioc.mp hp).1
    have hpz : (p : ℝ) ≤ z := by exact_mod_cast (mem_Ioc.mp hp).2
    have ha := sieveParameter_antitone hD (show 1 < (p : ℝ) by linarith)
      (show 1 < (z : ℝ) by linarith) hpz
    linarith
  have hsum := tendsto_finsetSum (Ioc ⌊w⌋₊ z) (fun p hp =>
    (tendsto_upperContinuousPartial (sieveParameter D p - 1) (hchild p hp)).mul_const (buchstabCoefficient P z p))
  have hmain := (tendsto_lowerContinuousPartial (sieveParameter D z) hs.le).comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto hsum (hmain.add_const _) (Filter.Eventually.of_forall
    (fun N => hb N D w z hD hw hwz hs P hP hodd))

end Chen.LinearSieve
