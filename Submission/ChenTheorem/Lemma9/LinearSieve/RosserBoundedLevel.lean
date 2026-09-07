import Submission.ChenTheorem.Lemma9.LinearSieve.RosserMassLogBound
import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryError
import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryLowerBound

set_option autoImplicit true
open Finset

namespace Chen.LinearSieve

/-- A depth-independent bound, including levels below the asymptotic threshold. -/
theorem rosserRelativeDefect_dimension_one_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ upper : Bool, ∀ D : ℝ,
      rosserRelativeDefect P (z + 1) upper D ≤
        ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) ^ 2 := by
  obtain ⟨K, hK, hb⟩ := primeDensityMass_dimension_one
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd upper D
  obtain ⟨_, hexp, hinv⟩ := hb z hz P hP hodd
  have hdef := (rosserDefect_partial_bounds P hP hodd 0 (z + 1) upper D).2
  simp only [range_zero, sum_empty, sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_mul] at hdef
  have hV := primeDensity_sieveProduct_pos P hP hodd (z + 1)
  unfold rosserRelativeDefect
  rw [div_eq_mul_inv, pow_two]
  exact (mul_le_mul_of_nonneg_right hdef (inv_nonneg.mpr hV.le)).trans
    (mul_le_mul hexp hinv (inv_nonneg.mpr hV.le) ((Real.exp_pos _).le.trans hexp))

theorem inflatedAuxiliaryError_bounded_level_lower (d δ D B s c : ℝ) (H : ℝ → ℝ)
    (hδ : 0 ≤ δ) (hD : 1 < D) (hDB : D ≤ B) (hs : 1 ≤ s)
    (hc : 0 ≤ c) (hcH : c ≤ H s) :
    (Real.log B) ^ (-δ) * c ≤ inflatedAuxiliaryError d δ D s H := by
  have hH := hc.trans hcH
  have hp := Real.rpow_le_rpow_of_nonpos (Real.log_pos hD)
    (Real.log_le_log (by linarith : 0 < D) hDB) (by linarith : -δ ≤ 0)
  have hcs : c ≤ s * H s := hcH.trans (le_mul_of_one_le_left hH hs)
  have h := mul_le_mul hp hcs hc (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
  apply h.trans
  simpa only [auxiliaryErrorScale, mul_assoc] using
    auxiliaryErrorScale_le_inflated d δ D s H hD (by linarith) hH

theorem sieveParameter_bounded_level {D B : ℝ} {z : ℕ}
    (hD : 1 < D) (hDB : D ≤ B) (hz : 2 ≤ z) :
    sieveParameter D z ≤ Real.log B / Real.log 2 := by
  unfold sieveParameter
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hzR
  have hlogD := Real.log_le_log (by linarith : 0 < D) hDB
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  calc
    Real.log D / Real.log z ≤ Real.log D / Real.log 2 :=
      div_le_div_of_nonneg_left (Real.log_pos hD).le hlog2 hlogz
    _ ≤ Real.log B / Real.log 2 := div_le_div_of_nonneg_right hlogD hlog2.le

/-- One multiplier handles all bounded levels, both signs, both auxiliary
functions and every finite odd prime set. It is independent of the cutoff. -/
theorem rosserRelativeDefect_bounded_level (d δ B : ℝ) (hδ : 0 ≤ δ) (hB : 1 < B) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 < D → D ≤ B → ∀ z : ℕ, 2 ≤ z →
      1 < sieveParameter D (z + 1) → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ upper : Bool,
      (rosserRelativeDefect P (z + 1) upper D ≤
        M * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError) ∧
      (rosserRelativeDefect P (z + 1) upper D ≤
        M * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError) := by
  obtain ⟨K, hK, hb⟩ := rosserRelativeDefect_dimension_one_bound
  let T := max 3 (Real.log B / Real.log 2)
  let c := min (upperAuxiliaryError T) (lowerAuxiliaryError T)
  let q := (Real.log B) ^ (-δ) * c
  let A := (1 + K / Real.log 2) * (Real.log B / Real.log 2)
  let M := max 1 (A ^ 2 / q)
  have hT : 3 ≤ T := le_max_left _ _
  have hc : 0 < c := lt_min (upperAuxiliaryError_pos T (by linarith))
    (lowerAuxiliaryError_pos T (by linarith))
  have hq : 0 < q := mul_pos (Real.rpow_pos_of_pos (Real.log_pos hB) _) hc
  have hM : 1 ≤ M := le_max_left _ _
  have hMq : A ^ 2 ≤ M * q := (div_le_iff₀ hq).mp (le_max_right _ _)
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hcoef : 0 ≤ 1 + K / Real.log 2 := by positivity
  refine ⟨M, hM, ?_⟩
  intro D hD hDB z hz hs P hP hodd upper
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz1 : 0 < Real.log ((z : ℝ) + 1) := Real.log_pos (by linarith)
  have hzD : (z : ℝ) + 1 < D := by
    apply (Real.log_lt_log_iff (by linarith) (by linarith)).mp
    have h := (lt_div_iff₀ hlogz1).mp hs
    simpa only [one_mul] using h
  have hzB : (z : ℝ) ≤ B := by linarith
  have hlogzB := Real.log_le_log (by linarith : (0 : ℝ) < z) hzB
  have ha : (1 + K / Real.log 2) * (Real.log z / Real.log 2) ≤ A :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogzB hlog2.le) hcoef
  have ha0 : 0 ≤ (1 + K / Real.log 2) * (Real.log z / Real.log 2) := by
    have := (Real.log_pos (by linarith : (1 : ℝ) < z)).le
    positivity
  have hdef := (hb z hz P hP hodd upper D).trans (pow_le_pow_left₀ ha0 ha 2)
  have hsT : sieveParameter D (z + 1) ≤ T := by
    have h := sieveParameter_bounded_level hD hDB (show 2 ≤ z + 1 by omega)
    simp only [Nat.cast_add, Nat.cast_one] at h
    exact h.trans (le_max_right _ _)
  have hcu : c ≤ upperAuxiliaryError (sieveParameter D (z + 1)) :=
    (min_le_left _ _).trans (antitoneOn_upperAuxiliaryError hs (show 1 < T by linarith) hsT)
  have hcl : c ≤ lowerAuxiliaryError (sieveParameter D (z + 1)) :=
    (min_le_right _ _).trans (antitoneOn_lowerAuxiliaryError (show 0 < sieveParameter D (z + 1) by linarith)
      (show 0 < T by linarith) hsT)
  have hu := inflatedAuxiliaryError_bounded_level_lower d δ D B _ c upperAuxiliaryError hδ hD hDB hs.le hc.le hcu
  have hl := inflatedAuxiliaryError_bounded_level_lower d δ D B _ c lowerAuxiliaryError hδ hD hDB hs.le hc.le hcl
  exact ⟨hdef.trans (hMq.trans (mul_le_mul_of_nonneg_left hu (by linarith))),
    hdef.trans (hMq.trans (mul_le_mul_of_nonneg_left hl (by linarith)))⟩

end Chen.LinearSieve
