import Submission.ChenTheorem.Lemma9.LinearSieve.RosserInitialErrorTransfer
import Submission.ChenTheorem.Lemma9.LinearSieve.RosserInductionParameters
import Submission.ChenTheorem.Lemma9.LinearSieve.RosserFullDefectStep
import Submission.ChenTheorem.Lemma9.LinearSieve.RosserBoundedLevel

set_option autoImplicit true
open Filter Finset

namespace Chen.LinearSieve

/-- A uniform comparison for the actual total Rosser defects. Strong
induction on the finite cutoff discharges every child estimate; one multiplier
handles all levels, cutoffs and finite sets of odd primes. -/
theorem rosserRelativeDefect_uniform_error (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ z : ℕ, 2 ≤ z → ∀ D : ℝ, 1 < D →
      (1 < sieveParameter D (z + 1) →
        rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D (z + 1)) +
          M * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError) ∧
      (2 < sieveParameter D (z + 1) →
        rosserRelativeDefect P (z + 1) false D ≤ lowerContinuousError (sieveParameter D (z + 1)) +
          M * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError) := by
  have hevent := (rosserRelativeDefect_fullError_upper_step d δ hd hδ hδ1 hgap).and
    ((rosserRelativeDefect_fullError_lower_step d δ hd hδ hδ1 hgap).and
    ((rosserRelativeDefect_initial_upper_step d δ hd hδ hδ1 hgap).and
    ((rosserRelativeDefect_growing_parameter d δ (by linarith)).and
    ((eventually_growingPrefixCutoff_properties d (by linarith)).and
      (rosserCubeCutoff_tendsto.eventually_ge_atTop 2)))))
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hevent
  let B := max B₀ 2
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨M, hM, hbase⟩ := rosserRelativeDefect_bounded_level d δ B hδ hB
  have hM0 : 0 ≤ M := by linarith
  refine ⟨M, hM, ?_⟩
  intro P hP hodd z
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro hz D hD
    by_cases hDB : D ≤ B
    · constructor
      · intro hs
        exact (hbase D hD hDB z hz hs P hP hodd true).1.trans
          (le_add_of_nonneg_left (upperContinuousError_bounds _ hs).1)
      · intro hs
        exact (hbase D hD hDB z hz (by linarith) P hP hodd false).2.trans
          (le_add_of_nonneg_left (lowerContinuousError_bounds _ hs.le).1)
    · have hDB₀ : B₀ ≤ D := (le_max_left _ _).trans (le_of_not_ge hDB)
      rcases hB₀ D hDB₀ with ⟨hupper, hlower, hinitial, hlarge, hcut, hcube⟩
      rcases hcut with ⟨_, hL, hw, hm, hσlo, hσhi, hlevel⟩
      have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
      have hz1 : 1 < (z : ℝ) + 1 := by linarith
      have hs0 := sieveParameter_pos hD hz1
      have hσ := growingSieveParameter_pos d (Real.log D) hL
      have hcoef : 1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D)) ≤ 1 := by
        have h := div_nonneg (show 0 ≤ 1 - δ by linarith) (show 0 ≤ 64 * growingSieveParameter d (Real.log D) by positivity)
        linarith
      have relax (H : ℝ → ℝ) (hH : 0 ≤ H (sieveParameter D (z + 1))) :
          M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
            inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) H) ≤
          M * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) H := by
        apply mul_le_mul_of_nonneg_left _ hM0
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef
          (inflatedAuxiliaryError_nonneg d δ D _ H hD hs0.le hH)
      by_cases hzm : z ≤ growingPrefixIndex d D
      · have hst : sieveParameter D (growingPrefixIndex d D + 1) ≤ sieveParameter D (z + 1) :=
          sieveParameter_antitone hD hz1
            (show 1 < (growingPrefixIndex d D : ℝ) + 1 by exact_mod_cast (show 1 < growingPrefixIndex d D + 1 by omega))
            (show (z : ℝ) + 1 ≤ (growingPrefixIndex d D : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hzm 1)
        have he : Real.exp (-sieveParameter D (z + 1)) ≤ M :=
          (Real.exp_le_one_iff.mpr (by linarith)).trans hM
        have hb := hlarge z hz (hσlo.trans hst) P hP hodd
        constructor
        · intro hs
          exact ((hb true).1.trans (mul_le_mul_of_nonneg_right he
            (inflatedAuxiliaryError_nonneg d δ D _ upperAuxiliaryError hD hs0.le
              (upperAuxiliaryError_nonneg _ hs)))).trans
            (le_add_of_nonneg_left (upperContinuousError_bounds _ hs).1)
        · intro hs
          exact ((hb false).2.trans (mul_le_mul_of_nonneg_right he
            (inflatedAuxiliaryError_nonneg d δ D _ lowerAuxiliaryError hD hs0.le
              (lowerAuxiliaryError_nonneg _ hs0)))).trans
            (le_add_of_nonneg_left (lowerContinuousError_bounds _ hs.le).1)
      · have hwz : growingPrefixCutoff d D ≤ z := by
          have hf := Nat.lt_floor_add_one (growingPrefixCutoff d D)
          have hmz : growingPrefixIndex d D + 1 ≤ z := by omega
          exact hf.le.trans (show ((⌊growingPrefixCutoff d D⌋₊ : ℕ) : ℝ) + 1 ≤ z by exact_mod_cast hmz)
        have child (p : ℕ) (hpP : p ∈ P) (hpz : p ≤ z) (hDp : 1 < D / p) :=
          ih (p - 1) (show p - 1 < z by have := hodd p hpP; omega)
            (show 2 ≤ p - 1 by have := hodd p hpP; omega) (D / p) hDp
        have child' (p : ℕ) (hpP : p ∈ P) (hpz : p ≤ z) (hDp : 1 < D / p) :
            (1 < sieveParameter (D / p) p → rosserRelativeDefect P p true (D / p) ≤
              upperContinuousError (sieveParameter (D / p) p) +
                M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError) ∧
            (2 < sieveParameter (D / p) p → rosserRelativeDefect P p false (D / p) ≤
              lowerContinuousError (sieveParameter (D / p) p) +
                M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) := by
          have hp1 : 1 ≤ p := by have := hodd p hpP; omega
          simpa only [Nat.sub_add_cancel hp1, Nat.cast_sub hp1, Nat.cast_one, sub_add_cancel] using child p hpP hpz hDp
        constructor
        · intro hs
          by_cases hs3 : 3 ≤ sieveParameter D (z + 1)
          · have hb := hupper M hM z hwz hs3 P hP hodd (by
              intro p hp hpP
              have hpz := (mem_Ioc.mp hp).2
              have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hodd p hpP; omega)
              have hst := strictAntiOn_sieveParameter hD hpR hz1 (show (p : ℝ) < (z : ℝ) + 1 by exact_mod_cast (show p < z + 1 by omega))
              have hDp := child_level_gt_one hD hpR (by linarith)
              apply (child' p hpP hpz hDp).2
              rw [sieveParameter_div_self D p (by linarith) hpR]
              linarith)
            exact hb.trans (_root_.add_le_add le_rfl (relax upperAuxiliaryError (upperAuxiliaryError_nonneg _ hs)))
          · have hs3' := le_of_not_ge hs3
            have hmz := rosserCubeCutoff_le_of_actual_parameter D hD hcube z hz hs3'
            have ht := sieveParameter_rosserCubeCutoff_gt_three D hD hcube
            exact hinitial M hM z hz hs hs3' P hP hodd (by
              intro p hp hpP
              have hpm := (mem_Ioc.mp hp).2
              have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hodd p hpP; omega)
              have hmR : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
              have hst := sieveParameter_antitone hD hpR hmR (show (p : ℝ) ≤ rosserCubeCutoff D by exact_mod_cast hpm)
              have hDp := child_level_gt_one hD hpR (by linarith)
              apply (child' p hpP (hpm.trans hmz) hDp).2
              rw [sieveParameter_div_self D p (by linarith) hpR]
              linarith)
        · intro hs
          have hb := hlower M hM z hwz hs P hP hodd (by
            intro p hp hpP
            have hpz := (mem_Ioc.mp hp).2
            have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hodd p hpP; omega)
            have hst := strictAntiOn_sieveParameter hD hpR hz1 (show (p : ℝ) < (z : ℝ) + 1 by exact_mod_cast (show p < z + 1 by omega))
            have hDp := child_level_gt_one hD hpR (by linarith)
            apply (child' p hpP hpz hDp).1
            rw [sieveParameter_div_self D p (by linarith) hpR]
            linarith)
          exact hb.trans (_root_.add_le_add le_rfl (relax lowerAuxiliaryError (lowerAuxiliaryError_nonneg _ hs0)))

end Chen.LinearSieve
