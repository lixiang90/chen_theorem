import ChenTheorem.Lemma9.LinearSieve.RosserFullErrorStep
import ChenTheorem.Lemma9.LinearSieve.RosserUnroundedPrefix
import ChenTheorem.Lemma9.LinearSieve.CubeCutoffRounding

open Filter Finset
open scoped Topology

namespace Chen.LinearSieve

theorem rosserRelativeDefect_unrounded_upper_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ,
      growingPrefixCutoff d D ≤ z → growingPrefixIndex d D + 1 ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) z, p ∈ P →
        rosserRelativeDefect P p false (D / p) ≤ lowerContinuousError (sieveParameter (D / p) p) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) →
      rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D z) +
        M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError) := by
  filter_upwards [rosserPartialDefect_fullError_upper_step d δ hd hδ hδ1 hgap,
    rosserPartialPrefix_unrounded_upper_inverse_small d δ ((1 - δ) / 64) (by linarith) (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hb hpref hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro M hM z hwz hmz hs P hP hodd hchild
  have h := hb (z + 1) M hM z hwz hs P hP hodd (by simp) (by
    intro p hp hpP
    have hpz := (mem_Ioc.mp hp).2
    rw [rosserPartialDefect_eq_defect P (z + 1) p false (D / p) (by omega)]
    have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hodd p hpP; omega)
    simpa only [sieveParameter_div_self D p (by linarith : 0 < D) hpR] using hchild p hp hpP)
  rw [rosserPartialDefect_eq_defect P (z + 1 + 1) (z + 1) true D (by omega)] at h
  have hp := hpref P hP hodd (z + 1) z hmz hs true
  have hσ := growingSieveParameter_pos d (Real.log D) hL
  have hE := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D z) upperAuxiliaryError hD
    (by linarith) (upperAuxiliaryError_nonneg _ (by linarith))
  have hn : 0 ≤ (((1 - δ) / 64) / growingSieveParameter d (Real.log D)) *
      inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError := by positivity
  have hpM := hp.trans (le_mul_of_one_le_left hn hM)
  have hfinal := h.trans (_root_.add_le_add (_root_.add_le_add hpM le_rfl) le_rfl)
  have he : (((1 - δ) / 64) / growingSieveParameter d (Real.log D)) +
      (1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D))) =
      1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D)) := by field_simp; ring
  calc
    _ ≤ _ := hfinal
    _ = _ := by rw [← he]; ring

theorem eventually_growingPrefix_before_cube (d : ℝ) (hd : 1 < d) :
    ∀ᶠ D : ℝ in atTop, growingPrefixCutoff d D < rosserCubeCutoff D ∧
      growingPrefixIndex d D + 1 ≤ rosserCubeCutoff D := by
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_growingPrefixCutoff_properties d hd,
    rosserCubeCutoff_tendsto.eventually_ge_atTop 2, hg.eventually_ge_atTop 3,
    sieveParameter_rosserCubeCutoff_tendsto.eventually (gt_mem_nhds (by norm_num : (3 : ℝ) < 4))]
      with D hc hm hσ ht
  rcases hc with ⟨hD, hL, hw, hidx, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hσ
  have hlt : growingPrefixCutoff d D < rosserCubeCutoff D := by
    by_contra h
    have hle := le_of_not_gt h
    have hmR : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
    have ha := sieveParameter_antitone hD hmR (show 1 < growingPrefixCutoff d D by linarith) hle
    rw [sieveParameter_growingPrefixCutoff d D hL] at ha
    linarith
  refine ⟨hlt, ?_⟩
  have h := (Nat.floor_lt (by linarith : 0 ≤ growingPrefixCutoff d D)).mpr hlt
  change growingPrefixIndex d D < rosserCubeCutoff D at h
  omega

/-- A smooth comparison at the strict cube cutoff, with its full contraction
still available for transfer over the initial upper interval. -/
theorem rosserRelativeDefect_cube_upper_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ M : ℝ, 1 ≤ M →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) (rosserCubeCutoff D), p ∈ P →
        rosserRelativeDefect P p false (D / p) ≤ lowerContinuousError (sieveParameter (D / p) p) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) →
      rosserRelativeDefect P (rosserCubeCutoff D + 1) true D ≤
        upperContinuousError (sieveParameter D (rosserCubeCutoff D)) +
        M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D (rosserCubeCutoff D)) upperAuxiliaryError) := by
  filter_upwards [rosserRelativeDefect_unrounded_upper_step d δ hd hδ hδ1 hgap,
    eventually_growingPrefix_before_cube d (by linarith), eventually_gt_atTop (1 : ℝ),
    rosserCubeCutoff_tendsto.eventually_ge_atTop 2] with D hb hp hD hm
  intro M hM P hP hodd hchild
  exact hb M hM _ hp.1.le hp.2 (sieveParameter_rosserCubeCutoff_gt_three D hD hm).le P hP hodd hchild

end Chen.LinearSieve
