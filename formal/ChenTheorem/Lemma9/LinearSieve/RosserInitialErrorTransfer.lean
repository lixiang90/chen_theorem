import ChenTheorem.Lemma9.LinearSieve.RosserCubeErrorStep
import ChenTheorem.Lemma9.LinearSieve.CubeInitialBudget
import ChenTheorem.Lemma9.LinearSieve.InitialTransferAlgebra

open Filter Finset
open scoped Topology

namespace Chen.LinearSieve

/-- Transfer from the contracted cube-cutoff estimate to the whole initial
upper interval, preserving the same multiplier of the full auxiliary error. -/
theorem eventually_rosser_initial_error_transfer (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ, 2 ≤ z →
      1 < sieveParameter D (z + 1) → sieveParameter D (z + 1) ≤ 3 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeDefect P (rosserCubeCutoff D + 1) true D ≤
        upperContinuousError (sieveParameter D (rosserCubeCutoff D)) +
        M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D (rosserCubeCutoff D)) upperAuxiliaryError) →
      rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D (z + 1)) +
        M * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError := by
  obtain ⟨K, hK, hratio⟩ := primeDensity_sieveProduct_dimension_one
  have hd0 : 0 < d := by linarith
  have hgap1 : δ + 1 / d < 1 := by
    have h := div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) hd0.le
    linarith
  have hε : 0 < (1 - δ) / 512 := by linarith
  have hg := (tendsto_growingSieveParameter_atTop d hd0).comp Real.tendsto_log_atTop
  filter_upwards [eventually_cube_initial_density_budget d δ K ((1 - δ) / 512) (by linarith) hgap1 hε,
    eventually_inflatedUpperError_initial_transfer d δ ((1 - δ) / 512) (by linarith) hε,
    eventually_growingPrefixCutoff_properties d (by linarith),
    rosserCubeCutoff_tendsto.eventually_ge_atTop 2, hg.eventually_ge_atTop 1,
    sieveParameter_rosserCubeCutoff_tendsto.eventually (gt_mem_nhds (by norm_num : (3 : ℝ) < 4))]
      with D hb hi hc hm hσ ht4
  rcases hc with ⟨hD, hL, hw, hidx, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hσ
  let t := sieveParameter D (rosserCubeCutoff D)
  let σ := growingSieveParameter d (Real.log D)
  let r := K / Real.log (rosserCubeCutoff D)
  let x := (1 - δ) / (512 * σ)
  let ρ := 1 - (1 - δ) / (64 * σ)
  have ht : 3 < t := sieveParameter_rosserCubeCutoff_gt_three D hD hm
  have hmR : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
  have hlogm := Real.log_pos hmR
  have hA : 0 < linearSieveInitialConstant := by linarith [linearSieveInitialConstant_ge_three]
  have hr : 0 ≤ r := div_nonneg hK.le hlogm.le
  have hx : 0 ≤ x := by dsimp [x, σ]; positivity
  have hρ : 0 ≤ ρ := by
    have h := (div_le_one (by dsimp [σ]; positivity : 0 < 64 * σ)).mpr
      (show 1 - δ ≤ 64 * σ by change 1 - δ ≤ 64 * growingSieveParameter d (Real.log D); linarith)
    dsimp [ρ]
    linarith
  have hbudget : (Real.log D) ^ δ * (r + (1 + r) * (t - 3) / linearSieveInitialConstant) ≤ x := by
    convert! hb.2 using 1
    dsimp [x, σ]
    ring
  have hrx : r ≤ x := by
    have hC : 0 ≤ r + (1 + r) * (t - 3) / linearSieveInitialConstant := by positivity
    have hrC : r ≤ r + (1 + r) * (t - 3) / linearSieveInitialConstant := le_add_of_nonneg_right (by positivity)
    exact hrC.trans ((le_mul_of_one_le_left hC (Real.one_le_rpow hL.le hδ)).trans hbudget)
  intro M hM z hz hs hs3 P hP hodd hroot
  let s := sieveParameter D (z + 1)
  let E := inflatedAuxiliaryError d δ D s upperAuxiliaryError
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hE : 0 ≤ E := inflatedAuxiliaryError_nonneg d δ D s upperAuxiliaryError hD hs0.le
    (upperAuxiliaryError_nonneg s hs)
  have hM0 : 0 ≤ M := by linarith
  have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hz1 : 1 < (z : ℝ) + 1 := by linarith
  have hmz : rosserCubeCutoff D ≤ z := by
    by_contra h
    have hzm : z + 1 ≤ rosserCubeCutoff D := by omega
    have ha := sieveParameter_antitone hD hz1 hmR (show (z : ℝ) + 1 ≤ rosserCubeCutoff D by exact_mod_cast hzm)
    change t ≤ s at ha
    linarith
  have hR := hratio (rosserCubeCutoff D) z hm hmz P hP hodd
  have hlogz := Real.log_le_log (by linarith : (0 : ℝ) < z) (show (z : ℝ) ≤ z + 1 by linarith)
  have hR' := hR.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogz hlogm.le)
    (show 0 ≤ 1 + r by linarith))
  have he : Real.log ((z : ℝ) + 1) / Real.log (rosserCubeCutoff D) = t / s := by
    dsimp [t, s, sieveParameter]
    have hlogD := (Real.log_pos hD).ne'
    field_simp
  rw [he] at hR'
  have hroot0 : 0 ≤ 1 + rosserRelativeDefect P (rosserCubeCutoff D + 1) true D := by
    have h := rosserRelativeDefect_nonneg P hP hodd (rosserCubeCutoff D + 1) true D
    linarith
  have hprod := mul_le_mul hR' (_root_.add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hroot) hroot0
    (mul_nonneg (show 0 ≤ 1 + r by linarith) (div_nonneg (by linarith : 0 ≤ t) hs0.le))
  have hstart : rosserRelativeDefect P (z + 1) true D ≤
      (1 + r) * (t / s) * (1 + upperContinuousError t +
        M * (ρ * inflatedAuxiliaryError d δ D t upperAuxiliaryError)) - 1 := by
    rw [rosserRelativeDefect_upper_transport_of_cube P hP hodd _ _ hmz D
      (rosserCubeCutoff_cube_bounds D (by linarith)).2]
    convert! sub_le_sub_right hprod 1 using 1
    ring
  have hweight := weighted_upperFunction_le_initial_add t ht.le
  change t * (1 + upperContinuousError t) ≤ linearSieveInitialConstant + (t - 3) at hweight
  have htransfer : t * inflatedAuxiliaryError d δ D t upperAuxiliaryError ≤ (1 + x) * (s * E) := by
    convert! hi.2 s t hs (by linarith) ht4.le using 1
    dsimp [x, σ]
    ring
  have hnum := _root_.add_le_add hweight (mul_le_mul_of_nonneg_left htransfer (mul_nonneg hM0 hρ))
  have hscaled := mul_le_mul_of_nonneg_left hnum (div_nonneg (show 0 ≤ 1 + r by linarith) hs0.le)
  have hmajor : rosserRelativeDefect P (z + 1) true D ≤
      (1 + r) / s * (linearSieveInitialConstant + (t - 3) + M * ρ * ((1 + x) * (s * E))) - 1 := by
    apply hstart.trans
    convert! sub_le_sub_right hscaled 1 using 1
    ring
  have hloss := (initial_density_loss_le_error d δ D s r (t - 3) hD hs hs3 hr (by linarith)).trans
    (mul_le_mul_of_nonneg_right hbudget hE)
  have hlossM := hloss.trans (le_mul_of_one_le_left (mul_nonneg hx hE) hM)
  have halgebra := initial_transfer_absorption (1 - δ) σ r (by linarith) (by linarith) hσ hr hrx
  have hexpand : rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError s +
      (linearSieveInitialConstant * r + (1 + r) * (t - 3)) / s + M * (ρ * (1 + r) * (1 + x)) * E := by
    convert! hmajor using 1
    rw [upperContinuousError_initial s hs hs3]
    field_simp
    ring
  have hfinal := hexpand.trans (_root_.add_le_add (_root_.add_le_add le_rfl hlossM) le_rfl)
  calc
    _ ≤ upperContinuousError s + M * ((x + ρ * (1 + r) * (1 + x)) * E) := by
      convert! hfinal using 1
      ring
    _ ≤ upperContinuousError s + M * E := _root_.add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using mul_le_mul_of_nonneg_right halgebra hE) hM0)

/-- The initial upper interval depends only on smaller lower cutoffs. -/
theorem rosserRelativeDefect_initial_upper_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ, 2 ≤ z →
      1 < sieveParameter D (z + 1) → sieveParameter D (z + 1) ≤ 3 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) (rosserCubeCutoff D), p ∈ P →
        rosserRelativeDefect P p false (D / p) ≤ lowerContinuousError (sieveParameter (D / p) p) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) →
      rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D (z + 1)) +
        M * inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError := by
  filter_upwards [eventually_rosser_initial_error_transfer d δ hd hδ hδ1 hgap,
    rosserRelativeDefect_cube_upper_step d δ hd hδ hδ1 hgap] with D ht hc
  intro M hM z hz hs hs3 P hP hodd hchild
  exact ht M hM z hz hs hs3 P hP hodd (hc M hM P hP hodd hchild)

end Chen.LinearSieve
