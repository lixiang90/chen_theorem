/-
The fourth-power Cauchy--Hölder estimate used after equation (15).
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open MeasureTheory Set Real
open scoped Interval

namespace Chen

/-- Weighted Cauchy--Schwarz in the form used for the `A` term after
equation (17).  The exceptional arithmetic factor `c i` is absorbed into
the first second moment through the pointwise bound `c i ^ 2 ≤ I`. -/
theorem weighted_cauchy_sq_of_sq_le
    {ι : Type*} (s : Finset ι) (w c f g : ι → ℝ) {I : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hI : 0 ≤ I) (hcI : ∀ i ∈ s, c i ^ 2 ≤ I) :
    (∑ i ∈ s, w i * c i * f i * g i) ^ 2 ≤
      (I * ∑ i ∈ s, w i * f i ^ 2) *
        ∑ i ∈ s, w i * g i ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => w i * c i * f i * g i)
    (f := fun i => I * (w i * f i ^ 2))
    (g := fun i => w i * g i ^ 2)
    (fun i hi => mul_nonneg hI (mul_nonneg (hw i hi) (sq_nonneg _)))
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i hi => by
      calc
        (w i * c i * f i * g i) ^ 2 =
            c i ^ 2 * (w i ^ 2 * f i ^ 2 * g i ^ 2) := by ring
        _ ≤ I * (w i ^ 2 * f i ^ 2 * g i ^ 2) :=
          mul_le_mul_of_nonneg_right (hcI i hi) (by positivity)
        _ = (I * (w i * f i ^ 2)) * (w i * g i ^ 2) := by ring)
  simpa only [← Finset.mul_sum] using hcs

/-- Weighted three-factor Hölder in the polynomial `2,4,4` form used for
the `B` term after equation (17).  Keeping fourth powers avoids introducing
square roots into the later dyadic estimates. -/
theorem weighted_holder_244_pow_four_of_sq_le
    {ι : Type*} (s : Finset ι) (w c f g h : ι → ℝ) {I : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hI : 0 ≤ I) (hcI : ∀ i ∈ s, c i ^ 2 ≤ I) :
    (∑ i ∈ s, w i * c i * f i * g i * h i) ^ 4 ≤
      (I * ∑ i ∈ s, w i * f i ^ 2) ^ 2 *
        (∑ i ∈ s, w i * g i ^ 4) *
          ∑ i ∈ s, w i * h i ^ 4 := by
  let A : ℝ := ∑ i ∈ s, w i * c i * f i * g i * h i
  let F : ℝ := I * ∑ i ∈ s, w i * f i ^ 2
  let G : ℝ := ∑ i ∈ s, w i * (g i * h i) ^ 2
  let G₄ : ℝ := ∑ i ∈ s, w i * g i ^ 4
  let H₄ : ℝ := ∑ i ∈ s, w i * h i ^ 4
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (hw i hi) (hc i hi)) (hf i hi))
        (hg i hi))
      (hh i hi)
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg hI (Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (sq_nonneg _))
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  have hG₄0 : 0 ≤ G₄ := by
    dsimp only [G₄]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (by positivity)
  have hH₄0 : 0 ≤ H₄ := by
    dsimp only [H₄]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (by positivity)
  have hfirst : A ^ 2 ≤ F * G := by
    simpa only [A, F, G, mul_assoc] using
      weighted_cauchy_sq_of_sq_le s w c f (fun i => g i * h i)
        hw hI hcI
  have hsecond : G ^ 2 ≤ G₄ * H₄ := by
    dsimp only [G, G₄, H₄]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun i => w i * (g i * h i) ^ 2)
      (f := fun i => w i * g i ^ 4)
      (g := fun i => w i * h i ^ 4)
    · intro i hi
      exact mul_nonneg (hw i hi) (by positivity)
    · intro i hi
      exact mul_nonneg (hw i hi) (by positivity)
    · intro i hi
      ring_nf
      exact le_rfl
  change A ^ 4 ≤ F ^ 2 * G₄ * H₄
  calc
    A ^ 4 = (A ^ 2) ^ 2 := by ring
    _ ≤ (F * G) ^ 2 := by gcongr
    _ = F ^ 2 * G ^ 2 := by ring
    _ ≤ F ^ 2 * (G₄ * H₄) := by gcongr
    _ = F ^ 2 * G₄ * H₄ := by ring

/-- Jensen's inequality on an interval of length `2π`, in the exact
fourth-power form needed for Cauchy's formula. -/
theorem intervalIntegral_pow_four_le
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) :
    (∫ t in (0 : ℝ)..2 * Real.pi, g t) ^ 4 ≤
      (2 * Real.pi) ^ 3 *
        ∫ t in (0 : ℝ)..2 * Real.pi, (g t) ^ 4 := by
  let T : ℝ := 2 * Real.pi
  let S : Set ℝ := Set.Ioc 0 T
  have hT : 0 < T := by dsimp only [T]; positivity
  have hSint : IntegrableOn g S := by
    rw [show S = Set.Ioc 0 T by rfl]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      (hg.intervalIntegrable 0 T)
  have hSfour : IntegrableOn (fun t => (g t) ^ 4) S := by
    rw [show S = Set.Ioc 0 T by rfl]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      ((hg.pow 4).intervalIntegrable 0 T)
  have hmeasure : volume S = ENNReal.ofReal T := by
    simp [S, Real.volume_Ioc]
  have hmeasure0 : volume S ≠ 0 := by
    rw [hmeasure, ENNReal.ofReal_ne_zero_iff]
    exact hT
  have hmeasureTop : volume S ≠ ⊤ := by
    rw [hmeasure]
    exact ENNReal.ofReal_ne_top
  have hmeasureReal : volume.real S = T := by
    simp [S, Real.volume_real_Ioc_of_le hT.le]
  have hJ := (convexOn_pow 4 :
    ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ 4)).map_set_average_le
      (continuous_pow 4).continuousOn isClosed_Ici hmeasure0 hmeasureTop
      (Filter.Eventually.of_forall fun t => hg0 t) hSint hSfour
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq] at hJ
  rw [hmeasureReal] at hJ
  simp only [smul_eq_mul] at hJ
  rw [intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_of_le hT.le]
  change (∫ t in S, g t) ^ 4 ≤ T ^ 3 * ∫ t in S, g t ^ 4
  have hTne : T ≠ 0 := ne_of_gt hT
  field_simp [hTne] at hJ ⊢
  nlinarith

/-- Fourth-power form of Cauchy's estimate, retaining the circle integral
instead of replacing it by a supremum. -/
theorem norm_deriv_pow_four_le_circleIntegral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    ‖deriv f c‖ ^ 4 ≤
      (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ‖f (circleMap c r θ)‖ ^ 4 := by
  let g : ℝ → ℝ := fun θ => ‖f (circleMap c r θ)‖
  have hg : Continuous g :=
    hf.continuous.norm.comp (continuous_circleMap c r)
  have hJ := intervalIntegral_pow_four_le g hg
    (fun θ => norm_nonneg _)
  have hcauchy := (hf.differentiableOn).deriv_eq_smul_circleIntegral
    hr (c := c) (R := r)
  have hnorm :
      2 * Real.pi * ‖deriv f c‖ ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r := by
    calc
      2 * Real.pi * ‖deriv f c‖ =
          ‖(2 * Real.pi * Complex.I : ℂ) • deriv f c‖ := by
        simp [Complex.norm_real, Complex.norm_I,
          abs_of_pos Real.pi_pos]
      _ = ‖∮ z in C(c, r), (1 / (z - c) ^ 2) • f z‖ := by
        rw [hcauchy]
      _ ≤ ∫ θ in (0 : ℝ)..2 * Real.pi,
          ‖deriv (circleMap c r) θ •
            ((1 / (circleMap c r θ - c) ^ 2) •
              f (circleMap c r θ))‖ := by
        unfold circleIntegral
        exact intervalIntegral.norm_integral_le_integral_norm
          Real.two_pi_pos.le
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        dsimp only [g]
        simp [deriv_circleMap, circleMap_sub_center,
          norm_pow, norm_circleMap_zero, abs_of_pos hr]
        field_simp [hr.ne']
  rw [intervalIntegral.integral_div] at hnorm
  have hnorm' :
      2 * Real.pi * r * ‖deriv f c‖ ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    calc
      2 * Real.pi * r * ‖deriv f c‖ =
          r * (2 * Real.pi * ‖deriv f c‖) := by ring
      _ ≤ r * ((∫ θ in (0 : ℝ)..2 * Real.pi, g θ) / r) :=
        mul_le_mul_of_nonneg_left hnorm hr.le
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
        field_simp [hr.ne']
  have hpow :
      (2 * Real.pi * r * ‖deriv f c‖) ^ 4 ≤
        (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) ^ 4 := by
    gcongr
  have hcombined := hpow.trans hJ
  let I : ℝ := ∫ θ in (0 : ℝ)..2 * Real.pi, g θ ^ 4
  have hscaled :
      (2 * Real.pi) ^ 3 *
          (‖deriv f c‖ ^ 4 * (2 * Real.pi * r ^ 4)) ≤
        (2 * Real.pi) ^ 3 * I := by
    calc
      (2 * Real.pi) ^ 3 *
          (‖deriv f c‖ ^ 4 * (2 * Real.pi * r ^ 4)) =
        (2 * Real.pi * r * ‖deriv f c‖) ^ 4 := by ring
      _ ≤ (2 * Real.pi) ^ 3 * I := by
        simpa only [I] using hcombined
  have hcancel :
      ‖deriv f c‖ ^ 4 * (2 * Real.pi * r ^ 4) ≤ I :=
    (mul_le_mul_iff_left₀ (pow_pos Real.two_pi_pos 3)).mp (by
      simpa only [mul_comm] using hscaled)
  have hden : 0 < 2 * Real.pi * r ^ 4 := by positivity
  calc
    ‖deriv f c‖ ^ 4 ≤ I / (2 * Real.pi * r ^ 4) :=
      (le_div_iff₀ hden).2 hcancel
    _ = (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ‖f (circleMap c r θ)‖ ^ 4 := by
      dsimp only [I, g]
      rw [div_eq_inv_mul]

end Chen
