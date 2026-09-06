import ChenTheorem.Lemma6.ZeroFreeWidthGeometry
import ChenTheorem.Lemma6.LFunctionDiskLogDerivative

open Set Metric

namespace Chen

noncomputable def zeroFreeDiskCenter (R t : ℝ) : ℂ :=
  ((1 + R / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I

theorem zeroFreeDiskCenter_re (R t : ℝ) : (zeroFreeDiskCenter R t).re = 1 + R / 4 := by
  simp [zeroFreeDiskCenter]

theorem zeroFreeDiskCenter_im (R t : ℝ) : (zeroFreeDiskCenter R t).im = t := by
  simp [zeroFreeDiskCenter]

/-- The disk whose radius is the mixed width stays inside the full region,
even though the width varies with the imaginary coordinate. -/
theorem zeroFreeDisk_subset_region (N : ℕ) (cH cS : ℝ) (hcH : 0 < cH) (hcS : 0 < cS)
    (q : ℕ) (hq : 2 ≤ q) (t : ℝ)
    (hsmall : primitiveZeroFreeWidthAt N cH cS q t ≤ 1 / 4) :
    ∀ w ∈ ball (zeroFreeDiskCenter (primitiveZeroFreeWidthAt N cH cS q t) t)
      (primitiveZeroFreeWidthAt N cH cS q t),
      1 - primitiveZeroFreeWidthAt N cH cS q w.im < w.re := by
  intro w hw
  let R := primitiveZeroFreeWidthAt N cH cS q t
  have hn : ‖w - zeroFreeDiskCenter R t‖ < R := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hi := Complex.abs_im_le_norm (w - zeroFreeDiskCenter R t)
  rw [Complex.sub_im, zeroFreeDiskCenter_im] at hi
  have hheight : |w.im - t| ≤ 1 / 4 := by change R ≤ 1 / 4 at hsmall; linarith
  have hwidth := primitiveZeroFreeWidthAt_height_comparison N cH cS hcH.le hcS.le q hq t w.im hheight
  have hr := Complex.abs_re_le_norm (w - zeroFreeDiskCenter R t)
  rw [Complex.sub_re, zeroFreeDiskCenter_re] at hr
  have hre := (abs_le.mp hr).1
  change (3 / 4) * R ≤ _ at hwidth
  linarith

theorem half_width_point_mem_threeQuarterDisk (R : ℝ) (s : ℂ)
    (hlo : 1 - R / 2 ≤ s.re) (hhi : s.re ≤ 1 + R) :
    dist s (zeroFreeDiskCenter R s.im) ≤ 3 * R / 4 := by
  have heq : s - zeroFreeDiskCenter R s.im = ((s.re - (1 + R / 4) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [zeroFreeDiskCenter]
  rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Conditional only on nonvanishing in the full mixed region, the disk
estimate applies to every point of the half-width region near the line one.
No logarithmic-derivative estimate is assumed. -/
theorem norm_LFunction_logDeriv_le_of_mixed_region
    (N : ℕ) (cH cS : ℝ) (hcH : 0 < cH) (hcS : 0 < cS)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (hne : ∀ w : ℂ, 1 - primitiveZeroFreeWidthAt N cH cS q w.im < w.re →
      DirichletCharacter.LFunction χ w ≠ 0)
    (s : ℂ) (hsmall : primitiveZeroFreeWidthAt N cH cS q s.im ≤ 1 / 4)
    (hlo : 1 - primitiveZeroFreeWidthAt N cH cS q s.im / 2 ≤ s.re)
    (hhi : s.re ≤ 1 + primitiveZeroFreeWidthAt N cH cS q s.im) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      224 * Real.log (48 * Real.sqrt q * Real.log (2 * q) *
        (‖zeroFreeDiskCenter (primitiveZeroFreeWidthAt N cH cS q s.im) s.im‖ +
          primitiveZeroFreeWidthAt N cH cS q s.im) /
            primitiveZeroFreeWidthAt N cH cS q s.im + 1) /
              primitiveZeroFreeWidthAt N cH cS q s.im := by
  have hR := primitiveZeroFreeWidthAt_pos (N := N) hcH hcS hq s.im
  apply norm_LFunction_logDeriv_le_of_nonvanishing_ball hχ hq _ _ hR hsmall
  · rw [zeroFreeDiskCenter_re]
  · rw [zeroFreeDiskCenter_re]
    linarith
  · intro w hw
    exact hne w (zeroFreeDisk_subset_region N cH cS hcH hcS q hq s.im hsmall w hw)
  · exact half_width_point_mem_threeQuarterDisk _ s hlo hhi

end Chen
