import ChenTheorem.Lemma6.ZeroFreeLogScale
import ChenTheorem.Lemma6.LogDerivBound

namespace Chen

/-- The global logarithmic-derivative condition follows from the mixed
nonvanishing region. Its constant depends only on the two region constants. -/
theorem norm_LFunction_logDeriv_le_scale_sq (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcHsmall : cH ≤ 1 / 8) (hcS : 0 < cS)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (hne : ∀ w : ℂ, 1 - primitiveZeroFreeWidthAt N cH cS q w.im < w.re →
      DirichletCharacter.LFunction χ w ≠ 0)
    (s : ℂ) (hs : 1 - primitiveZeroFreeWidthAt N cH cS q s.im / 2 ≤ s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      (224 * (100 + (1 / cH + 1 / cS)) * (1 / cH + 1 / cS) +
        4 * (1 / cH + 1 / cS) ^ 2) * primitiveZeroFreeScaleAt N q s.im ^ 2 := by
  let R := primitiveZeroFreeWidthAt N cH cS q s.im
  let H := primitiveZeroFreeScaleAt N q s.im
  let K := 1 / cH + 1 / cS
  have hR : 0 < R := primitiveZeroFreeWidthAt_pos (N := N) hcH hcS hq s.im
  have hsmall : R ≤ 1 / 4 := primitiveZeroFreeWidthAt_le_quarter N cH cS hcHsmall q hq s.im
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 < H := by
    have hL := primitiveZeroFreeHeightLog_pos hq s.im
    have hQ := Real.rpow_nonneg (Nat.cast_nonneg q) ((1 : ℝ) / N)
    dsimp [H, primitiveZeroFreeScaleAt]
    linarith
  have hinv : 1 / R ≤ K * H := inv_primitiveZeroFreeWidthAt_le_scale N cH cS hcH hcS q hq s.im
  change _ ≤ (224 * (100 + K) * K + 4 * K ^ 2) * H ^ 2
  by_cases hnear : s.re ≤ 1 + R
  · have hd := norm_LFunction_logDeriv_le_of_mixed_region N cH cS hcH hcS hq hχ hne s hsmall hs hnear
    have hg := zeroFreeDisk_log_growth_le_scale N cH cS hcH hcS q hq s.im hsmall
    apply hd.trans
    calc
      _ ≤ 224 * ((100 + K) * H) / R :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num)) hR.le
      _ = (224 * ((100 + K) * H)) * (1 / R) := by ring
      _ ≤ (224 * ((100 + K) * H)) * (K * H) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (K * H)]
  · have hgap : 0 < s.re - 1 := by linarith
    have hd := (lemma6_norm_logDeriv_le_majorant χ (by linarith : 1 < s.re)).trans
      (lemma6LogDerivMajorant_le hgap (show s.re = 1 + (s.re - 1) by ring))
    have hdist : 1 / (s.re - 1) ≤ 1 / R := one_div_le_one_div_of_le hR (by linarith)
    have hsq : (1 / (s.re - 1)) ^ 2 ≤ (K * H) ^ 2 :=
      sq_le_sq₀ (by positivity) (by positivity) |>.mpr (hdist.trans hinv)
    apply hd.trans
    rw [show 4 / (s.re - 1) ^ 2 = 4 * (1 / (s.re - 1)) ^ 2 by rw [div_pow, one_pow]; ring]
    have hpos : 0 ≤ 224 * (100 + K) * K * H ^ 2 := by positivity
    nlinarith

end Chen
