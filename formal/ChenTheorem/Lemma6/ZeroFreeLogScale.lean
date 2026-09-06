import ChenTheorem.Lemma6.ZeroFreeWidthScale

namespace Chen

/-- The logarithm in the disk estimate is linear in the requested
conductor-height scale; the large growth bound enters only through a logarithm. -/
theorem zeroFreeDisk_log_growth_le_scale (N : ℕ) (cH cS : ℝ)
    (hcH : 0 < cH) (hcS : 0 < cS) (q : ℕ) (hq : 2 ≤ q) (t : ℝ)
    (hsmall : primitiveZeroFreeWidthAt N cH cS q t ≤ 1 / 4) :
    Real.log (48 * Real.sqrt q * Real.log (2 * q) *
      (‖zeroFreeDiskCenter (primitiveZeroFreeWidthAt N cH cS q t) t‖ +
        primitiveZeroFreeWidthAt N cH cS q t) / primitiveZeroFreeWidthAt N cH cS q t + 1) ≤
      (100 + (1 / cH + 1 / cS)) * primitiveZeroFreeScaleAt N q t := by
  let R := primitiveZeroFreeWidthAt N cH cS q t
  let A : ℝ := (q : ℝ) * (|t| + 2)
  let H := primitiveZeroFreeScaleAt N q t
  let K := 1 / cH + 1 / cS
  have hR : 0 < R := primitiveZeroFreeWidthAt_pos (N := N) hcH hcS hq t
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hqA : (q : ℝ) ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hcenter : ‖zeroFreeDiskCenter R t‖ + R ≤ A := by
    apply (zeroFreeDiskCenter_norm_add_radius_le R t hR hsmall).trans
    dsimp [A]
    nlinarith [abs_nonneg t]
  have hsqrt : Real.sqrt (q : ℝ) ≤ A := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg q)
    have hn := Real.sqrt_nonneg (q : ℝ)
    nlinarith
  have hlog : Real.log (2 * (q : ℝ)) ≤ 2 * A := by
    have hl := Real.log_le_self (by positivity : (0 : ℝ) ≤ 2 * q)
    linarith
  have hlogpos : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by linarith)
  have hnum : 48 * Real.sqrt q * Real.log (2 * q) * (‖zeroFreeDiskCenter R t‖ + R) ≤ 96 * A ^ 3 := by
    calc
      _ ≤ 48 * A * (2 * A) * A := by gcongr
      _ = _ := by ring
  have hunit : 1 ≤ A ^ 3 / R := by
    apply (le_div_iff₀ hR).mpr
    have hpow : 1 ≤ A ^ 3 := one_le_pow₀ (by linarith : 1 ≤ A)
    change R ≤ 1 / 4 at hsmall
    linarith
  have hinside : 48 * Real.sqrt q * Real.log (2 * q) * (‖zeroFreeDiskCenter R t‖ + R) / R + 1 ≤
      97 * A ^ 3 / R := by
    have hd := div_le_div_of_nonneg_right hnum hR.le
    simp only [mul_div_assoc] at hd ⊢
    nlinarith
  have hinsidepos : 0 < 48 * Real.sqrt q * Real.log (2 * q) * (‖zeroFreeDiskCenter R t‖ + R) / R + 1 := by positivity
  have hlogbound := Real.log_le_log hinsidepos hinside
  have heq : Real.log (97 * A ^ 3 / R) = Real.log 97 + 3 * Real.log A + Real.log (1 / R) := by
    rw [Real.log_div (by positivity) hR.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_div one_ne_zero hR.ne', Real.log_one]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [heq] at hlogbound
  have h97 : Real.log 97 ≤ (97 : ℝ) := Real.log_le_self (by norm_num)
  have hlogR : Real.log (1 / R) ≤ 1 / R := Real.log_le_self (by positivity)
  have hinv : 1 / R ≤ K * H := inv_primitiveZeroFreeWidthAt_le_scale N cH cS hcH hcS q hq t
  have hL : 0 < Real.log A := primitiveZeroFreeHeightLog_pos hq t
  have hQ : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / N) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hH1 : 1 ≤ H := by dsimp [H, primitiveZeroFreeScaleAt]; linarith
  have hHL : Real.log A ≤ H := by dsimp [H, primitiveZeroFreeScaleAt]; linarith
  change _ ≤ (100 + K) * H
  linarith

end Chen
