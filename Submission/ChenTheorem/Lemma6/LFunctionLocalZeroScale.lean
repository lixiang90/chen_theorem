import Submission.ChenTheorem.Lemma6.LFunctionLocalZeroLogDerivative
import Submission.ChenTheorem.Lemma6.ZeroFreeWidthScale

set_option autoImplicit true
namespace Chen

theorem dirichletZeroDisk_log_bound_le (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    Real.log (5 * dirichletZeroDiskBound q t) + 1 ≤
      91 * Real.log ((q : ℝ) * (|t| + 2)) := by
  let A : ℝ := (q : ℝ) * (|t| + 2)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 4 ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hqA : (q : ℝ) ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hc : ‖dirichletZeroDiskCenter t‖ + 1 / 2 ≤ A := by
    have hn : ‖dirichletZeroDiskCenter t‖ ≤ 5 / 4 + |t| := by
      unfold dirichletZeroDiskCenter
      apply (norm_add_le _ _).trans_eq
      norm_num [norm_mul]
    dsimp [A]
    nlinarith [abs_nonneg t]
  have hsqrt : Real.sqrt (q : ℝ) ≤ A := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg q)
    have hn := Real.sqrt_nonneg (q : ℝ)
    nlinarith
  have hl : Real.log (2 * (q : ℝ)) ≤ 2 * A := by
    have h := Real.log_le_self (by positivity : (0 : ℝ) ≤ 2 * q)
    linarith
  have hlpos : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hnum : 6 * Real.sqrt q * Real.log (2 * q) * (‖dirichletZeroDiskCenter t‖ + 1 / 2) ≤
      12 * A ^ 3 := by
    calc
      _ ≤ 6 * A * (2 * A) * A := by gcongr
      _ = _ := by ring
  have hApow : 1 ≤ A ^ 3 := one_le_pow₀ (by linarith : 1 ≤ A)
  have hM : dirichletZeroDiskBound q t ≤ 13 * A ^ 3 := by
    unfold dirichletZeroDiskBound
    linarith
  have hMpos := dirichletZeroDiskBound_ge_one q hq t
  have hlog := Real.log_le_log (by linarith : 0 < 5 * dirichletZeroDiskBound q t)
    (show 5 * dirichletZeroDiskBound q t ≤ 65 * A ^ 3 by linarith)
  rw [Real.log_mul (by norm_num : (65 : ℝ) ≠ 0) (by positivity : A ^ 3 ≠ 0),
    Real.log_pow] at hlog
  have h65 : Real.log 65 ≤ (65 : ℝ) := Real.log_le_self (by norm_num)
  have hL : (3 / 4 : ℝ) ≤ Real.log A := conductor_height_log_ge_threeQuarters q hq t
  change _ ≤ 91 * Real.log A
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- The local zero-pole expansion has an absolute conductor-height error,
uniform in every primitive character, without assuming a zero-free region. -/
theorem norm_LFunction_logDeriv_sub_local_zero_poles_le_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (t : ℝ)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32)
    (hne : DirichletCharacter.LFunction χ s ≠ 0) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
      diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w))
        (3 / 8) (s - dirichletZeroDiskCenter t)‖ ≤
      60000 * Real.log ((q : ℝ) * (|t| + 2)) := by
  apply (norm_LFunction_logDeriv_sub_local_zero_poles_le hq hχ t s hs hne).trans
  have h := dirichletZeroDisk_log_bound_le q hq t
  have hL := primitiveZeroFreeHeightLog_pos hq t
  linarith

end Chen
