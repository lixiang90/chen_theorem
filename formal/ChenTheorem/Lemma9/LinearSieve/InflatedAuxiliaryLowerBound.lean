import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryError
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryExponentialLowerBound

namespace Chen.LinearSieve

theorem auxiliaryInflation_exponential_lower (d D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    Real.exp (s * (d * Real.log s - Real.log (Real.log D))) ≤ auxiliaryInflation d D s := by
  have hq : 0 < s ^ d / Real.log D :=
    div_pos (Real.rpow_pos_of_pos hs d) (Real.log_pos hD)
  have hm := Real.rpow_le_rpow hq.le (show s ^ d / Real.log D ≤ 1 + s ^ d / Real.log D
    by linarith) hs.le
  rw [Real.rpow_def_of_pos hq, Real.log_div
    (Real.rpow_pos_of_pos hs d).ne' (Real.log_pos hD).ne', Real.log_rpow hs] at hm
  simpa only [auxiliaryInflation, mul_comm] using hm

/-- A common explicit lower bound for the full error scale. The positive
contribution `(d - 1) log s` is supplied by the extra factor and can
compensate for the auxiliary function's decay at large sieve parameters. -/
theorem inflatedAuxiliaryError_logarithmic_lower_bound (d δ D s : ℝ)
    (hD : 1 < D) (hs : 3 ≤ s) (hlog : 2 ≤ Real.log s) :
    auxiliaryLowerConstant * s * (Real.log D) ^ (-δ) *
        Real.exp (s * ((d - 1) * Real.log s - Real.log (Real.log s) -
          Real.log (Real.log D) - 6)) ≤ inflatedAuxiliaryError d δ D s upperAuxiliaryError ∧
      auxiliaryLowerConstant * s * (Real.log D) ^ (-δ) *
        Real.exp (s * ((d - 1) * Real.log s - Real.log (Real.log s) -
          Real.log (Real.log D) - 6)) ≤ inflatedAuxiliaryError d δ D s lowerAuxiliaryError := by
  have hs0 : 0 < s := by linarith
  have hI := auxiliaryInflation_exponential_lower d D s hD hs0
  have hH := auxiliaryError_logarithmic_lower_bound s hs hlog
  have hcoef : 0 ≤ (Real.log D) ^ (-δ) * s :=
    mul_nonneg (Real.rpow_nonneg (Real.log_pos hD).le (-δ)) hs0.le
  have hstep : ∀ H : ℝ → ℝ,
      auxiliaryLowerConstant * Real.exp
        (-s * Real.log s - s * Real.log (Real.log s) - 6 * s) ≤ H s →
      auxiliaryLowerConstant * s * (Real.log D) ^ (-δ) *
        Real.exp (s * ((d - 1) * Real.log s - Real.log (Real.log s) -
          Real.log (Real.log D) - 6)) ≤ inflatedAuxiliaryError d δ D s H := by
    intro H hH
    have hm := _root_.mul_le_mul hI hH
      (mul_nonneg auxiliaryLowerConstant_pos.le (Real.exp_pos _).le)
      (auxiliaryInflation_pos d D s hD hs0.le).le
    have hc := mul_le_mul_of_nonneg_left hm hcoef
    have heq : s * (d * Real.log s - Real.log (Real.log D)) +
        (-s * Real.log s - s * Real.log (Real.log s) - 6 * s) =
        s * ((d - 1) * Real.log s - Real.log (Real.log s) - Real.log (Real.log D) - 6) := by
      ring
    have he : (Real.log D) ^ (-δ) * s *
        (Real.exp (s * (d * Real.log s - Real.log (Real.log D))) *
          (auxiliaryLowerConstant * Real.exp
            (-s * Real.log s - s * Real.log (Real.log s) - 6 * s))) =
        auxiliaryLowerConstant * s * (Real.log D) ^ (-δ) *
          Real.exp (s * ((d - 1) * Real.log s - Real.log (Real.log s) -
            Real.log (Real.log D) - 6)) := by
      rw [← heq, Real.exp_add]
      ring
    rw [he] at hc
    calc
      _ ≤ (Real.log D) ^ (-δ) * s * (auxiliaryInflation d D s * H s) := hc
      _ = _ := by unfold inflatedAuxiliaryError auxiliaryErrorScale; ring
  exact ⟨hstep upperAuxiliaryError hH.1, hstep lowerAuxiliaryError hH.2⟩

end Chen.LinearSieve
