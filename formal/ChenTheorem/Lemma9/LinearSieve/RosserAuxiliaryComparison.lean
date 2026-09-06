import ChenTheorem.Lemma9.LinearSieve.RosserParameterExponential
import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryLowerBound

namespace Chen.LinearSieve

/-- The exact remaining exponent after comparing the actual factorial
tail with the lower bound for the full auxiliary error. -/
noncomputable def auxiliaryComparisonExponent (B d δ D s : ℝ) : ℝ :=
  2 * Real.log B + 2 * Real.log s + δ * Real.log (Real.log D) - Real.log auxiliaryLowerConstant +
    s * (8 + Real.log (1 + Real.log B) + Real.log (Real.log s) +
      Real.log (Real.log D) - d * Real.log s)

theorem parameter_exponential_le_inflated_auxiliary (B d δ D s : ℝ)
    (hD : 1 < D) (hs : 3 ≤ s) (hlog : 2 ≤ Real.log s) :
    Real.exp (2 * Real.log B + 3 * Real.log s +
        s * (2 + Real.log (1 + Real.log B) - Real.log s)) ≤
      Real.exp (auxiliaryComparisonExponent B d δ D s) *
        inflatedAuxiliaryError d δ D s upperAuxiliaryError ∧
      Real.exp (2 * Real.log B + 3 * Real.log s +
        s * (2 + Real.log (1 + Real.log B) - Real.log s)) ≤
      Real.exp (auxiliaryComparisonExponent B d δ D s) *
        inflatedAuxiliaryError d δ D s lowerAuxiliaryError := by
  have hs0 : 0 < s := by linarith
  have hL := Real.log_pos hD
  have h := inflatedAuxiliaryError_logarithmic_lower_bound d δ D s hD hs hlog
  have he : Real.exp (auxiliaryComparisonExponent B d δ D s) *
      (auxiliaryLowerConstant * s * (Real.log D) ^ (-δ) *
        Real.exp (s * ((d - 1) * Real.log s - Real.log (Real.log s) -
          Real.log (Real.log D) - 6))) =
      Real.exp (2 * Real.log B + 3 * Real.log s +
        s * (2 + Real.log (1 + Real.log B) - Real.log s)) := by
    calc
      _ = Real.exp (auxiliaryComparisonExponent B d δ D s) *
          (Real.exp (Real.log auxiliaryLowerConstant) * Real.exp (Real.log s) *
            Real.exp (Real.log (Real.log D) * (-δ)) *
              Real.exp (s * ((d - 1) * Real.log s - Real.log (Real.log s) -
                Real.log (Real.log D) - 6))) := by
        rw [Real.exp_log auxiliaryLowerConstant_pos, Real.exp_log hs0,
          Real.rpow_def_of_pos hL]
      _ = Real.exp (auxiliaryComparisonExponent B d δ D s + Real.log auxiliaryLowerConstant +
          Real.log s + Real.log (Real.log D) * (-δ) +
          s * ((d - 1) * Real.log s - Real.log (Real.log s) - Real.log (Real.log D) - 6)) := by
        simp only [Real.exp_add]
        ring
      _ = _ := by
        congr 1
        unfold auxiliaryComparisonExponent
        ring
  have hu := mul_le_mul_of_nonneg_left h.1 (Real.exp_pos (auxiliaryComparisonExponent B d δ D s)).le
  have hl := mul_le_mul_of_nonneg_left h.2 (Real.exp_pos (auxiliaryComparisonExponent B d δ D s)).le
  rw [he] at hu hl
  exact ⟨hu, hl⟩

/-- An actual large-parameter comparison, uniform in the prime set and
both sieve signs. Its explicitly displayed exponent is the remaining
elementary estimate needed when selecting the growing split parameter. -/
theorem rosserRelativeDefect_le_inflated_auxiliary :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ upper : Bool, ∀ d δ D : ℝ,
      1 < D → 6 ≤ sieveParameter D (z + 1) → 2 ≤ Real.log (sieveParameter D (z + 1)) →
      rosserRelativeDefect P (z + 1) upper D ≤
        Real.exp (auxiliaryComparisonExponent (depthMassMajorant K z) d δ D
          (sieveParameter D (z + 1))) * inflatedAuxiliaryError d δ D
            (sieveParameter D (z + 1)) upperAuxiliaryError ∧
      rosserRelativeDefect P (z + 1) upper D ≤
        Real.exp (auxiliaryComparisonExponent (depthMassMajorant K z) d δ D
          (sieveParameter D (z + 1))) * inflatedAuxiliaryError d δ D
            (sieveParameter D (z + 1)) lowerAuxiliaryError := by
  obtain ⟨K, hK, hb⟩ := rosserRelativeDefect_parameter_exponential
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd upper d δ D hD hs hlog
  have h := hb z hz P hP hodd upper D hD hs
  have hc := parameter_exponential_le_inflated_auxiliary (depthMassMajorant K z) d δ D
    (sieveParameter D (z + 1)) hD (by linarith) hlog
  exact ⟨h.trans hc.1, h.trans hc.2⟩

end Chen.LinearSieve
