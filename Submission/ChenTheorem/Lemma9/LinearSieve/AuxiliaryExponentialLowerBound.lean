import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryLowerBound

set_option autoImplicit true
namespace Chen.LinearSieve

theorem auxiliaryError_exponential_lower_bound (s ε : ℝ) (hs : 3 ≤ s)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    auxiliaryLowerConstant * Real.exp (-(s / (1 - ε) + 1) * Real.log (s / ε)) ≤
        upperAuxiliaryError s ∧
      auxiliaryLowerConstant * Real.exp (-(s / (1 - ε) + 1) * Real.log (s / ε)) ≤
        lowerAuxiliaryError s := by
  have hs0 : 0 < s := by linarith
  have hh : 0 < 1 - ε := by linarith
  have hq : 0 < ε / s := div_pos hε0 hs0
  have hq1 : ε / s ≤ 1 := (div_le_one hs0).2 (by linarith)
  have hn := (Nat.ceil_lt_add_one (div_nonneg hs0.le hh.le)).le
  have hp := Real.rpow_le_rpow_of_exponent_ge hq hq1 hn
  rw [Real.rpow_natCast, Real.rpow_def_of_pos hq] at hp
  have hl : Real.log (ε / s) = -Real.log (s / ε) := by
    rw [Real.log_div hε0.ne' hs0.ne', Real.log_div hs0.ne' hε0.ne']
    ring
  rw [hl] at hp
  have he : -Real.log (s / ε) * (s / (1 - ε) + 1) =
      -(s / (1 - ε) + 1) * Real.log (s / ε) := by ring
  rw [he] at hp
  have hm := mul_le_mul_of_nonneg_left hp auxiliaryLowerConstant_pos.le
  have hb := auxiliaryError_lower_bound s ε hs hε0 hε1
  exact ⟨hm.trans hb.1, hm.trans hb.2⟩

/-- Choosing the short interval length `1 / log s` gives the lower
bound of size `exp (-s log s - s log log s - O(s))` needed for the
large-parameter part of the quantitative sieve induction. -/
theorem auxiliaryError_logarithmic_lower_bound (s : ℝ) (hs : 3 ≤ s)
    (hlog : 2 ≤ Real.log s) :
    auxiliaryLowerConstant * Real.exp
        (-s * Real.log s - s * Real.log (Real.log s) - 6 * s) ≤ upperAuxiliaryError s ∧
      auxiliaryLowerConstant * Real.exp
        (-s * Real.log s - s * Real.log (Real.log s) - 6 * s) ≤ lowerAuxiliaryError s := by
  have hs0 : 0 < s := by linarith
  have hl0 : 0 < Real.log s := by linarith
  have hl1 : 0 < Real.log s - 1 := by linarith
  have hε0 : 0 < 1 / Real.log s := one_div_pos.mpr hl0
  have hε1 : 1 / Real.log s < 1 := (div_lt_one hl0).2 (by linarith)
  have hb := auxiliaryError_exponential_lower_bound s (1 / Real.log s) hs hε0 hε1
  have hloglog := Real.log_le_sub_one_of_pos hl0
  have hlogs := Real.log_le_sub_one_of_pos hs0
  have hsum : Real.log s + Real.log (Real.log s) ≤ 2 * Real.log s := by linarith
  have hterm : (s / (Real.log s - 1)) * (Real.log s + Real.log (Real.log s)) ≤
      4 * s := by
    calc
      _ ≤ (s / (Real.log s - 1)) * (2 * Real.log s) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hs0.le hl1.le)
      _ ≤ 4 * s := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hl1]
        nlinarith
  have hfactor : s / (1 - 1 / Real.log s) + 1 = s + s / (Real.log s - 1) + 1 := by
    have hd : 1 - 1 / Real.log s ≠ 0 := by linarith
    field_simp
    ring
  have hratio : s / (1 / Real.log s) = s * Real.log s := by field_simp
  rw [hratio, Real.log_mul hs0.ne' hl0.ne', hfactor] at hb
  have hexp : -s * Real.log s - s * Real.log (Real.log s) - 6 * s ≤
      -(s + s / (Real.log s - 1) + 1) * (Real.log s + Real.log (Real.log s)) := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    auxiliaryLowerConstant_pos.le
  exact ⟨hm.trans hb.1, hm.trans hb.2⟩

end Chen.LinearSieve
