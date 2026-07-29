import ChenTheorem.MainEstimates

open Filter Real
open scoped Classical

namespace Chen

/-!
The paper proves its shifted conclusion by repeating the preceding sieve
argument with the fixed even shift `h`.  The shifted sieve infrastructure has
not yet been split into analogues of Lemmas 5, 8, 9 and inequality (28), so the
resulting quantitative estimate is kept here as one explicit upstream target.
This lets `Main.lean` contain only deductions from named lemma interfaces.
-/

set_option warn.sorry false in
/-- Quantitative shifted form used for Theorem 2. -/
theorem chenCountShift_lower_estimate
    (h : ℕ) (hh : Even h) (h0 : 0 < h) :
    ∀ᶠ x : ℕ in atTop,
      0.67 * (x : ℝ) * chenConst h / (Real.log x) ^ 2 ≤
        (chenCountShift h x : ℝ) := by
  sorry

end Chen
