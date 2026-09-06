import ChenTheorem.Lemma9.LinearSieve.InitialConstantCalibration
import ChenTheorem.Lemma9.LinearSieve.RosserAsymptoticError

open Filter

namespace Chen.LinearSieve

/-- The actual upper Rosser polynomial has the classical numerical main term
uniformly on compact subintervals of the initial upper range. -/
theorem eventually_rosser_upper_polynomial_calibrated (a b ε : ℝ) (ha : 1 < a)
    (hab : a ≤ b) (hb : b ≤ 3) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → a ≤ sieveParameter D (z + 1) →
      sieveParameter D (z + 1) ≤ b → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserEval P primeDensity (z + 1) true D ≤
        sieveProduct P primeDensity (z + 1) *
          (2 * Real.exp Real.eulerMascheroniConstant / sieveParameter D (z + 1) + ε) := by
  filter_upwards [eventually_rosser_upper_polynomial_compact a b ε ha hab hε] with D hD
  intro z hz has hsb P hP hodd
  have h := hD z hz has hsb P hP hodd
  rwa [upperLinearSieveFunction_initial_calibrated _ (ha.trans_le has) (hsb.trans hb)] at h

/-- The analogous calibrated lower bound on the initial lower range. -/
theorem eventually_rosser_lower_polynomial_calibrated (a b ε : ℝ) (ha : 2 < a)
    (hab : a ≤ b) (hb : b ≤ 4) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → a ≤ sieveParameter D (z + 1) →
      sieveParameter D (z + 1) ≤ b → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      sieveProduct P primeDensity (z + 1) *
        (2 * Real.exp Real.eulerMascheroniConstant * Real.log (sieveParameter D (z + 1) - 1) /
          sieveParameter D (z + 1) - ε) ≤ rosserEval P primeDensity (z + 1) false D := by
  filter_upwards [eventually_rosser_lower_polynomial_compact a b ε ha hab hε] with D hD
  intro z hz has hsb P hP hodd
  have h := hD z hz has hsb P hP hodd
  rwa [lowerLinearSieveFunction_initial_calibrated _ (ha.le.trans has) (hsb.trans hb)] at h

end Chen.LinearSieve
