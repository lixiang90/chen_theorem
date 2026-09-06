import ChenTheorem.Lemma9.LinearSieve.PrimeAbelAbsolute
import ChenTheorem.Lemma9.LinearSieve.LogPowerSubstitution

open Set Filter MeasureTheory
open scoped Classical Topology

namespace Chen.LinearSieve

noncomputable def upperSievePrimeSum (a X : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊X ^ (1 / 10 : ℝ)⌋₊ ⌊X ^ (1 / 3 : ℝ)⌋₊ with p.Prime,
    upperSievePrimeWeight a X p * (p : ℝ)⁻¹

/-- The prime-reciprocal sieve sum approaches its continuous profile uniformly
over all level exponents above `29/60`. -/
theorem eventually_upperSievePrimeSum_error_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, 29 / 60 < a →
      |upperSievePrimeSum a X -
        ∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α| < ε := by
  filter_upwards [eventually_uniform_error_above_rpow (c := (1 / 10 : ℝ))
    (by norm_num) (show 0 < ε / 20 by positivity), eventually_gt_atTop (1 : ℝ)] with X hE hX
  intro a ha
  have hX0 : 0 < X := by linarith
  have hleft : 1 < X ^ (1 / 10 : ℝ) := Real.one_lt_rpow hX (by norm_num)
  have hab : X ^ (1 / 10 : ℝ) ≤ X ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hf : ∀ t ∈ Icc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ)),
      DifferentiableAt ℝ (upperSievePrimeWeight a X) t := by
    intro t ht
    exact (hasDerivAt_upperSievePrimeWeight a X t
      ((Real.rpow_pos_of_pos hX0 _).trans_le ht.1)
      (by linarith [upperSievePrimeWeight_argument a X t ha hX ht])).differentiableAt
  have hfa := upperSievePrimeWeight_bounds a X (X ^ (1 / 10 : ℝ)) ha hX ⟨le_rfl, hab⟩
  have hfb := upperSievePrimeWeight_bounds a X (X ^ (1 / 3 : ℝ)) ha hX ⟨hab, le_rfl⟩
  have herr := abs_primeReciprocal_abel_error_le hleft hab
    (show 0 ≤ ε / 20 by positivity) (upperSievePrimeWeight a X) hf
    (continuousOn_deriv_upperSievePrimeWeight a X ha hX).integrableOn_Icc
    (fun t ht => hE t ht.1) hfa.1 hfb.1
    (fun t ht => deriv_upperSievePrimeWeight_nonneg a X t ha hX (Ioc_subset_Icc_self ht))
  rw [integral_upperSievePrimeWeight a X hX] at herr
  have hb := mul_le_mul_of_nonneg_left hfb.2 (show 0 ≤ 2 * (ε / 20) by positivity)
  unfold upperSievePrimeSum
  linarith

theorem tendsto_upperSievePrimeSum (a : ℝ) (ha : 29 / 60 < a) :
    Tendsto (upperSievePrimeSum a) atTop
      (𝓝 (∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_upperSievePrimeSum_error_lt ε hε] with X hX
  simpa only [Real.dist_eq] using hX a ha

end Chen.LinearSieve
