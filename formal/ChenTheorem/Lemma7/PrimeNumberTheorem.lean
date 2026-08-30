import ChenTheorem.Lemma7.Normalization
import PrimeNumberTheoremAnd.Consequences

open Filter Real
open scoped Classical

namespace Chen

/-!
# Lemma 7: prime-number-theorem input

The final sentence of the paper's proof of Lemma 7 replaces the smoothed
von Mangoldt sum by its main term.  This is a uniform form of the prime
number theorem: the quotient `x / (p₁ p₂)` is at least `x^(1/3)` throughout
`chenPairs x`, so the ordinary `o(y)` remainder is uniform over all pairs.

Mathlib 4.32.2 does not yet contain the prime number theorem.  We import
`WeakPNT''` from `PrimeNumberTheoremAnd`, which states `ψ(y) ∼ y`, and derive
the required uniform estimate here.  The uniformity is not an additional
analytic input: it follows from the lower bound
`x^(1/3) < x/(p₁p₂)` throughout `chenPairs x`.
-/

/-- A one-sided eventual form of the prime number theorem for Chebyshev's
first function. -/
theorem eventually_chebyshevPsi_le_mul (η : ℝ) (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, Chebyshev.psi y ≤ (1 + η) * y := by
  have hyne : ∀ᶠ y : ℝ in atTop, (fun y : ℝ => y) y ≠ 0 :=
    (eventually_gt_atTop 0).mono fun _ hy => hy.ne'
  have hratio :
      Tendsto (fun y : ℝ => Chebyshev.psi y / y) atTop (nhds 1) := by
    change Tendsto (Chebyshev.psi / fun y : ℝ => y) atTop (nhds 1)
    exact (Asymptotics.isEquivalent_iff_tendsto_one hyne).mp WeakPNT''
  have hup : ∀ᶠ y : ℝ in atTop, Chebyshev.psi y / y < 1 + η :=
    (tendsto_order.mp hratio).2 (1 + η) (by linarith)
  filter_upwards [hup, eventually_gt_atTop 0] with y hy hy0
  exact ((div_lt_iff₀ hy0).mp hy).le

/-- On an admissible pair, the auxiliary `range (x + 1)` cutoff in
`smoothedMIndices` is redundant. -/
theorem smoothedMIndices_eq_Icc {x : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) :
    smoothedMIndices x q =
      Finset.Icc 0 ⌊(x : ℝ) / ((q.1 : ℝ) * q.2)⌋₊ := by
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  have hY1 : 1 < Y := one_lt_pairQuotient hq
  have hY0 : 0 ≤ Y := le_trans (by norm_num) hY1.le
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with ⟨hp₁, hp₂, _hp₁lo, _hp₁hi, _hp₂lo, _hp₂hi⟩
  have hprod1 : (1 : ℝ) ≤ (q.1 : ℝ) * q.2 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hp₁.ne_zero hp₂.ne_zero)
  have hYx : Y ≤ (x : ℝ) := div_le_self (Nat.cast_nonneg x) hprod1
  ext n
  simp only [smoothedMIndices, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Icc]
  constructor
  · rintro ⟨_hnx, hnY⟩
    exact ⟨Nat.zero_le n, (Nat.le_floor_iff hY0).2 hnY⟩
  · rintro ⟨_hn0, hnY⟩
    have hnYR : (n : ℝ) ≤ Y := (Nat.le_floor_iff hY0).1 hnY
    have hnx : n ≤ x := by exact_mod_cast hnYR.trans hYx
    exact ⟨Nat.lt_succ_iff.mpr hnx, hnYR⟩

/-- Uniform smoothed prime number theorem on the range of Chen prime pairs.

This is the formal analytic content of the phrase "by Lemma 1" in the last
line of the proof of Lemma 7, together with the classical prime number
theorem for `∑_{n ≤ y} Λ(n)`. -/
theorem eventually_smoothed_pair_mass_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop,
      ∀ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n ≤
          (1 + η) * (x : ℝ) *
            ((q.1 : ℝ) * (q.2 : ℝ) *
              Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
  rcases Filter.eventually_atTop.1
      (eventually_chebyshevPsi_le_mul η hη) with ⟨A, hA⟩
  have hroot : ∀ᶠ x : ℕ in atTop,
      A ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop A)
  filter_upwards [hroot, eventually_gt_atTop 1] with x hxroot hx1
  intro q hq
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  have hY1 : 1 < Y := one_lt_pairQuotient hq
  have hlog : 0 < Real.log Y := Real.log_pos hY1
  have hinv : 0 ≤ (Real.log Y)⁻¹ := inv_nonneg.mpr hlog.le
  have hpsi : Chebyshev.psi Y ≤ (1 + η) * Y :=
    hA Y (hxroot.trans (rpow_third_lt_pairQuotient hq).le)
  calc
    ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n ≤
        (Real.log Y)⁻¹ * Chebyshev.psi Y := by
      rw [smoothedMIndices_eq_Icc hq, Chebyshev.psi_eq_sum_Icc,
        Finset.mul_sum]
      exact Finset.sum_le_sum fun n _hn => by
        have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
          ArithmeticFunction.vonMangoldt_nonneg
        have hy : 0 ≤
            (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
        have hΦ :
            chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) ≤ 1 :=
          chenPhi_le_one x (by exact_mod_cast hx1) hy
        change (Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt n *
            chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) ≤
          (Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt n
        calc
          (Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt n *
              chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) ≤
            ((Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt n) * 1 :=
              mul_le_mul_of_nonneg_left hΦ (mul_nonneg hinv hΛ)
          _ = (Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt n := by ring
    _ ≤ (Real.log Y)⁻¹ * ((1 + η) * Y) :=
      mul_le_mul_of_nonneg_left hpsi hinv
    _ = (1 + η) * (x : ℝ) *
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
      have hprod : (q.1 : ℝ) * (q.2 : ℝ) ≠ 0 := by
        intro hzero
        have : Y = 0 := by simp [Y, hzero]
        linarith
      dsimp only [Y] at hlog ⊢
      field_simp [hprod, hlog.ne']

/-- The smoothed prime mass is nonnegative. -/
theorem smoothedPrimeMass_nonneg {x : ℕ} (hx : 1 < x) :
    0 ≤ smoothedPrimeMass x := by
  unfold smoothedPrimeMass
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro n hn
  exact smoothedMKernel_nonneg hx hq

/-- Summing the uniform smoothed PNT over the admissible prime pairs. -/
theorem eventually_smoothedPrimeMass_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop,
      smoothedPrimeMass x ≤
        (1 + η) * (x : ℝ) *
          ∑ q ∈ chenPairs x,
            ((q.1 : ℝ) * (q.2 : ℝ) *
              Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
  filter_upwards [eventually_smoothed_pair_mass_le η hη] with x hx
  rw [smoothedPrimeMass]
  calc
    ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n ≤
      ∑ q ∈ chenPairs x,
        (1 + η) * (x : ℝ) *
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
      exact Finset.sum_le_sum fun q hq => hx q hq
    _ = (1 + η) * (x : ℝ) *
        ∑ q ∈ chenPairs x,
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
      rw [Finset.mul_sum]

end Chen
