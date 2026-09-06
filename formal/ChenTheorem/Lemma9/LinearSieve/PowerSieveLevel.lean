import ChenTheorem.Lemma9.LinearSieve.CountAsymptoticSieve

open Filter Finset
open scoped Classical

namespace Chen.LinearSieve

/-- Every fixed power level strictly below the square root is eventually
admissible for any logarithmic saving demanded by BV. -/
theorem eventually_powerSieveCutoff_le_bv_level (a : ℝ) (ha : a < 1 / 2) (B : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      (powerSieveCutoff a x : ℝ) ≤ Real.sqrt x / Real.log x ^ B := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop B (show 0 < 1 / 2 - a by linarith)).def
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall,
    eventually_ge_atTop (2 : ℕ)] with x hx hx2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlog : Real.log x ^ B ≤ (x : ℝ) ^ (1 / 2 - a) := by
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg hlpos.le B),
      abs_of_nonneg (Real.rpow_nonneg hxpos.le (1 / 2 - a))] using hx
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlpos B)).mpr
  calc
    _ ≤ (x : ℝ) ^ a * Real.log x ^ B := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlpos.le B)
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le a)
    _ ≤ (x : ℝ) ^ a * (x : ℝ) ^ (1 / 2 - a) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hxpos.le a)
    _ = Real.sqrt x := by
      rw [← Real.rpow_add hxpos, Real.sqrt_eq_rpow]
      congr 1
      ring

/-- The same level remains nontrivial after fixing any of Chen's middle
primes, uniformly up to the endpoint `x^(1/3)`. -/
theorem eventually_powerSieveCutoff_div_midPrime (a : ℝ) (ha : 1 / 3 < a) :
    ∀ᶠ x : ℕ in atTop, ∀ k ∈ midPrimes x, 1 < powerSieveCutoff a x / k := by
  have ha0 : 0 < a := by linarith
  have hratio := (powerSieveCutoff_div_rpow_tendsto a ha0).eventually
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hpow := ((tendsto_rpow_atTop (show 0 < a - 1 / 3 by linarith)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hratio, hpow, eventually_ge_atTop (2 : ℕ)] with x hratio hpow hx
  intro k hk
  obtain ⟨hkprime, _, hkbound⟩ := (mem_filter.mp hk).2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hhalf : (1 / 2) * (x : ℝ) ^ a ≤ (powerSieveCutoff a x : ℝ) :=
    le_of_lt ((lt_div_iff₀ (Real.rpow_pos_of_pos hxpos a)).mp hratio)
  have hp : 4 ≤ (x : ℝ) ^ (a - 1 / 3) := hpow
  have heq : (x : ℝ) ^ a = (x : ℝ) ^ (a - 1 / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hlower : 2 * (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (powerSieveCutoff a x : ℝ) := by
    calc
      _ ≤ (1 / 2) * ((x : ℝ) ^ (a - 1 / 3) * (x : ℝ) ^ ((1 : ℝ) / 3)) := by
        nlinarith [Real.rpow_nonneg hxpos.le ((1 : ℝ) / 3)]
      _ ≤ _ := by rw [← heq]; exact hhalf
  have hkn : 2 * k ≤ powerSieveCutoff a x := by
    exact_mod_cast (mul_le_mul_of_nonneg_left hkbound (by norm_num : (0 : ℝ) ≤ 2)).trans hlower
  have hdiv : 2 ≤ powerSieveCutoff a x / k := (Nat.le_div_iff_mul_le hkprime.pos).mpr hkn
  omega

/-- After choosing the explicit level `floor(x^a)`, every auxiliary
level and every loss in the original count inequality has been supplied.
Sharp estimates of the displayed Rosser polynomials remain necessary. -/
theorem eventually_chen_count_lower_at_power_level
    (hBV : BombieriVinogradov.Statement) (a : ℝ) (ha : 1 / 3 < a) (ha' : a < 1 / 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, ¬x.Prime →
      (x : ℝ) * rosserEval (chenReducedSmallPrimes x) primeDensity
          (powerSieveCutoff ((1 : ℝ) / 10) x + 1) false (powerSieveCutoff a x) / Real.log x -
        (1 / 2) * ((∑ k ∈ chenReducedMidPrimes x,
          ((x : ℝ) / Nat.totient k) * rosserEval (chenReducedSmallPrimes x) primeDensity
            (powerSieveCutoff ((1 : ℝ) / 10) x + 1) true (powerSieveCutoff a x / k : ℕ)) /
              Real.log (countCutoff x)) -
        δ * ((x : ℝ) * chenConst x / Real.log x ^ 2) ≤
      (sievedPrimeCount x : ℝ) -
        (1 / 2) * ∑ k ∈ midPrimes x, (sievedPrimeCountAt x k : ℝ) := by
  obtain ⟨B, hB, hcount⟩ := eventually_chen_count_lower_of_rosser_polynomials hBV δ hδ
  filter_upwards [hcount, eventually_powerSieveCutoff_le_bv_level a ha' B,
    eventually_powerSieveCutoff_div_midPrime a ha,
    (powerSieveCutoff_tendsto a (by linarith)).eventually (eventually_ge_atTop 2)]
    with x hcount hQ hmid hlevel
  intro hxnp
  apply hcount hxnp (powerSieveCutoff a x) hQ (powerSieveCutoff a x)
    (by exact_mod_cast (show 1 < powerSieveCutoff a x by omega)) le_rfl
    (fun k => (powerSieveCutoff a x / k : ℕ))
  · intro k hk
    exact_mod_cast hmid k (mem_filter.mp hk).1
  · exact fun _ _ => le_rfl

end Chen.LinearSieve
