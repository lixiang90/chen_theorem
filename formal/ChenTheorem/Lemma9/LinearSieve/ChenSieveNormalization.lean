import ChenTheorem.Lemma9.LinearSieve.PowerSieveCutoff

open Filter Finset
open scoped Classical

namespace Chen.LinearSieve

theorem chenSmallPrimes_eq_oddPrimesLE (x : ℕ) (hx : 1 ≤ x) :
    chenSmallPrimes x = oddPrimesLE (powerSieveCutoff ((1 : ℝ) / 10) x) := by
  ext p
  simp only [mem_chenSmallPrimes hx, oddPrimesLE, mem_filter, Nat.mem_primesLE, powerSieveCutoff]
  rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg x) _)]
  tauto

/-- The local product of the actual small-prime set in the constructed
Chen sieve is the product normalized in the analytic development. -/
theorem chen_sieveProduct_eq (x : ℕ) (hx : 1 ≤ x) :
    sieveProduct (chenReducedSmallPrimes x) primeDensity
      (powerSieveCutoff ((1 : ℝ) / 10) x + 1) =
      primeSieveProduct x (powerSieveCutoff ((1 : ℝ) / 10) x) := by
  have hz : ∀ p ∈ chenReducedSmallPrimes x, p < powerSieveCutoff ((1 : ℝ) / 10) x + 1 := by
    intro p hp
    have hpS := (mem_filter.mp hp).1
    rw [chenSmallPrimes_eq_oddPrimesLE x hx] at hpS
    have := (Nat.mem_primesLE.mp (mem_filter.mp hpS).1).1
    omega
  rw [sieveProduct_eq_prod _ _ _ hz]
  unfold chenReducedSmallPrimes primeSieveProduct
  rw [chenSmallPrimes_eq_oddPrimesLE x hx]

/-- Equation (25) in the relative-error form needed for Chen's eventual
lower bound. The residue parameter `x` varies with the cutoff, so the
large-prime-divisor tail has been controlled uniformly. -/
theorem chen_sieve_product_normalization :
    Tendsto (fun x : ℕ =>
      sieveProduct (chenReducedSmallPrimes x) primeDensity
        (powerSieveCutoff ((1 : ℝ) / 10) x + 1) * Real.log x / chenConst x)
      atTop (nhds (20 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := primeSieveProduct_power_normalized_tendsto ((1 : ℝ) / 10) (by norm_num)
  have heq : 2 * Real.exp (-Real.eulerMascheroniConstant) / ((1 : ℝ) / 10) =
      20 * Real.exp (-Real.eulerMascheroniConstant) := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  rw [chen_sieveProduct_eq x hx]
  ring

/-- Arbitrarily accurate normalization of the actual finite sieve
product, with no extra mathematical input beyond its proved limit. -/
theorem eventually_abs_chen_sieve_product_error_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      |sieveProduct (chenReducedSmallPrimes x) primeDensity
          (powerSieveCutoff ((1 : ℝ) / 10) x + 1) * Real.log x / chenConst x -
        20 * Real.exp (-Real.eulerMascheroniConstant)| < ε := by
  have h := chen_sieve_product_normalization.eventually
    (Metric.ball_mem_nhds _ hε)
  simpa only [Metric.mem_ball, Real.dist_eq] using h

end Chen.LinearSieve
