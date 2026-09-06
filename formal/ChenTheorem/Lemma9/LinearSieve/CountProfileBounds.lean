import ChenTheorem.Lemma9.LinearSieve.NormalizedRosserProfile
import ChenTheorem.Lemma9.LinearSieve.ShiftedCountAsymptoticSieve

open Filter Finset
open scoped Classical

namespace Chen.LinearSieve

theorem eventually_chen_count_profile_lower (hBV : BombieriVinogradov.Statement)
    (a K : ℝ) (ha : 29 / 60 < a) (ha' : a < 1 / 2)
    (hK : K < chenContinuousSieveProfile a) :
    ∀ᶠ x : ℕ in atTop, ¬x.Prime →
      K * ((x : ℝ) * chenConst x / Real.log x ^ 2) ≤
        (sievedPrimeCount x : ℝ) - (1 / 2) *
          ∑ p ∈ midPrimes x, (sievedPrimeCountAt x p : ℝ) := by
  let L := (K + chenContinuousSieveProfile a) / 2
  have hKL : K < L := by dsimp [L]; linarith
  have hL : L < chenContinuousSieveProfile a := by dsimp [L]; linarith
  have hmain := eventually_powerRosserMainTerm_lower chenReducedSmallPrimes chenReducedMidPrimes chenConst
    (fun x _ p hp => chenSmallPrimes_prime x p (mem_filter.mp hp).1)
    (fun x hx p hp => ((mem_chenSmallPrimes (by omega : 1 ≤ x)).mp (mem_filter.mp hp).1).2.1)
    (fun _ _ hp => (mem_filter.mp hp).1)
    (fun x => twinConst_pos.trans_le (twinConst_le_chenConst x))
    chen_sieve_product_normalization a L ha ha' hL
  filter_upwards [hmain, eventually_chen_count_lower_at_power_level hBV a
    (by linarith) ha' (L - K) (sub_pos.mpr hKL)] with x hm hc
  intro hxnp
  have hc' := hc hxnp
  change powerRosserMainTerm a (chenReducedSmallPrimes x) (chenReducedMidPrimes x) x -
    (L - K) * ((x : ℝ) * chenConst x / Real.log x ^ 2) ≤ _ at hc'
  nlinarith

theorem eventually_shifted_chen_count_profile_lower (hBV : BombieriVinogradov.Statement)
    (h : ℕ) (hh : h ≠ 0) (a K : ℝ) (ha : 29 / 60 < a) (ha' : a < 1 / 2)
    (hK : K < chenContinuousSieveProfile a) :
    ∀ᶠ x : ℕ in atTop,
      K * ((x : ℝ) * chenConst h / Real.log x ^ 2) ≤
        (shiftedSievedPrimeCount h x : ℝ) - (1 / 2) *
          ∑ p ∈ midPrimes x, (shiftedSievedPrimeCountAt h x p : ℝ) := by
  let L := (K + chenContinuousSieveProfile a) / 2
  have hKL : K < L := by dsimp [L]; linarith
  have hL : L < chenContinuousSieveProfile a := by dsimp [L]; linarith
  have hmain := eventually_powerRosserMainTerm_lower (chenShiftedSmallPrimes h)
    (chenShiftedMidPrimes h) (fun _ => chenConst h)
    (fun x _ p hp => chenSmallPrimes_prime x p (mem_filter.mp hp).1)
    (fun x hx p hp => ((mem_chenSmallPrimes (by omega : 1 ≤ x)).mp (mem_filter.mp hp).1).2.1)
    (fun _ _ hp => (mem_filter.mp hp).1)
    (fun _ => twinConst_pos.trans_le (twinConst_le_chenConst h))
    (chen_shifted_sieve_product_normalization h hh) a L ha ha' hL
  filter_upwards [hmain, eventually_shifted_chen_count_lower_at_power_level hBV h hh a
    (by linarith) ha' (L - K) (sub_pos.mpr hKL)] with x hm hc
  change powerRosserMainTerm a (chenShiftedSmallPrimes h x) (chenShiftedMidPrimes h x) x -
    (L - K) * ((x : ℝ) * chenConst h / Real.log x ^ 2) ≤ _ at hc
  nlinarith

end Chen.LinearSieve
