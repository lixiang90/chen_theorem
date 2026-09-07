import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedChenPrimeCounts
import Submission.ChenTheorem.Lemma9.LinearSieve.ChenSieveNormalization

set_option autoImplicit true
open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

theorem largeDivisorTail_eq_one_of_le (h y : ℕ) (hy : h ≤ y) :
    largeDivisorTail h y = 1 := by
  apply prod_eq_one
  intro p hp
  obtain ⟨hpf, _, hyp⟩ := mem_filter.mp hp
  obtain ⟨_, hpd, hh⟩ := Nat.mem_primeFactors.mp hpf
  have hph := Nat.le_of_dvd (Nat.pos_of_ne_zero hh) hpd
  omega

/-- For a fixed nonzero shift the divisor tail eventually vanishes
exactly, giving the singular series `C_h` instead of the varying `C_x`. -/
theorem primeSieveProduct_fixed_log_normalized_tendsto (h : ℕ) (hh : h ≠ 0)
    (y : ℕ → ℕ) (hy : Tendsto y atTop atTop) :
    Tendsto (fun x => (primeSieveProduct h (y x) / chenConst h) * Real.log (y x))
      atTop (nhds (2 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have htwin : Tendsto (fun x => twinPartialProduct (y x) / twinConst) atTop (nhds 1) := by
    simpa only [Function.comp_apply, div_self (ne_of_gt twinConst_pos)] using
      (twinPartialProduct_tendsto.comp hy).div_const twinConst
  have hlim := ((primeEulerProduct_mul_log_tendsto.comp hy).const_mul 2).mul htwin
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [hy.eventually (eventually_ge_atTop 2),
    hy.eventually (eventually_ge_atTop h)] with x hyx hyh
  dsimp only [Function.comp_apply]
  rw [primeSieveProduct_normalized h (y x) hh hyx, largeDivisorTail_eq_one_of_le h (y x) hyh]
  ring

theorem primeSieveProduct_fixed_power_normalized_tendsto (h : ℕ) (hh : h ≠ 0)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => (primeSieveProduct h (powerSieveCutoff a x) / chenConst h) * Real.log x)
      atTop (nhds (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hprod := primeSieveProduct_fixed_log_normalized_tendsto h hh (powerSieveCutoff a)
    (powerSieveCutoff_tendsto a ha)
  have hlim := hprod.div (log_powerSieveCutoff_div_log_tendsto a ha) (ne_of_gt ha)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    (powerSieveCutoff_tendsto a ha).eventually (eventually_ge_atTop 2)] with x hx hy
  have hlogx : Real.log (x : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  have hlogy : Real.log (powerSieveCutoff a x : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < powerSieveCutoff a x by omega)))
  have hC : chenConst h ≠ 0 := ne_of_gt (twinConst_pos.trans_le (twinConst_le_chenConst h))
  dsimp only [Pi.div_apply]
  field_simp

theorem chen_shifted_sieveProduct_eq (h x : ℕ) (hx : 1 ≤ x) :
    sieveProduct (chenShiftedSmallPrimes h x) primeDensity
      (powerSieveCutoff ((1 : ℝ) / 10) x + 1) =
      primeSieveProduct h (powerSieveCutoff ((1 : ℝ) / 10) x) := by
  have hz : ∀ p ∈ chenShiftedSmallPrimes h x, p < powerSieveCutoff ((1 : ℝ) / 10) x + 1 := by
    intro p hp
    have hpS := (mem_filter.mp hp).1
    rw [chenSmallPrimes_eq_oddPrimesLE x hx] at hpS
    have := (Nat.mem_primesLE.mp (mem_filter.mp hpS).1).1
    omega
  rw [sieveProduct_eq_prod _ _ _ hz]
  unfold chenShiftedSmallPrimes primeSieveProduct
  rw [chenSmallPrimes_eq_oddPrimesLE x hx]

/-- The fixed-shift counterpart of equation (25), for the exact sifting
prime set used in the finite translated prime sequence. -/
theorem chen_shifted_sieve_product_normalization (h : ℕ) (hh : h ≠ 0) :
    Tendsto (fun x : ℕ =>
      sieveProduct (chenShiftedSmallPrimes h x) primeDensity
        (powerSieveCutoff ((1 : ℝ) / 10) x + 1) * Real.log x / chenConst h)
      atTop (nhds (20 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have hp := primeSieveProduct_fixed_power_normalized_tendsto h hh ((1 : ℝ) / 10) (by norm_num)
  have heq : 2 * Real.exp (-Real.eulerMascheroniConstant) / ((1 : ℝ) / 10) =
      20 * Real.exp (-Real.eulerMascheroniConstant) := by ring
  rw [heq] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  rw [chen_shifted_sieveProduct_eq h x hx]
  ring

end Chen.LinearSieve
