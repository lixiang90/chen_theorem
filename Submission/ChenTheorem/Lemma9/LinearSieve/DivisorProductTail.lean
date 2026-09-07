import Submission.ChenTheorem.Lemma9.LinearSieve.SieveProduct

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- The inverse correction contributed by prime divisors beyond the
sieving cutoff. Keeping it explicit yields uniform bounds as `x` varies. -/
noncomputable def largeDivisorTail (x y : ℕ) : ℝ :=
  ∏ p ∈ x.primeFactors with 2 < p ∧ y < p, (1 - primeDensity p)

theorem smallDivisorCorrection_mul_twinConst (x y : ℕ) :
    smallDivisorCorrection x y * twinConst = chenConst x * largeDivisorTail x y := by
  have hprod : smallDivisorCorrection x y =
      (∏ p ∈ x.primeFactors with 2 < p, ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        largeDivisorTail x y := by
    unfold smallDivisorCorrection largeDivisorTail
    simp only [prod_filter]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hodd : 2 < p
    · have hpR : (2 : ℝ) < p := by exact_mod_cast hodd
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
      simp only [hodd, true_and, if_true, primeDensity_apply, Nat.totient_prime hpp,
        Nat.cast_sub hpp.one_le, Nat.cast_one]
      by_cases hpy : p ≤ y
      · simp [hpy, Nat.not_lt.mpr hpy]
      · simp only [hpy, if_false, Nat.lt_of_not_ge hpy, if_true]
        field_simp
        ring
    · simp [hodd]
  rw [hprod, chenConst]
  ring

theorem one_sub_sum_le_prod_one_sub (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ S, 0 ≤ w p ∧ w p ≤ 1) :
    1 - (∑ p ∈ S, w p) ≤ ∏ p ∈ S, (1 - w p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have haW := hw a (mem_insert_self _ _)
    have hS : ∀ p ∈ S, 0 ≤ w p ∧ w p ≤ 1 := fun p hp => hw p (mem_insert_of_mem hp)
    have hsum : 0 ≤ ∑ p ∈ S, w p := sum_nonneg (fun p hp => (hS p hp).1)
    rw [sum_insert ha, prod_insert ha]
    calc
      _ ≤ (1 - w a) * (1 - ∑ p ∈ S, w p) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih hS) (sub_nonneg.mpr haW.2)

theorem largeDivisorTail_bounds (x y : ℕ) (hy : 2 ≤ y) :
    0 ≤ largeDivisorTail x y ∧ largeDivisorTail x y ≤ 1 ∧
      1 - (x.primeFactors.card : ℝ) / y ≤ largeDivisorTail x y := by
  let S := x.primeFactors.filter (fun p => 2 < p ∧ y < p)
  have hw (p : ℕ) (hp : p ∈ S) : 0 ≤ primeDensity p ∧ primeDensity p ≤ (1 : ℝ) / y := by
    have hprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have hyp := (mem_filter.mp hp).2.2
    have hypR : (y : ℝ) + 1 ≤ p := by exact_mod_cast (show y + 1 ≤ p by omega)
    have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
    have hyp' : (y : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have hp1pos : 0 < (p : ℝ) - 1 := by linarith
    simp only [primeDensity_apply, Nat.totient_prime hprime, Nat.cast_sub hprime.one_le, Nat.cast_one]
    constructor
    · positivity
    · rw [← one_div]
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < y by omega)) hyp'
  have hwone : ∀ p ∈ S, 0 ≤ primeDensity p ∧ primeDensity p ≤ 1 := by
    intro p hp
    exact ⟨(hw p hp).1, (hw p hp).2.trans ((div_le_one (by exact_mod_cast (show 0 < y by omega))).mpr
      (by exact_mod_cast (show 1 ≤ y by omega)))⟩
  have hsum : (∑ p ∈ S, primeDensity p) ≤ (x.primeFactors.card : ℝ) / y := by
    calc
      _ ≤ ∑ _p ∈ S, (1 : ℝ) / y := sum_le_sum (fun p hp => (hw p hp).2)
      _ = (S.card : ℝ) / y := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast card_filter_le _ _) (by positivity)
  exact ⟨prod_nonneg (fun p hp => sub_nonneg.mpr (hwone p hp).2),
    prod_le_one (fun p hp => sub_nonneg.mpr (hwone p hp).2)
      (fun p hp => sub_le_self _ (hwone p hp).1),
    (sub_le_sub_left hsum 1).trans (one_sub_sum_le_prod_one_sub S primeDensity hwone)⟩

/-- Exact normalization by Chen's singular series, with the only
`x`-dependent truncation isolated in `largeDivisorTail`. -/
theorem primeSieveProduct_normalized (x y : ℕ) (hx : x ≠ 0) (hy : 2 ≤ y) :
    primeSieveProduct x y / chenConst x =
      2 * primeEulerProduct y * (twinPartialProduct y / twinConst) * largeDivisorTail x y := by
  have hC : chenConst x ≠ 0 := ne_of_gt (twinConst_pos.trans_le (twinConst_le_chenConst x))
  have htwin : twinConst ≠ 0 := ne_of_gt twinConst_pos
  have hsmall := smallDivisorCorrection_mul_twinConst x y
  have hratio : smallDivisorCorrection x y / chenConst x = largeDivisorTail x y / twinConst :=
    (div_eq_div_iff hC htwin).mpr (by simpa only [mul_comm] using hsmall)
  rw [primeSieveProduct_eq x y hx hy]
  calc
    _ = 2 * primeEulerProduct y * twinPartialProduct y *
        (smallDivisorCorrection x y / chenConst x) := by ring
    _ = _ := by rw [hratio]; ring

end Chen.LinearSieve
