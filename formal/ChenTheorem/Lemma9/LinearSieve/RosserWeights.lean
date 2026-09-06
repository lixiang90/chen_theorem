import ChenTheorem.Lemma9.LinearSieve.Rosser
import Mathlib.Data.Nat.GCD.BigOperators

open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem rosserCoefficient_eq_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (upper : Bool) (D : ℝ) (d : ℕ) :
    rosserCoefficient P z upper D d =
      ∑ ps ∈ (rosserTerms P z upper D).toFinset,
        if ps.prod = d then (-1 : ℝ) ^ ps.length else 0 := by
  by_cases hex : ∃ ps ∈ rosserTerms P z upper D, ps.prod = d
  · obtain ⟨ps, hps, rfl⟩ := hex
    rw [rosserCoefficient_eq_term P hP z upper D hps]
    symm
    rw [sum_eq_single ps]
    · simp
    · intro qs hqs hne
      have hprod : qs.prod ≠ ps.prod := fun h =>
        hne (rosserTerms_prod_injective P hP z upper D (List.mem_toFinset.mp hqs) hps h)
      simp [hprod]
    · intro hnot
      exact (hnot (List.mem_toFinset.mpr hps)).elim
  · rw [rosserCoefficient, dif_neg hex]
    symm
    apply sum_eq_zero
    intro ps hps
    have hprod : ps.prod ≠ d := fun h => hex ⟨ps, List.mem_toFinset.mp hps, h⟩
    simp [hprod]

/-- Reindex any finite arithmetic coefficient sum by its unique prime
strings. This is also the bridge to the recursive local-density polynomial. -/
theorem sum_rosserCoefficient (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (upper : Bool) (D : ℝ)
    (S : Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ S, rosserCoefficient P z upper D d * f d) =
      ∑ ps ∈ (rosserTerms P z upper D).toFinset,
        if ps.prod ∈ S then (-1 : ℝ) ^ ps.length * f ps.prod else 0 := by
  simp_rw [rosserCoefficient_eq_sum P hP, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro ps _
  simp only [ite_mul, zero_mul]
  simp

/-- Products of distinct primes divide n precisely when every factor does. -/
theorem descending_primes_prod_dvd {ps : List ℕ}
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hsorted : ps.Pairwise (· > ·)) (n : ℕ) :
    ps.prod ∣ n ↔ ∀ p ∈ ps, p ∣ n := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : Nat.Prime p := hprime p (by simp)
    have hprime' : ∀ q ∈ ps, Nat.Prime q := fun q hq => hprime q (by simp [hq])
    obtain ⟨hless, hsorted'⟩ := List.pairwise_cons.mp hsorted
    have hcop : p.Coprime ps.prod := Nat.coprime_list_prod_right_iff.mpr
      (fun q hq => (Nat.coprime_primes hp (hprime' q hq)).mpr (hless q hq).ne')
    constructor
    · intro h q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (dvd_mul_right _ _).trans h
      · exact (ih hprime' hsorted').mp ((dvd_mul_left ps.prod p).trans h) q hq
    · intro h
      exact hcop.mul_dvd_of_dvd_of_dvd (h p (by simp))
        ((ih hprime' hsorted').mpr (fun q hq => h q (by simp [hq])))

/-- Evaluate a surviving monomial on the divisibility indicators. -/
theorem rosserTermValue_divisibility (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (upper : Bool) (D : ℝ)
    {ps : List ℕ} (hps : ps ∈ rosserTerms P z upper D) (n : ℕ) :
    rosserTermValue (fun p => if p ∣ n then 1 else 0) ps =
      if ps.prod ∣ n then (-1 : ℝ) ^ ps.length else 0 := by
  have hsort := mem_rosserTerms_pairwise P z upper D hps
  have hprime : ∀ p ∈ ps, Nat.Prime p := fun p hp =>
    hP p (mem_rosserTerms_factors P z upper D hps p hp).1
  have hn : ps.Nodup := hsort.imp (fun h => ne_of_gt h)
  have hprod : (ps.map (fun p => if p ∣ n then (1 : ℝ) else 0)).prod =
      if ps.prod ∣ n then 1 else 0 := by
    rw [← List.prod_toFinset _ hn, Finset.prod_boole]
    simp only [List.mem_toFinset]
    simp only [← descending_primes_prod_dvd hprime hsort n]
  rw [rosserTermValue, hprod]
  split_ifs <;> simp

/-- Divisor sums of the constructed arithmetic coefficients are exactly
the recursive sieve polynomials on divisibility indicators. -/
theorem sum_divisors_rosserCoefficient (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (upper : Bool) (D : ℝ)
    (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, rosserCoefficient P z upper D d) =
      rosserEval P (fun p => if p ∣ n then 1 else 0) z upper D := by
  have hsum := sum_rosserCoefficient P hP z upper D n.divisors (fun _ => 1)
  simp only [mul_one] at hsum
  rw [hsum, ← rosserTerms_sum]
  rw [← List.sum_toFinset _ (rosserTerms_nodup P z upper D)]
  apply sum_congr rfl
  intro ps hps
  simpa [Nat.mem_divisors, hn] using
    (rosserTermValue_divisibility P hP z upper D (List.mem_toFinset.mp hps) n).symm

/-- With n = 1, every prime divisibility indicator vanishes. -/
theorem sieveProduct_divisibility_one (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) :
    sieveProduct P (fun p => if p ∣ 1 then 1 else 0) z = 1 := by
  apply prod_eq_one
  intro p _
  by_cases hp : p ∈ P
  · simp [hp, (hP p hp).not_dvd_one]
  · simp [hp]

/-- On divisors of the sifting product, the exact density product is the
delta function at 1. All sifting primes must lie below z. -/
theorem sieveProduct_divisibility_of_dvd (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (hz : ∀ p ∈ P, p < z)
    (n : ℕ) (hn : n ∣ ∏ p ∈ P, p) :
    sieveProduct P (fun p => if p ∣ n then 1 else 0) z =
      if n = 1 then 1 else 0 := by
  by_cases hn1 : n = 1
  · subst n
    simpa using sieveProduct_divisibility_one P hP z
  · rw [if_neg hn1]
    obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff id).mp (hqn.trans hn)
    have hqP : q ∈ P := by
      rcases (Nat.dvd_prime (hP p hp)).mp hqp with hq1 | rfl
      · exact (hq.ne_one hq1).elim
      · exact hp
    exact Finset.prod_eq_zero (mem_range.mpr (hz q hqP)) (by simp [hqP, hqn])

/-- The constructed lower coefficients satisfy the correct local
Moebius condition. -/
theorem rosserCoefficient_isLowerMoebius (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) :
    IsLowerMoebius (∏ p ∈ P, p) (rosserCoefficient P z false D) := by
  intro n hndiv
  by_cases hn : n = 0
  · simp [hn]
  · rw [sum_divisors_rosserCoefficient P hP z false D n hn]
    calc
      _ ≤ sieveProduct P (fun p => if p ∣ n then 1 else 0) z :=
        (rosserEval_bounds P _ (by intro p hp; split_ifs <;> norm_num) z D).1
      _ = _ := sieveProduct_divisibility_of_dvd P hP z hz n hndiv

/-- The upper coefficients even satisfy Mathlib's global upper-Moebius
condition, including integers with prime factors outside the sifting set. -/
theorem rosserCoefficient_isUpperMoebius (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (D : ℝ) :
    BoundingSieve.IsUpperMoebius (rosserCoefficient P z true D) := by
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [sum_divisors_rosserCoefficient P hP z true D n hn]
    have hprod : (if n = 1 then (1 : ℝ) else 0) ≤
        sieveProduct P (fun p => if p ∣ n then 1 else 0) z := by
      by_cases hn1 : n = 1
      · subst n
        rw [if_pos rfl, sieveProduct_divisibility_one P hP z]
      · simp only [if_neg hn1]
        exact sieveProduct_nonneg P _ z (by intro p hp; split_ifs <;> norm_num)
    exact hprod.trans
      (rosserEval_bounds P _ (by intro p hp; split_ifs <;> norm_num) z D).2

/-- Existence of actual Rosser lower and upper weights, with coefficients
bounded by one and strict level-D support. This theorem constructs the
weights explicitly; it does not assume a sieve-existence input. -/
theorem exists_rosser_sieve_weights (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (z : ℕ) (hz : ∀ p ∈ P, p < z)
    (D : ℝ) (hD : 1 < D) :
    ∃ lower upper : ℕ → ℝ,
      IsLowerMoebius (∏ p ∈ P, p) lower ∧
      BoundingSieve.IsUpperMoebius upper ∧
      (∀ d, |lower d| ≤ 1 ∧ |upper d| ≤ 1) ∧
      (∀ d : ℕ, D ≤ d → lower d = 0 ∧ upper d = 0) := by
  refine ⟨rosserCoefficient P z false D, rosserCoefficient P z true D,
    rosserCoefficient_isLowerMoebius P hP z hz D,
    rosserCoefficient_isUpperMoebius P hP z D, ?_, ?_⟩
  · intro d
    exact ⟨abs_rosserCoefficient_le_one P z false D d,
      abs_rosserCoefficient_le_one P z true D d⟩
  · intro d hd
    exact ⟨rosserCoefficient_eq_zero_of_level P hP z false D hD d hd,
      rosserCoefficient_eq_zero_of_level P hP z true D hD d hd⟩

end Chen.LinearSieve
