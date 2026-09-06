import ChenTheorem.Lemma9.LinearSieve.ChenPrimeCounts
import ChenTheorem.Analysis.MertensProduct
import ChenTheorem.Lemma7.SingularSeries

open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

noncomputable def oddPrimesLE (y : ℕ) : Finset ℕ := y.primesLE.filter (2 < ·)

noncomputable def primeSieveProduct (x y : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesLE y with ¬p ∣ x, (1 - primeDensity p)

noncomputable def twinPartialProduct (y : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesLE y, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)

noncomputable def smallDivisorCorrection (x y : ℕ) : ℝ :=
  ∏ p ∈ x.primeFactors with 2 < p ∧ p ≤ y, ((p : ℝ) - 1) / ((p : ℝ) - 2)

theorem oddPrimesLE_prime {p y : ℕ} (hp : p ∈ oddPrimesLE y) : p.Prime :=
  (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2

/-- The exact algebraic decomposition of the sieve density product into
the ordinary Euler product, twin-prime factors and divisor corrections. -/
theorem primeSieveProduct_factorization (x y : ℕ) (hx : x ≠ 0) :
    primeSieveProduct x y =
      (∏ p ∈ oddPrimesLE y, (1 - (1 : ℝ) / p)) * twinPartialProduct y *
        smallDivisorCorrection x y := by
  have hset : (oddPrimesLE y).filter (fun p => p ∣ x) =
      x.primeFactors.filter (fun p => 2 < p ∧ p ≤ y) := by
    ext p
    simp only [oddPrimesLE, mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    tauto
  rw [smallDivisorCorrection, ← hset, prod_filter, twinPartialProduct,
    ← prod_mul_distrib, ← prod_mul_distrib, primeSieveProduct, prod_filter]
  apply prod_congr rfl
  intro p hp
  have hpp := oddPrimesLE_prime hp
  have hpR : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  simp only [primeDensity_apply, Nat.totient_prime hpp, Nat.cast_sub hpp.one_le, Nat.cast_one]
  split_ifs <;> field_simp <;> ring

theorem oddPrimeEulerProduct_eq (y : ℕ) (hy : 2 ≤ y) :
    (∏ p ∈ oddPrimesLE y, (1 - (1 : ℝ) / p)) = 2 * primeEulerProduct y := by
  have h2 : 2 ∈ y.primesLE := Nat.mem_primesLE.mpr ⟨hy, Nat.prime_two⟩
  have hset : oddPrimesLE y = y.primesLE.erase 2 := by
    ext p
    simp only [oddPrimesLE, mem_filter, mem_erase, Nat.mem_primesLE]
    constructor
    · intro h; exact ⟨by omega, h.1⟩
    · rintro ⟨hne, hp, hprime⟩
      exact ⟨⟨hp, hprime⟩, by have := hprime.two_le; omega⟩
  rw [hset, primeEulerProduct, ← prod_erase_mul _ _ h2]
  norm_num
  ring

theorem primeSieveProduct_eq (x y : ℕ) (hx : x ≠ 0) (hy : 2 ≤ y) :
    primeSieveProduct x y = 2 * primeEulerProduct y * twinPartialProduct y *
      smallDivisorCorrection x y := by
  rw [primeSieveProduct_factorization x y hx, oddPrimeEulerProduct_eq y hy]

/-- Relate the recursive sieve's product to its intrinsic prime set. -/
theorem sieveProduct_eq_prod (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ)
    (hz : ∀ p ∈ P, p < z) : sieveProduct P w z = ∏ p ∈ P, (1 - w p) := by
  unfold sieveProduct
  have hset : (range z).filter (fun p => p ∈ P) = P := by
    ext p
    simp only [mem_filter, mem_range]
    exact ⟨And.right, fun hp => ⟨hz p hp, hp⟩⟩
  rw [← hset, prod_filter]
  apply prod_congr rfl
  intro p _
  split_ifs <;> simp_all

end Chen.LinearSieve
