import Submission.ChenTheorem.Lemma9.LinearSieve.DivisorProductTail

set_option autoImplicit true
open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

theorem twinPartialProduct_tendsto : Tendsto twinPartialProduct atTop (nhds twinConst) := by
  let I : ℕ → Finset Nat.Primes := fun y => y.primesLE.attach.image
    (fun p => (⟨p.val, (Nat.mem_primesLE.mp p.property).2⟩ : Nat.Primes))
  have hmem (y : ℕ) (p : Nat.Primes) : p ∈ I y ↔ (p : ℕ) ≤ y := by
    constructor
    · intro hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      exact (Nat.mem_primesLE.mp q.property).1
    · intro hp
      exact Finset.mem_image.mpr
        ⟨⟨p.val, Nat.mem_primesLE.mpr ⟨hp, p.property⟩⟩, mem_attach _ _, rfl⟩
  have hI : Tendsto I atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone
    · intro y z hyz p hp
      exact (hmem z p).mpr (((hmem y p).mp hp).trans hyz)
    · intro p
      refine ⟨(p : ℕ), ?_⟩
      exact (hmem (p : ℕ) p).mpr le_rfl
  have hraw : Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, twinLocalFactor p) atTop
      (nhds twinConst) := by
    have h := multipliable_twinLocalFactor.hasProd
    change Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, twinLocalFactor p) atTop
      (nhds (∏' p : Nat.Primes, twinLocalFactor p)) at h
    rw [← twinConst_eq_tprod_twinLocalFactor] at h
    exact h
  have heq (y : ℕ) : (∏ p ∈ I y, twinLocalFactor p) = twinPartialProduct y := by
    let f : ℕ → ℝ := fun p => if 2 < p then 1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2 else 1
    have hinj : ∀ p ∈ y.primesLE.attach, ∀ q ∈ y.primesLE.attach,
        (⟨p.val, (Nat.mem_primesLE.mp p.property).2⟩ : Nat.Primes) =
          ⟨q.val, (Nat.mem_primesLE.mp q.property).2⟩ → p = q := by
      intro p _ q _ hpq
      apply Subtype.ext
      exact congrArg (fun r : Nat.Primes => (r : ℕ)) hpq
    calc
      _ = ∏ p ∈ y.primesLE.attach,
          twinLocalFactor (⟨p.val, (Nat.mem_primesLE.mp p.property).2⟩ : Nat.Primes) :=
        prod_image hinj
      _ = ∏ p ∈ y.primesLE.attach, f p.val := by
        apply prod_congr rfl
        intro p _
        dsimp only [f, twinLocalFactor, twinFactorIncrement]
        split_ifs <;> ring
      _ = ∏ p ∈ y.primesLE, f p := prod_attach _ f
      _ = _ := by simp only [f, twinPartialProduct, oddPrimesLE, prod_filter]
  exact (hraw.comp hI).congr' (Eventually.of_forall heq)

/-- The cutoff error is uniform in the residue parameter whenever its
prime-factor count is negligible relative to the sieve cutoff. -/
theorem largeDivisorTail_tendsto (y : ℕ → ℕ) (hy : Tendsto y atTop atTop)
    (hratio : Tendsto (fun x : ℕ => (x.primeFactors.card : ℝ) / y x) atTop (nhds 0)) :
    Tendsto (fun x => largeDivisorTail x (y x)) atTop (nhds 1) := by
  have hlower : Tendsto (fun x : ℕ => 1 - (x.primeFactors.card : ℝ) / y x) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [hy.eventually (eventually_ge_atTop 2)] with x hx
    exact (largeDivisorTail_bounds x (y x) hx).2.2
  · filter_upwards [hy.eventually (eventually_ge_atTop 2)] with x hx
    exact (largeDivisorTail_bounds x (y x) hx).2.1

/-- Uniform normalized sieve product along any sufficiently large cutoff
whose size dominates the number of distinct prime factors of `x`. -/
theorem primeSieveProduct_log_normalized_tendsto (y : ℕ → ℕ) (hy : Tendsto y atTop atTop)
    (hratio : Tendsto (fun x : ℕ => (x.primeFactors.card : ℝ) / y x) atTop (nhds 0)) :
    Tendsto (fun x => (primeSieveProduct x (y x) / chenConst x) * Real.log (y x)) atTop
      (nhds (2 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have htwin : Tendsto (fun x => twinPartialProduct (y x) / twinConst) atTop (nhds 1) := by
    simpa only [Function.comp_apply, div_self (ne_of_gt twinConst_pos)] using
      (twinPartialProduct_tendsto.comp hy).div_const twinConst
  have hlim := (((primeEulerProduct_mul_log_tendsto.comp hy).const_mul 2).mul htwin).mul
    (largeDivisorTail_tendsto y hy hratio)
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ), hy.eventually (eventually_ge_atTop 2)] with x hx hyx
  dsimp only [Function.comp_apply]
  rw [primeSieveProduct_normalized x (y x) (by omega) hyx]
  ring

end Chen.LinearSieve
