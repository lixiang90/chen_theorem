import Submission.ChenTheorem.Lemma9.LinearSieve.ReducedPrimeCounts
import Submission.ChenTheorem.Defs

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- The full small-prime set occurring in Chen's definitions of the two
ordinary sieve counts. -/
noncomputable def chenSmallPrimes (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter (fun p => p.Prime ∧ 2 < p ∧
    (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10))

theorem mem_chenSmallPrimes {x p : ℕ} (hx : 1 ≤ x) :
    p ∈ chenSmallPrimes x ↔ p.Prime ∧ 2 < p ∧
      (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
  constructor
  · intro h; exact (mem_filter.mp h).2
  · intro h
    have hpx : p ≤ x := by
      exact_mod_cast h.2.2.trans
        (Real.rpow_le_self_of_one_le (by exact_mod_cast hx) (by norm_num))
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), h⟩

theorem chenSmallPrimes_prime (x : ℕ) : ∀ p ∈ chenSmallPrimes x, Nat.Prime p :=
  fun _ hp => (mem_filter.mp hp).2.1

theorem coprime_chenSmallPrimes_iff (x : ℕ) (hx : 1 ≤ x) (n : ℕ) :
    (∏ r ∈ chenSmallPrimes x, r).Coprime n ↔
      ∀ r : ℕ, r.Prime → 2 < r → (r : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) → ¬r ∣ n := by
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h r hr hodd hsmall
    exact hr.coprime_iff_not_dvd.mp (h r ((mem_chenSmallPrimes hx).mpr ⟨hr, hodd, hsmall⟩))
  · intro h r hr
    obtain ⟨hprime, hodd, hsmall⟩ := (mem_chenSmallPrimes hx).mp hr
    exact hprime.coprime_iff_not_dvd.mpr (h r hprime hodd hsmall)

theorem sievedPrimeCount_eq_card (x : ℕ) (hx : 1 ≤ x) :
    sievedPrimeCount x = (primeDifferenceSiftedPrimes x (chenSmallPrimes x)).card := by
  unfold sievedPrimeCount primeDifferenceSiftedPrimes
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc, coprime_chenSmallPrimes_iff x hx]
  constructor
  · rintro ⟨hp, hprime, hsieve⟩
    exact ⟨⟨hprime.one_le, by omega⟩, hprime, hsieve⟩
  · rintro ⟨⟨_, hp⟩, hprime, hsieve⟩
    exact ⟨by omega, hprime, hsieve⟩

theorem sievedPrimeCountAt_eq_card (x k : ℕ) (hx : 1 ≤ x) :
    sievedPrimeCountAt x k =
      (primeDifferenceSiftedPrimesAt x k (chenSmallPrimes x)).card := by
  unfold sievedPrimeCountAt primeDifferenceSiftedPrimesAt primeDifferenceSiftedPrimes
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc, coprime_chenSmallPrimes_iff x hx]
  constructor
  · rintro ⟨hp, hprime, hkd, hsieve⟩
    exact ⟨⟨⟨hprime.one_le, by omega⟩, hprime, hsieve⟩, hkd⟩
  · rintro ⟨⟨⟨_, hp⟩, hprime, hsieve⟩, hkd⟩
    exact ⟨by omega, hprime, hkd, hsieve⟩

/-- Chen's actual ordinary-count expression is obtained from the reduced
logarithmic main and correction estimates, with explicit small-prime and
non-reduced-residue losses. No sieve asymptotic is assumed here. -/
theorem chen_count_lower_of_log_bounds (x : ℕ) (hx : 1 < x) (hxnp : ¬x.Prime)
    (T : ℝ) (hT : 1 < T) (L U : ℝ)
    (hL : L ≤ primeDifferenceSiftedSum x ((chenSmallPrimes x).filter (fun r => ¬r ∣ x)))
    (hU : (∑ k ∈ midPrimes x with ¬k ∣ x,
      primeDifferenceSiftedSumAt x k ((chenSmallPrimes x).filter (fun r => ¬r ∣ x))) ≤ U) :
    L / Real.log x - (1 / 2) * (U / T.log) - 5 * (⌈T⌉₊ : ℝ) -
        (3 / 2) * x.primeFactors.card ≤
      (sievedPrimeCount x : ℝ) - (1 / 2) * ∑ k ∈ midPrimes x, (sievedPrimeCountAt x k : ℝ) := by
  have hK : ∀ k ∈ midPrimes x, Nat.Prime k := fun k hk => (mem_filter.mp hk).2.1
  have hlarge : ∀ k ∈ (midPrimes x).filter (fun k => ¬k ∣ x),
      (x : ℝ) ^ ((1 : ℝ) / 10) < k := by
    intro k hk
    exact (mem_filter.mp (mem_filter.mp hk).1).2.2.1
  have hc := primeDifference_count_lower_of_log_bounds x hx hxnp
    ((chenSmallPrimes x).filter (fun r => ¬r ∣ x)) ((midPrimes x).filter (fun k => ¬k ∣ x))
    (fun k hk => hK k (mem_filter.mp hk).1) hlarge T hT L U hL hU
  have hr := primeDifferenceWeightedCount_reduced_le x (by omega) (chenSmallPrimes x)
    (midPrimes x) (chenSmallPrimes_prime x) hK
  have h := (sub_le_sub_right hc ((3 / 2) * (x.primeFactors.card : ℝ))).trans hr
  simpa only [primeDifferenceWeightedCount, sievedPrimeCount_eq_card x hx.le,
    sievedPrimeCountAt_eq_card x _ hx.le] using h

/-- Small sifting primes whose residue class is reduced. -/
noncomputable abbrev chenReducedSmallPrimes (x : ℕ) : Finset ℕ :=
  (chenSmallPrimes x).filter (fun r => ¬r ∣ x)

/-- Middle primes whose residue class is reduced. -/
noncomputable abbrev chenReducedMidPrimes (x : ℕ) : Finset ℕ :=
  (midPrimes x).filter (fun k => ¬k ∣ x)

/-- A fully constructed finite sieve lower bound for the exact two counts
in equation (26). Remaining tasks are the sharp asymptotics of these
explicit Rosser polynomials and the asymptotic choice of the parameters. -/
theorem chen_count_lower_of_rosser_polynomials (x : ℕ) (hx : 1 < x) (hxnp : ¬x.Prime)
    (T : ℝ) (hT : 1 < T) (z : ℕ) (hz : ∀ p ∈ chenReducedSmallPrimes x, p < z)
    (Q : ℕ) (D : ℝ) (hD : 1 < D) (hDQ : D ≤ Q)
    (DAt : ℕ → ℝ) (hDAt : ∀ k ∈ chenReducedMidPrimes x, 1 < DAt k)
    (hDAtQ : ∀ k ∈ chenReducedMidPrimes x, DAt k ≤ (Q / k : ℕ)) :
    (((x : ℝ) * rosserEval (chenReducedSmallPrimes x) primeDensity z false D -
        ∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) / Real.log x) -
      (1 / 2) * (((∑ k ∈ chenReducedMidPrimes x,
        ((x : ℝ) / Nat.totient k) *
          rosserEval (chenReducedSmallPrimes x) primeDensity z true (DAt k)) +
        ∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) / T.log) -
      5 * (⌈T⌉₊ : ℝ) - (3 / 2) * x.primeFactors.card ≤
      (sievedPrimeCount x : ℝ) - (1 / 2) * ∑ k ∈ midPrimes x, (sievedPrimeCountAt x k : ℝ) := by
  have hP : ∀ p ∈ chenReducedSmallPrimes x, Nat.Prime p :=
    fun p hp => chenSmallPrimes_prime x p (mem_filter.mp hp).1
  have hodd : ∀ p ∈ chenReducedSmallPrimes x, 2 < p :=
    fun p hp => ((mem_chenSmallPrimes hx.le).mp (mem_filter.mp hp).1).2.1
  have hK : ∀ k ∈ chenReducedMidPrimes x, Nat.Prime k :=
    fun k hk => (mem_filter.mp (mem_filter.mp hk).1).2.1
  have hsep : ∀ p ∈ chenReducedSmallPrimes x, ∀ k ∈ chenReducedMidPrimes x, p < k := by
    intro p hp k hk
    have hpSmall := ((mem_chenSmallPrimes hx.le).mp (mem_filter.mp hp).1).2.2
    have hkLarge := (mem_filter.mp (mem_filter.mp hk).1).2.2.1
    exact_mod_cast lt_of_le_of_lt hpSmall hkLarge
  have hcopP : x.Coprime (∏ p ∈ chenReducedSmallPrimes x, p) :=
    Nat.coprime_prod_right_iff.mpr (fun p hp =>
      ((hP p hp).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2).symm)
  have hcopK : ∀ k ∈ chenReducedMidPrimes x, x.Coprime k :=
    fun k hk => ((hK k hk).coprime_iff_not_dvd.mpr (mem_filter.mp hk).2).symm
  obtain ⟨hlower, hupper⟩ := primeDifference_rosser_main_and_correction x
    (chenReducedSmallPrimes x) (chenReducedMidPrimes x) hP hodd hK hsep hcopP hcopK
    z hz Q D hD hDQ DAt hDAt hDAtQ
  exact chen_count_lower_of_log_bounds x hx hxnp T hT _ _ hlower hupper

end Chen.LinearSieve
