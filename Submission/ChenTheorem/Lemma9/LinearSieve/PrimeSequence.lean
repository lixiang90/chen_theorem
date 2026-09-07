import Submission.ChenTheorem.Lemma9.LinearSieve.RosserSieve
import Submission.ChenTheorem.Lemma9.BombieriVinogradov.PrimeWeights
import Mathlib.Data.Nat.Totient

set_option autoImplicit true

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- Local density of a reduced residue class among primes. -/
noncomputable def primeDensity : ArithmeticFunction ℝ :=
  ⟨fun d => (Nat.totient d : ℝ)⁻¹, by simp⟩

@[simp] theorem primeDensity_apply (d : ℕ) :
    primeDensity d = (Nat.totient d : ℝ)⁻¹ := rfl

theorem primeDensity_multiplicative : primeDensity.IsMultiplicative := by
  constructor
  · simp
  · intro m n hmn
    simp [Nat.totient_mul hmn, mul_inv_rev, mul_comm]

theorem squarefree_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Squarefree (∏ p ∈ P, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (hP p hp).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq

/-- The prime `p = x - n` contributes its logarithm to the sieve sequence. -/
noncomputable def primeDifferenceWeight (x n : ℕ) : ℝ :=
  if (x - n).Prime then Real.log ((x - n : ℕ) : ℝ) else 0

theorem primeDifferenceWeight_nonneg (x n : ℕ) :
    0 ≤ primeDifferenceWeight x n := by
  unfold primeDifferenceWeight
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · exact le_rfl

/-- The actual logarithmically weighted sequence `x - p`, `p ≤ x`.
The prime `2` is excluded from `P`, since its density is one. -/
noncomputable def primeDifferenceSieve (x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) : BoundingSieve where
  support := (Icc 1 x).image (fun p => x - p)
  prodPrimes := ∏ p ∈ P, p
  prodPrimes_squarefree := squarefree_prod_primes P hP
  weights := primeDifferenceWeight x
  weights_nonneg := primeDifferenceWeight_nonneg x
  totalMass := x
  nu := primeDensity
  nu_mult := primeDensity_multiplicative
  nu_pos_of_prime := by
    intro p hp _
    simp only [primeDensity_apply, inv_pos]
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  nu_lt_one_of_prime := by
    intro p hp hd
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hP q hq)).mp hpq
    subst q
    simp only [primeDensity_apply, Nat.totient_prime hp]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast (show 1 < p - 1 by have := hodd p hq; omega)

theorem sum_primeDifference_support (x : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ (Icc 1 x).image (fun p => x - p), f n) =
      ∑ p ∈ Icc 1 x, f (x - p) := by
  apply sum_image
  intro p hp q hq heq
  dsimp at heq
  have hp' := (mem_Icc.mp hp).2
  have hq' := (mem_Icc.mp hq).2
  omega

/-- Multiples of `d` in the difference sequence are precisely primes in
the progression `x mod d`. No equidistribution assumption is used here. -/
theorem primeDifferenceSieve_multSum (x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) (d : ℕ) :
    (primeDifferenceSieve x P hP hodd).multSum d =
      BombieriVinogradov.progressionTheta x d x := by
  change (∑ n ∈ (Icc 1 x).image (fun p => x - p),
    if d ∣ n then primeDifferenceWeight x n else 0) = _
  rw [sum_primeDifference_support]
  apply sum_congr rfl
  intro p hp
  have hpx := (mem_Icc.mp hp).2
  have hsub : x - (x - p) = p := by omega
  simp only [primeDifferenceWeight, hsub, ← Nat.modEq_iff_dvd' hpx]
  split_ifs <;> simp_all

theorem primeDifferenceSieve_rem (x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) (d : ℕ) :
    (primeDifferenceSieve x P hP hodd).rem d =
      BombieriVinogradov.progressionTheta x d x - (x : ℝ) / Nat.totient d := by
  rw [BoundingSieve.rem, primeDifferenceSieve_multSum]
  simp [primeDifferenceSieve, div_eq_mul_inv, mul_comm]

/-- The sifted sum counts exactly the primes with `x - p` coprime to the
chosen sifting product, with logarithmic weights. -/
theorem primeDifferenceSieve_siftedSum (x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) :
    (primeDifferenceSieve x P hP hodd).siftedSum =
      ∑ p ∈ Icc 1 x, if p.Prime ∧ (∏ r ∈ P, r).Coprime (x - p)
        then Real.log p else 0 := by
  change (∑ n ∈ (Icc 1 x).image (fun p => x - p),
    if (∏ r ∈ P, r).Coprime n then primeDifferenceWeight x n else 0) = _
  rw [sum_primeDifference_support]
  apply sum_congr rfl
  intro p hp
  have hsub : x - (x - p) = p := by have := (mem_Icc.mp hp).2; omega
  simp only [primeDifferenceWeight, hsub]
  split_ifs <;> simp_all

/-- Logarithmic prime count after sifting `x - p` by `P`. -/
noncomputable def primeDifferenceSiftedSum (x : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ Icc 1 x, if p.Prime ∧ (∏ r ∈ P, r).Coprime (x - p)
    then Real.log p else 0

/-- The finite Rosser bounds for the actual difference sequence, expressed
entirely in terms of prime progression errors and explicit polynomials. -/
theorem primeDifference_rosser_bounds (x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (hcop : x.Coprime (∏ p ∈ P, p))
    (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) (hD : 1 < D)
    (Q : ℕ) (hDQ : D ≤ Q) :
    (x : ℝ) * rosserEval P primeDensity z false D -
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) ≤
      primeDifferenceSiftedSum x P ∧
    primeDifferenceSiftedSum x P ≤
      (x : ℝ) * rosserEval P primeDensity z true D +
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) := by
  have hb := rosser_sieve_bounds_of_remainders
    (primeDifferenceSieve x P hP hodd) P hP rfl z hz D hD Q hDQ
    (fun d => BombieriVinogradov.reducedThetaError x d x)
    (fun d => BombieriVinogradov.reducedThetaError_nonneg x d x) ?_
  · rw [primeDifferenceSieve_siftedSum] at hb
    simpa only [primeDifferenceSieve, primeDifferenceSiftedSum] using hb
  · intro d hd _
    have hdcop : x.Coprime d := hcop.of_dvd_right (Nat.mem_divisors.mp hd).1
    rw [primeDifferenceSieve_rem]
    dsimp only [BombieriVinogradov.reducedThetaError]
    rw [if_pos hdcop]

open Filter in
/-- Bombieri--Vinogradov controls the remainders of the concrete prime
difference sieve, uniformly in the chosen sifting primes and sieve level.
The only hypothesis here is the separately stated BV theorem. -/
theorem eventually_primeDifference_rosser_bounds
    (hBV : BombieriVinogradov.Statement) (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B →
        ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) → (∀ p ∈ P, 2 < p) →
        x.Coprime (∏ p ∈ P, p) →
        ∀ z : ℕ, (∀ p ∈ P, p < z) → ∀ D : ℝ, 1 < D → D ≤ Q →
          (x : ℝ) * rosserEval P primeDensity z false D -
              C * x / (Real.log x) ^ A ≤ primeDifferenceSiftedSum x P ∧
          primeDifferenceSiftedSum x P ≤
            (x : ℝ) * rosserEval P primeDensity z true D +
              C * x / (Real.log x) ^ A := by
  obtain ⟨B, C, hB, hC, herr⟩ := BombieriVinogradov.thetaStatement_reduced_errors
    (BombieriVinogradov.thetaStatement_of_statement hBV) A hA
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [herr] with x hx
  intro Q hQ P hP hodd hcop z hz D hD hDQ
  obtain ⟨hlower, hupper⟩ := primeDifference_rosser_bounds x P hP hodd hcop z hz D hD Q hDQ
  have he := hx Q hQ (fun _ => x)
  exact ⟨(sub_le_sub_left he _).trans hlower,
    hupper.trans (_root_.add_le_add le_rfl he)⟩

end Chen.LinearSieve
