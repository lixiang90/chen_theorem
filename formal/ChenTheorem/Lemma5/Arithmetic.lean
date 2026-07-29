import ChenTheorem.Lemma5.Core
import Mathlib.Data.Int.NatAbs

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- Every index retained by the smoothed `M` sum gives an integer argument
at most `x`. -/
theorem smoothedMArgument_le
    {x n : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    (hn : n ∈ smoothedMIndices x q) :
    q.1 * q.2 * n ≤ x := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with ⟨hp₁, hp₂, _⟩
  have hden : 0 < (q.1 : ℝ) * q.2 :=
    mul_pos (by exact_mod_cast hp₁.pos) (by exact_mod_cast hp₂.pos)
  have hn' := hn
  simp only [smoothedMIndices, Finset.mem_filter,
    Finset.mem_range] at hn'
  have hreal :
      (n : ℝ) * ((q.1 : ℝ) * q.2) ≤ x :=
    (le_div_iff₀ hden).mp hn'.2
  have hnat : n * (q.1 * q.2) ≤ x := by
    exact_mod_cast hreal
  simpa [mul_assoc, mul_comm, mul_left_comm] using hnat

/-- The divisor factor in equation (11) is uniformly bounded on the
smoothed range.  The zero displacement is harmless because `0.divisors` is
empty. -/
theorem displacement_divisors_card_le
    {m x : ℕ} (hm : m ≤ x) :
    ((Int.natAbs ((m : ℤ) - x)).divisors.card : ℝ) ≤
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 24) := by
  let a := Int.natAbs ((m : ℤ) - x)
  by_cases ha0 : a = 0
  · simp only [a, ha0, Nat.divisors_zero, Finset.card_empty,
      Nat.cast_zero]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  · have hcard := card_divisors_cast_le_rpow ha0
    have haeq : a = x - m := by
      simpa only [a] using
        (Int.natAbs_natCast_sub_natCast_of_le hm)
    have hale : a ≤ x := by omega
    have hpow :
        (a : ℝ) ^ ((1 : ℝ) / 24) ≤
          (x : ℝ) ^ ((1 : ℝ) / 24) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hale)
        (by norm_num)
    exact hcard.trans
      (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- If a prime power divides the argument of the primitive-character
majorant, coprimality removes every conductor divisible by its base prime. -/
theorem primitiveAssociateMajorant_le_primeFilter
    {d x m p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hpm : p ^ e ∣ m) :
    primitiveAssociateMajorant d x m ≤
      ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
        (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k : ℝ) := by
  rw [primitiveAssociateMajorant]
  have hsum :
      (∑ k : ↥d.divisors,
          if k.1 = 1 then 0
          else if m.Coprime k.1 then
            (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k.1 : ℝ)
          else 0) =
        ∑ k ∈ d.divisors,
          if k = 1 then 0
          else if m.Coprime k then
            (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k : ℝ)
          else 0 := by
    symm
    exact Finset.sum_subtype d.divisors (by simp)
      (fun k =>
        if k = 1 then 0
        else if m.Coprime k then
          (Nat.gcd (Int.natAbs ((m : ℤ) - x)) k : ℝ)
        else 0)
  rw [hsum]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    simp [hp.ne_one]
  · rw [if_neg hk1]
    by_cases hmk : m.Coprime k
    · rw [if_pos hmk]
      have hpowcop : (p ^ e).Coprime k :=
        Nat.Coprime.of_dvd_left hpm hmk
      have hpcop : p.Coprime k :=
        (Nat.coprime_pow_left_iff he p k).mp hpowcop
      rw [if_pos (hp.coprime_iff_not_dvd.mp hpcop)]
    · rw [if_neg hmk]
      positivity

/-- Equation (11), before summing over the two outer prime variables and the
smoothed von Mangoldt index: a fixed `(q,n)` contribution is controlled by
the least prime factor of `n` and the divisor count of its displacement from
`x`. -/
theorem mFiveArithmetic_inner_le
    {x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε)
    (q : ℕ × ℕ) (n : ℕ) :
    ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d x (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((Int.natAbs
                (((q.1 * q.2 * n : ℕ) : ℤ) - x)).divisors.card : ℝ)) := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · have hnpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, e, hp, he, hn⟩ := (isPrimePow_nat_iff n).mp hnpp
    subst n
    have hminfac : (p ^ e).minFac = p := by
      rw [Nat.pow_minFac he.ne', hp.minFac_eq]
    rw [hminfac]
    let a := Int.natAbs
      (((q.1 * q.2 * p ^ e : ℕ) : ℤ) - x)
    have hbad :
        ∀ d : ℕ, ¬(p ^ e).Coprime d ↔ p ∣ d := by
      intro d
      rw [Nat.coprime_pow_left_iff he p d,
        hp.coprime_iff_not_dvd]
      tauto
    have hassoc :
        ∀ d : ℕ,
          primitiveAssociateMajorant d x
              (q.1 * q.2 * p ^ e) ≤
            ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
              (Nat.gcd a k : ℝ) := by
      intro d
      exact primitiveAssociateMajorant_le_primeFilter
        hp he (by exact dvd_mul_left (p ^ e) (q.1 * q.2))
    calc
      ∑ d ∈ sieveModuli x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              (3 : ℝ) ^ distinctPrimeFactors d /
                (Nat.totient d : ℝ)) *
            (if ¬(p ^ e).Coprime d then
              ArithmeticFunction.vonMangoldt (p ^ e) *
                primitiveAssociateMajorant d x
                  (q.1 * q.2 * p ^ e)
            else 0) ≤
        ∑ d ∈ sieveModuli x ε,
          ((6 : ℝ) ^ (46656 : ℝ) *
              (d : ℝ) ^ (-(5 : ℝ) / 6)) *
            (if p ∣ d then
              ArithmeticFunction.vonMangoldt (p ^ e) *
                ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                  (Nat.gcd a k : ℝ)
            else 0) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hpd : p ∣ d
          · rw [if_pos ((hbad d).2 hpd), if_pos hpd]
            exact mul_le_mul
              (sieveCoefficient_le_decay_uniform d)
              (mul_le_mul_of_nonneg_left (hassoc d)
                ArithmeticFunction.vonMangoldt_nonneg)
              (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (primitiveAssociateMajorant_nonneg _ _ _))
              (mul_nonneg (by positivity)
                (Real.rpow_nonneg (by positivity) _))
          · simp [hpd, (hbad d).not.mpr hpd]
      _ = (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ∑ d ∈ (sieveModuli x ε).filter (p ∣ ·),
              (d : ℝ) ^ (-(5 : ℝ) / 6) *
                ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                  (Nat.gcd a k : ℝ) := by
          symm
          calc
            (6 : ℝ) ^ (46656 : ℝ) *
                ArithmeticFunction.vonMangoldt (p ^ e) *
                ∑ d ∈ (sieveModuli x ε).filter (p ∣ ·),
                  (d : ℝ) ^ (-(5 : ℝ) / 6) *
                    ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                      (Nat.gcd a k : ℝ) =
              ∑ d ∈ (sieveModuli x ε).filter (p ∣ ·),
                (6 : ℝ) ^ (46656 : ℝ) *
                  ArithmeticFunction.vonMangoldt (p ^ e) *
                  ((d : ℝ) ^ (-(5 : ℝ) / 6) *
                    ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                      (Nat.gcd a k : ℝ)) := by
                rw [Finset.mul_sum]
            _ = ∑ d ∈ sieveModuli x ε,
                ((6 : ℝ) ^ (46656 : ℝ) *
                    (d : ℝ) ^ (-(5 : ℝ) / 6)) *
                  (if p ∣ d then
                    ArithmeticFunction.vonMangoldt (p ^ e) *
                      ∑ k ∈ d.divisors.filter (fun k => ¬p ∣ k),
                        (Nat.gcd a k : ℝ)
                  else 0) := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hpd : p ∣ d
                · simp only [if_pos hpd]
                  ring
                · simp [hpd]
      _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ((x : ℝ) ^ ((1 : ℝ) / 12) *
              (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
                (a.divisors.card : ℝ)) :=
          by
            by_cases ha0 : a = 0
            · have heq :
                  q.1 * q.2 * p ^ e = x := by
                have hz :
                    (((q.1 * q.2 * p ^ e : ℕ) : ℤ) - x) = 0 := by
                  exact Int.natAbs_eq_zero.mp (by
                    simpa only [a] using ha0)
                exact_mod_cast (sub_eq_zero.mp hz)
              have hpx : p ∣ x := by
                rw [← heq]
                exact dvd_mul_of_dvd_right
                  (dvd_pow_self p he.ne') (q.1 * q.2)
              have hDempty :
                  (sieveModuli x ε).filter (p ∣ ·) = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro d hd
                have hd' := Finset.mem_filter.mp hd
                have hddata := (Finset.mem_filter.mp hd'.1).2
                have hpone := Nat.eq_one_of_dvd_coprimes
                  hddata.2.1 hd'.2 hpx
                exact hp.ne_one hpone
              simp [hDempty, ha0]
            · exact mul_le_mul_of_nonneg_left
                (modulus_conductor_gcd_sum_le hx1 hp ha0 hε)
                (mul_nonneg (by positivity)
                  ArithmeticFunction.vonMangoldt_nonneg)
      _ = (6 : ℝ) ^ (46656 : ℝ) *
          ArithmeticFunction.vonMangoldt (p ^ e) *
            ((x : ℝ) ^ ((1 : ℝ) / 12) *
              (p : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
                (a.divisors.card : ℝ)) := rfl

/-- Uniform form of the fixed-index estimate, after applying the
`n^(1/24)` divisor bound to the displacement. -/
theorem mFiveArithmetic_inner_le_uniform
    {x : ℕ} {ε : ℝ} (hx : 2 ≤ x) (hε : 0 ≤ ε)
    {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    {n : ℕ} (hn : n ∈ smoothedMIndices x q) :
    ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d x (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 8) *
            (harmonic x : ℝ) ^ 2 *
              (ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹) := by
  have hx1 : 1 ≤ x := by omega
  have hxpos : 0 < (x : ℝ) := by positivity
  have hm : q.1 * q.2 * n ≤ x :=
    smoothedMArgument_le hq hn
  have hdiv := displacement_divisors_card_le hm
  calc
    ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          (if ¬n.Coprime d then
            ArithmeticFunction.vonMangoldt n *
              primitiveAssociateMajorant d x (q.1 * q.2 * n)
          else 0) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((Int.natAbs
                (((q.1 * q.2 * n : ℕ) : ℤ) - x)).divisors.card : ℝ)) :=
      mFiveArithmetic_inner_le hx1 hε q n
    _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
        ArithmeticFunction.vonMangoldt n *
          ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (n.minFac : ℝ)⁻¹ * (harmonic x : ℝ) ^ 2 *
              ((1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
                (x : ℝ) ^ ((1 : ℝ) / 24))) := by
      gcongr
      exact mul_nonneg (by positivity)
        ArithmeticFunction.vonMangoldt_nonneg
    _ = (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 8) *
            (harmonic x : ℝ) ^ 2 *
              (ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹) := by
      have hexp :
          (1 : ℝ) / 8 = (1 : ℝ) / 12 + (1 : ℝ) / 24 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      ring

/-- Explicit version of Chen's equation (11).  The arithmetic part of `M₅`
has exponent `23/24`; the remaining factors are a fixed constant and three
harmonic/logarithmic losses. -/
theorem mFiveArithmeticMajorant_le_explicit
    {x : ℕ} {ε : ℝ} (hx : 2 ≤ x) (hε : 0 ≤ ε) :
    mFiveArithmeticMajorant x ε ≤
      9 * (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((23 : ℝ) / 24) *
            (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ) ^ 3 := by
  let A : ℝ :=
    (6 : ℝ) ^ (46656 : ℝ) *
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 8) *
          (harmonic x : ℝ) ^ 2
  let B : ℝ :=
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
      Real.log x * (harmonic x : ℝ)
  have hx1 : 1 ≤ x := by omega
  have hxpos : 0 < (x : ℝ) := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast hx1)
  have hH : 0 ≤ (harmonic x : ℝ) := by
    exact_mod_cast (show 0 ≤ harmonic x by
      rw [harmonic]
      positivity)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _))
      (sq_nonneg _)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (by positivity) hlogx)
      hH
  have hsum :
      mFiveArithmeticMajorant x ε ≤
        ((chenPairs x).card : ℝ) * A * B := by
    rw [mFiveArithmeticMajorant]
    calc
      ∑ q ∈ chenPairs x,
          ∑ n ∈ smoothedMIndices x q,
            ∑ d ∈ sieveModuli x ε,
              (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                  (3 : ℝ) ^ distinctPrimeFactors d /
                    (Nat.totient d : ℝ)) *
                (if ¬n.Coprime d then
                  ArithmeticFunction.vonMangoldt n *
                    primitiveAssociateMajorant d x (q.1 * q.2 * n)
                else 0) ≤
        ∑ q ∈ chenPairs x, A * B := by
          apply Finset.sum_le_sum
          intro q hq
          calc
            ∑ n ∈ smoothedMIndices x q,
                ∑ d ∈ sieveModuli x ε,
                  (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
                      (3 : ℝ) ^ distinctPrimeFactors d /
                        (Nat.totient d : ℝ)) *
                    (if ¬n.Coprime d then
                      ArithmeticFunction.vonMangoldt n *
                        primitiveAssociateMajorant d x
                          (q.1 * q.2 * n)
                    else 0) ≤
              ∑ n ∈ smoothedMIndices x q,
                A * (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
                    apply Finset.sum_le_sum
                    intro n hn
                    simpa only [A] using
                      mFiveArithmetic_inner_le_uniform hx hε hq hn
            _ = A * ∑ n ∈ smoothedMIndices x q,
                ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹ := by
                    rw [Finset.mul_sum]
            _ ≤ A * B := by
                    exact mul_le_mul_of_nonneg_left
                      (by
                        simpa only [B] using
                          sum_smoothedMIndices_vonMangoldt_div_minFac_le
                            hx q)
                      hA
      _ = ((chenPairs x).card : ℝ) * A * B := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  have hcard := chenPairs_card_cast_le x hx1
  calc
    mFiveArithmeticMajorant x ε ≤
        ((chenPairs x).card : ℝ) * A * B := hsum
    _ ≤ (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * A * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard hA) hB
    _ = 9 * (6 : ℝ) ^ (46656 : ℝ) *
        (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
          (x : ℝ) ^ ((23 : ℝ) / 24) *
            (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ) ^ 3 := by
      have hexp :
          (23 : ℝ) / 24 = (5 : ℝ) / 6 + (1 : ℝ) / 8 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      dsimp only [A, B]
      ring

/-- The five logarithmic factors in the explicit `M₅` estimate are
eventually absorbed by `x^(1/100)`. -/
theorem eventually_log_pow_five_le_rpow :
    ∀ᶠ n : ℕ in atTop,
      (Real.log n) ^ 5 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
  have hδ : (0 : ℝ) < 1 / 100 := by norm_num
  have hreal :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x ^ (5 : ℝ)‖ ≤
          ‖x ^ ((1 : ℝ) / 100)‖ :=
    (isLittleO_log_rpow_rpow_atTop (5 : ℝ) hδ).eventuallyLE
  have hnat :
      ∀ᶠ n : ℕ in atTop,
        ‖Real.log (n : ℝ) ^ (5 : ℝ)‖ ≤
          ‖(n : ℝ) ^ ((1 : ℝ) / 100)‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_gt_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn1)
  have hn' :
      (Real.log n) ^ 5 ≤
        |(n : ℝ) ^ ((1 : ℝ) / 100)| := by
    simpa [Real.rpow_natCast, abs_of_nonneg hlogpos.le]
      using hn
  rw [abs_of_nonneg
    (Real.rpow_nonneg hnpos.le ((1 : ℝ) / 100))] at hn'
  exact hn'

/-- The fixed positive constant left after absorbing all logarithmic losses
in equation (11). -/
noncomputable def mFivePowerConstant : ℝ :=
  72 * (6 : ℝ) ^ (46656 : ℝ) *
    (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
      ((Real.log 2)⁻¹ + 1)

theorem mFivePowerConstant_pos : 0 < mFivePowerConstant := by
  rw [mFivePowerConstant]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The three harmonic factors, the logarithm, and the ceiling in equation
(11) cost at most five powers of `log x`. -/
theorem mFive_log_loss_le
    {x : ℕ} (hlogOne : 1 ≤ Real.log (x : ℝ)) :
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
        Real.log x * (harmonic x : ℝ) ^ 3 ≤
      8 * ((Real.log 2)⁻¹ + 1) * (Real.log x) ^ 5 := by
  let L : ℝ := Real.log x
  let H : ℝ := harmonic x
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    linarith
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hHle : H ≤ 2 * L := by
    dsimp only [H, L]
    have hH := harmonic_le_one_add_log x
    linarith
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hceil :
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ K * L := by
    have hy0 : 0 ≤ L / Real.log 2 := by positivity
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) ≤ L / Real.log 2 + 1 :=
        (Nat.ceil_lt_add_one hy0).le
      _ = (Real.log 2)⁻¹ * L + 1 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (Real.log 2)⁻¹ * L + L := by
        linarith
      _ = K * L := by
        dsimp only [K]
        ring
  calc
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
        Real.log x * (harmonic x : ℝ) ^ 3 =
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ^ 3 := by rfl
    _ ≤ (K * L) * L * (2 * L) ^ 3 := by gcongr
    _ = 8 * K * L ^ 5 := by ring
    _ = 8 * ((Real.log 2)⁻¹ + 1) * (Real.log x) ^ 5 := by
      rfl

/-- Fixed-exponent form of equation (11), after absorbing its five
logarithmic factors by `x^(1/100)`. -/
theorem mFiveArithmeticMajorant_le_fixed_rpow
    {x : ℕ} {ε : ℝ} (hx : 2 ≤ x) (hε : 0 ≤ ε)
    (hlogOne : 1 ≤ Real.log (x : ℝ))
    (hlogFive :
      (Real.log x) ^ 5 ≤ (x : ℝ) ^ ((1 : ℝ) / 100)) :
    mFiveArithmeticMajorant x ε ≤
      mFivePowerConstant * (x : ℝ) ^ ((581 : ℝ) / 600) := by
  let P : ℝ :=
    9 * (6 : ℝ) ^ (46656 : ℝ) *
      (1 + 24 / Real.log 2) ^ (16777216 : ℝ) *
        (x : ℝ) ^ ((23 : ℝ) / 24)
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hxpos : 0 < (x : ℝ) := by positivity
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  calc
    mFiveArithmeticMajorant x ε ≤
        P * ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) ^ 3) := by
      simpa only [P, mul_assoc] using
        (mFiveArithmeticMajorant_le_explicit
          (x := x) (ε := ε) hx hε)
    _ ≤ P * (8 * K * (Real.log x) ^ 5) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [K] using mFive_log_loss_le hlogOne) hP0
    _ ≤ P * (8 * K *
        (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogFive
          (mul_nonneg (by norm_num) hK0)) hP0
    _ = mFivePowerConstant *
        (x : ℝ) ^ ((581 : ℝ) / 600) := by
      have hexp :
          (581 : ℝ) / 600 =
            (23 : ℝ) / 24 + (1 : ℝ) / 100 := by
        norm_num
      rw [mFivePowerConstant, hexp, Real.rpow_add hxpos]
      dsimp only [P, K]
      ring

/-- The explicit equation-(11) bound implies the `x^(1-ε/3)` saving used
in the final assembly of Lemma 5. -/
theorem eventually_mFiveArithmeticMajorant_le_rpow
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop,
      mFiveArithmeticMajorant x ε ≤
        mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [eventually_log_pow_five_le_rpow, hlogOne,
    eventually_ge_atTop 2] with x hlogFive hlogOne hx2
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  calc
    mFiveArithmeticMajorant x ε ≤
        mFivePowerConstant * (x : ℝ) ^ ((581 : ℝ) / 600) :=
      mFiveArithmeticMajorant_le_fixed_rpow
        hx2 hε0.le hlogOne hlogFive
    _ ≤ mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hxone (by linarith))
        mFivePowerConstant_pos.le

/-- `M₅` itself has the power saving required by Lemma 5. -/
theorem eventually_mFive_le_rpow
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, Even x →
      mFive x ε ≤
        mFivePowerConstant * (x : ℝ) ^ (1 - ε / 3) := by
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  filter_upwards
      [eventually_mFiveArithmeticMajorant_le_rpow hε0 hε1,
        hxlargeEventually] with x hmajor hxlarge
  intro hxeven
  exact (mFive_le_arithmeticMajorant hxeven hxlarge).trans hmajor

/-- Equations (6)–(11), with the formula-(5) smoothing error deliberately
kept separate: the smoothed sieve expansion is bounded by `M₁ + M₂` plus a
fixed power saving. -/
theorem smoothedSieveExpansion_power_bound
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      smoothedSieveExpansion x ε ≤
        mOne x ε + mTwo x ε +
          C * (x : ℝ) ^ (1 - ε / 3) := by
  obtain ⟨C₃, hC₃, hthree⟩ :=
    abs_mThree_power_bound hε0 hε1
  let C : ℝ := C₃ + mFivePowerConstant
  refine ⟨C, add_pos hC₃ mFivePowerConstant_pos, ?_⟩
  filter_upwards [hthree, eventually_mFive_le_rpow hε0 hε1,
    eventually_ge_atTop 1] with x hthree hfive hx1
  intro hxeven
  have hsmooth :=
    smoothedSieveExpansion_le hxeven hx1 hε0.le
  have hfour := mFour_le_mTwo_add_mFive x ε
  calc
    smoothedSieveExpansion x ε ≤
        mOne x ε + |mThree x ε| + mFour x ε := hsmooth
    _ ≤ mOne x ε +
        C₃ * (x : ℝ) ^ (1 - ε / 3) +
          (mTwo x ε + mFive x ε) := by
      gcongr
      exact hthree hxeven
    _ ≤ mOne x ε +
        C₃ * (x : ℝ) ^ (1 - ε / 3) +
          (mTwo x ε +
            mFivePowerConstant *
              (x : ℝ) ^ (1 - ε / 3)) := by
      gcongr
      exact hfive hxeven
    _ = mOne x ε + mTwo x ε +
        C * (x : ℝ) ^ (1 - ε / 3) := by
      dsimp only [C]
      ring

end Chen
