import ChenTheorem.Lemma7.SingularSeries

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-!
# Lemma 7: lower bounds for the normalizing sum

This file formalizes the elementary `V_k` argument following equation (22).
-/

/-- The finite sum denoted by `V_k(X)` in the proof of Lemma 7. -/
noncomputable def totientSquarefreeMass (k X : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n.Coprime k),
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 /
      (Nat.totient n : ℝ)

theorem totient_cast_eq_mul_primeFactors (n : ℕ) :
    (Nat.totient n : ℝ) =
      (n : ℝ) *
        ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
  have h := Nat.totient_eq_mul_prod_factors n
  have hR := congrArg (fun q : ℚ => (q : ℝ)) h
  norm_num at hR
  exact hR

theorem prod_prime_div_sub_one_eq_nat_div_totient
    {n : ℕ} (hn : 0 < n) :
    ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) =
      (n : ℝ) / Nat.totient n := by
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  rw [totient_cast_eq_mul_primeFactors]
  have hprod :
      ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [sub_ne_zero]
    exact Ne.symm (ne_of_lt ((inv_lt_one₀ (by positivity)).mpr hpR))
  have hlocalprod :
      ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) =
        1 / ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    calc
      _ = ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹)⁻¹ := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp0 : (p : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        have hp1 : (p : ℝ) - 1 ≠ 0 := by
          exact ne_of_gt (sub_pos.mpr (by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt))
        field_simp [hp0, hp1]
      _ = (∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹))⁻¹ := by
        rw [Finset.prod_inv_distrib]
      _ = _ := by rw [one_div]
  field_simp
  simpa only [one_div] using hlocalprod

/-- Euler's local identity
`∑_{d ∣ n} μ(d)² / φ(d) = n / φ(n)`. -/
theorem sum_divisors_moebius_sq_div_totient
    {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 /
          (Nat.totient d : ℝ) =
      (n : ℝ) / Nat.totient n := by
  have hrestrict :
      (∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 /
            (Nat.totient d : ℝ)) =
        ∑ d ∈ n.divisors.filter Squarefree,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 /
            (Nat.totient d : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hdf
    have hnot : ¬Squarefree d := by
      intro hsq
      exact hdf (Finset.mem_filter.mpr ⟨hd, hsq⟩)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
    simp
  rw [hrestrict, Nat.sum_divisors_filter_squarefree hn.ne']
  simp only [Nat.factors_eq]
  simp_rw [Finset.prod_val]
  have hterm :
      ∀ u ∈ n.primeFactors.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ u, p) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (∏ p ∈ u, p) : ℝ) =
          ∏ p ∈ u, (((p : ℝ) - 1)⁻¹) := by
    intro u hu
    have husub : u ⊆ n.primeFactors := Finset.mem_powerset.mp hu
    have huprime : ∀ p ∈ u, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (husub hp)
    have husq : Squarefree (∏ p ∈ u, p) :=
      Finset.squarefree_prod_of_pairwise_isCoprime
        (fun p hp q hq hpq => by
          change IsRelPrime p q
          rw [← Nat.coprime_iff_isRelPrime]
          exact (Nat.coprime_primes (huprime p hp) (huprime q hq)).2 hpq)
        (fun p hp => (huprime p hp).squarefree)
    have hμ :
        (((ArithmeticFunction.moebius (∏ p ∈ u, p) : ℤ) : ℝ) ^ 2) = 1 := by
      norm_cast
      exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree husq
    rw [hμ]
    rw [one_div, totient_cast_eq_prod_sub_one_of_squarefree husq,
      Nat.primeFactors_prod huprime, Finset.prod_inv_distrib]
  calc
    (∑ u ∈ n.primeFactorsList.toFinset.powerset,
        ((ArithmeticFunction.moebius (∏ p ∈ u, p) : ℤ) : ℝ) ^ 2 /
          (Nat.totient (∏ p ∈ u, p) : ℝ)) =
      ∑ u ∈ n.primeFactors.powerset,
        ∏ p ∈ u, (((p : ℝ) - 1)⁻¹) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ∏ p ∈ n.primeFactors,
        (1 + ((p : ℝ) - 1)⁻¹) := by
      rw [Finset.prod_one_add]
    _ = ∏ p ∈ n.primeFactors,
        (p : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hp1 : (p : ℝ) - 1 ≠ 0 := by
        exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hpprime.one_lt))
      field_simp
      ring
    _ = (n : ℝ) / Nat.totient n :=
      prod_prime_div_sub_one_eq_nat_div_totient hn

theorem totientSquarefreeMass_one_eq (X : ℕ) :
    totientSquarefreeMass 1 X =
      ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
        ((Nat.totient n : ℝ))⁻¹ := by
  unfold totientSquarefreeMass
  simp only [Nat.coprime_one_right_iff, Finset.filter_true]
  let A := Finset.Icc 1 X
  let B := A.filter Squarefree
  change (∑ n ∈ A,
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 /
        (Nat.totient n : ℝ)) =
    ∑ n ∈ B, ((Nat.totient n : ℝ))⁻¹
  calc
    (∑ n ∈ A,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 /
          (Nat.totient n : ℝ)) =
      ∑ n ∈ B,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 /
          (Nat.totient n : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hnA hnB
      have hnonsq : ¬Squarefree n := by
        intro hsq
        exact hnB (Finset.mem_filter.mpr ⟨hnA, hsq⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnonsq]
      norm_num
    _ = ∑ n ∈ B, ((Nat.totient n : ℝ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hsq := (Finset.mem_filter.mp hn).2
      have hμ : (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2) = 1 := by
        norm_cast
        exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      rw [hμ]
      norm_num

/-- The comparison `V₁(X) ≤ (k/φ(k)) V_k(X)` in the paper. -/
theorem totientSquarefreeMass_one_le
    {k X : ℕ} (hk : 0 < k) :
    totientSquarefreeMass 1 X ≤
      ((k : ℝ) / Nat.totient k) * totientSquarefreeMass k X := by
  let S := (Finset.Icc 1 X).filter Squarefree
  let D := k.divisors
  let B := (Finset.Icc 1 X).filter (fun n => n.Coprime k)
  let f : ℕ → ℕ × ℕ := fun n => (n.gcd k, n / n.gcd k)
  have hfprod (n : ℕ) : (f n).1 * (f n).2 = n := by
    dsimp only [f]
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n k)]
  have hfinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b := by
    intro a ha b hb hab
    have hprod := congrArg (fun z : ℕ × ℕ => z.1 * z.2) hab
    simpa only [hfprod] using hprod
  have hfmem : S.image f ⊆ D ×ˢ B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnS, rfl⟩
    have hn := Finset.mem_filter.mp hnS
    have hnIcc := Finset.mem_Icc.mp hn.1
    have hnsq := hn.2
    have hgpos : 0 < n.gcd k :=
      Nat.gcd_pos_of_pos_right n hk
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n k, hk.ne'⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        exact ⟨Nat.div_pos (Nat.gcd_le_left k (by omega)) hgpos,
          (Nat.div_le_self n _).trans hnIcc.2⟩
      · exact Nat.coprime_div_gcd_of_squarefree hnsq hk.ne'
  have hterm (n : ℕ) (hnS : n ∈ S) :
      ((Nat.totient n : ℝ))⁻¹ =
        (((ArithmeticFunction.moebius (f n).1 : ℤ) : ℝ) ^ 2 /
            (Nat.totient (f n).1 : ℝ)) *
          (((ArithmeticFunction.moebius (f n).2 : ℤ) : ℝ) ^ 2 /
            (Nat.totient (f n).2 : ℝ)) := by
    have hn := Finset.mem_filter.mp hnS
    have hnsq := hn.2
    have hdsq : Squarefree (f n).1 :=
      hnsq.squarefree_of_dvd (Nat.gcd_dvd_left n k)
    have hmsq : Squarefree (f n).2 :=
      hnsq.squarefree_of_dvd (Nat.div_dvd_of_dvd
        (Nat.gcd_dvd_left n k))
    have hcop : (f n).1.Coprime (f n).2 := by
      have hmK : (f n).2.Coprime k := by
        simpa only [f] using Nat.coprime_div_gcd_of_squarefree hnsq hk.ne'
      exact (Nat.Coprime.of_dvd_right (Nat.gcd_dvd_right n k) hmK).symm
    have hdpos : 0 < (f n).1 := Nat.gcd_pos_of_pos_right n hk
    have hmpos : 0 < (f n).2 := by
      dsimp only [f]
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn.1).1
      exact Nat.div_pos (Nat.gcd_le_left k hnpos) hdpos
    have hdμ : (((ArithmeticFunction.moebius (f n).1 : ℤ) : ℝ) ^ 2) = 1 := by
      norm_cast
      exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq
    have hmμ : (((ArithmeticFunction.moebius (f n).2 : ℤ) : ℝ) ^ 2) = 1 := by
      norm_cast
      exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hmsq
    rw [hdμ, hmμ]
    have htotNat : n.totient = (f n).1.totient * (f n).2.totient := by
      calc
        n.totient = ((f n).1 * (f n).2).totient :=
          congrArg Nat.totient (hfprod n).symm
        _ = _ := Nat.totient_mul hcop
    have htot : (Nat.totient n : ℝ) =
        (Nat.totient (f n).1 : ℝ) * (Nat.totient (f n).2 : ℝ) := by
      exact_mod_cast htotNat
    rw [htot]
    ring
  have himage :
      (∑ z ∈ S.image f,
        (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
            (Nat.totient z.1 : ℝ)) *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (Nat.totient z.2 : ℝ))) =
        ∑ n ∈ S, ((Nat.totient n : ℝ))⁻¹ := by
    rw [Finset.sum_image hfinj]
    apply Finset.sum_congr rfl
    intro n hn
    exact (hterm n hn).symm
  have hsubset :
      (∑ z ∈ S.image f,
        (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
            (Nat.totient z.1 : ℝ)) *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (Nat.totient z.2 : ℝ))) ≤
        ∑ z ∈ D ×ˢ B,
          (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.1 : ℝ)) *
            (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.2 : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hfmem
    intro z hz hznot
    have hz' := Finset.mem_product.mp hz
    have hdpos : 0 < z.1 := Nat.pos_of_mem_divisors hz'.1
    have hmpos : 0 < z.2 := (Finset.mem_Icc.mp
      (Finset.mem_filter.mp hz'.2).1).1
    positivity
  have hproduct :
      (∑ z ∈ D ×ˢ B,
          (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.1 : ℝ)) *
            (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.2 : ℝ))) =
        (∑ d ∈ D,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 /
            (Nat.totient d : ℝ)) *
          ∑ m ∈ B,
            ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 /
              (Nat.totient m : ℝ) := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
  rw [totientSquarefreeMass_one_eq]
  change (∑ n ∈ S, ((Nat.totient n : ℝ))⁻¹) ≤
    ((k : ℝ) / Nat.totient k) *
      ∑ m ∈ B,
        ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 /
          (Nat.totient m : ℝ)
  calc
    (∑ n ∈ S, ((Nat.totient n : ℝ))⁻¹) =
        ∑ z ∈ S.image f,
          (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.1 : ℝ)) *
            (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.2 : ℝ)) := himage.symm
    _ ≤ ∑ z ∈ D ×ˢ B,
          (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.1 : ℝ)) *
            (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
              (Nat.totient z.2 : ℝ)) := hsubset
    _ = (∑ d ∈ D,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 /
            (Nat.totient d : ℝ)) *
          ∑ m ∈ B,
            ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 /
              (Nat.totient m : ℝ) := hproduct
    _ = ((k : ℝ) / Nat.totient k) *
          ∑ m ∈ B,
            ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 /
              (Nat.totient m : ℝ) := by
      rw [show D = k.divisors by rfl,
        sum_divisors_moebius_sq_div_totient hk]

theorem sum_inv_divisors_eq_sigma_div
    {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, ((d : ℝ))⁻¹ =
      (ArithmeticFunction.sigma 1 n : ℝ) / n := by
  calc
    (∑ d ∈ n.divisors, ((d : ℝ))⁻¹) =
      ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) / n := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdpos : (0 : ℝ) < d := by
        exact_mod_cast Nat.pos_of_mem_divisors hd
      have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_div hdn hd0]
      change (d : ℝ)⁻¹ = ((n : ℝ) * (d : ℝ)⁻¹) * (n : ℝ)⁻¹
      calc
        (d : ℝ)⁻¹ = (d : ℝ)⁻¹ * 1 := (mul_one _).symm
        _ = (d : ℝ)⁻¹ * ((n : ℝ) * (n : ℝ)⁻¹) := by
          rw [mul_inv_cancel₀ hn0]
        _ = ((n : ℝ) * (d : ℝ)⁻¹) * (n : ℝ)⁻¹ := by ring
    _ = (∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ)) / n := by
      rw [Finset.sum_div]
    _ = (∑ d ∈ n.divisors, (d : ℝ)) / n := by
      rw [Nat.sum_div_divisors]
    _ = (ArithmeticFunction.sigma 1 n : ℝ) / n := by
      norm_num [ArithmeticFunction.sigma_apply]

theorem sum_inv_divisors_pow_squarefree_le
    {d Y : ℕ} (hd : Squarefree d) :
    ∑ m ∈ (d ^ Y).divisors, ((m : ℝ))⁻¹ ≤
      (d : ℝ) / Nat.totient d := by
  by_cases hY : Y = 0
  · subst Y
    simp only [pow_zero, Nat.divisors_one, Finset.sum_singleton,
      Nat.cast_one, inv_one]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
    have hφle : Nat.totient d ≤ d := Nat.totient_le d
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < Nat.totient d)).2
      (by norm_num; exact_mod_cast hφle)
  have hYpos : 0 < Y := Nat.pos_of_ne_zero hY
  have hpowpos : 0 < d ^ Y := pow_pos (Nat.pos_of_ne_zero hd.ne_zero) _
  rw [sum_inv_divisors_eq_sigma_div hpowpos,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      hpowpos.ne']
  rw [Nat.primeFactors_pow d hY]
  have hfac : ∀ p ∈ d.primeFactors,
      (Y • d.factorization) p = Y := by
    intro p hp
    simp [Nat.factorization_eq_one_of_squarefree hd
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
  have hfacPow : ∀ p ∈ d.primeFactors,
      (d ^ Y).factorization p = Y := by
    intro p hp
    rw [Nat.factorization_pow]
    exact hfac p hp
  have hprodRange :
      (∏ p ∈ d.primeFactors,
          ∑ i ∈ Finset.range ((d ^ Y).factorization p + 1), p ^ (i * 1)) =
        ∏ p ∈ d.primeFactors,
          ∑ i ∈ Finset.range (Y + 1), p ^ (i * 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [hfacPow p hp]
  rw [hprodRange]
  have hdcast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    calc
      (d : ℝ) = ((∏ p ∈ d.primeFactors, p : ℕ) : ℝ) := by
        exact_mod_cast (Nat.prod_primeFactors_of_squarefree hd).symm
      _ = ∏ p ∈ d.primeFactors, (p : ℝ) := by
        rw [Nat.cast_prod]
  have hdenProd : (d : ℝ) ^ Y =
      ∏ p ∈ d.primeFactors, (p : ℝ) ^ Y := by
    rw [hdcast, Finset.prod_pow]
  push_cast
  rw [hdenProd, ← Finset.prod_div_distrib]
  calc
    (∏ p ∈ d.primeFactors,
        (∑ i ∈ Finset.range (Y + 1), (p : ℝ) ^ (i * 1)) /
          (p : ℝ) ^ Y) ≤
      ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpprime := Nat.prime_of_mem_primeFactors hp
        have hpR : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
        norm_num only [mul_one]
        rw [Finset.sum_div]
        have hgeom := geom_sum_mul (x := ((p : ℝ))⁻¹) Y
        have hinv : 0 ≤ ((p : ℝ))⁻¹ := by positivity
        have hsum :
            ∑ i ∈ Finset.range (Y + 1), ((p : ℝ)) ^ i /
                ((p : ℝ)) ^ Y =
              ∑ j ∈ Finset.range (Y + 1), (((p : ℝ))⁻¹) ^ j := by
          rw [Finset.sum_bij (fun i _ => Y - i)]
          · intro i hi
            simp only [Finset.mem_range] at hi ⊢
            omega
          · intro i hi j hj hij
            simp only [Finset.mem_range] at hi hj
            omega
          · intro j hj
            have hjY : j ≤ Y := by
              simp only [Finset.mem_range] at hj
              omega
            refine ⟨Y - j, ?_, ?_⟩
            · simp only [Finset.mem_range]
              omega
            · exact Nat.sub_sub_self hjY
          · intro i hi
            have hiY : i ≤ Y := by
              simp only [Finset.mem_range] at hi
              omega
            have hp0 : (p : ℝ) ≠ 0 := by positivity
            have hpi0 : (p : ℝ) ^ i ≠ 0 := pow_ne_zero _ hp0
            have hprest0 : (p : ℝ) ^ (Y - i) ≠ 0 := pow_ne_zero _ hp0
            rw [inv_pow]
            conv_lhs => rw [show Y = i + (Y - i) by omega, pow_add]
            field_simp [hpi0, hprest0]
        have hfinite :
            ∑ j ∈ Finset.range (Y + 1), (((p : ℝ))⁻¹) ^ j ≤
              (1 - ((p : ℝ))⁻¹)⁻¹ := by
          have hrlt : (p : ℝ)⁻¹ < 1 :=
            (inv_lt_one₀ (by positivity)).mpr hpR
          have hrne : (p : ℝ)⁻¹ ≠ 1 := ne_of_lt hrlt
          rw [geom_sum_eq hrne]
          have hbase : 0 ≤ (((p : ℝ))⁻¹) ^ (Y + 1) := by positivity
          have hden : 0 < 1 - ((p : ℝ))⁻¹ := sub_pos.mpr
            hrlt
          have heq :
              ((((p : ℝ))⁻¹) ^ (Y + 1) - 1) /
                  (((p : ℝ))⁻¹ - 1) =
                (1 - (((p : ℝ))⁻¹) ^ (Y + 1)) /
                  (1 - ((p : ℝ))⁻¹) := by
            have hnum : (((p : ℝ))⁻¹) ^ (Y + 1) - 1 =
                -(1 - (((p : ℝ))⁻¹) ^ (Y + 1)) := by ring
            have hden' : ((p : ℝ))⁻¹ - 1 =
                -(1 - ((p : ℝ))⁻¹) := by ring
            rw [hnum, hden', neg_div_neg_eq]
          rw [heq]
          apply (div_le_iff₀ hden).2
          rw [inv_mul_cancel₀ hden.ne']
          linarith
        calc
          _ = ∑ j ∈ Finset.range (Y + 1), (((p : ℝ))⁻¹) ^ j := hsum
          _ ≤ (1 - ((p : ℝ))⁻¹)⁻¹ := hfinite
          _ = (p : ℝ) / ((p : ℝ) - 1) := by
            field_simp
    _ = (d : ℝ) / Nat.totient d :=
      prod_prime_div_sub_one_eq_nat_div_totient
        (Nat.pos_of_ne_zero hd.ne_zero)

theorem sum_inv_divisors_pow_filter_multiple_le
    {d Y : ℕ} (hd : Squarefree d) :
    ∑ m ∈ (d ^ Y).divisors.filter (d ∣ ·), ((m : ℝ))⁻¹ ≤
      ((Nat.totient d : ℝ))⁻¹ := by
  let A := (d ^ Y).divisors.filter (d ∣ ·)
  let I := A.image (fun m => m / d)
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hinj : Set.InjOn (fun m => m / d) A := by
    intro a ha b hb hab
    have hda : d ∣ a := (Finset.mem_filter.mp ha).2
    have hdb : d ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = a / d * d := (Nat.div_mul_cancel hda).symm
      _ = b / d * d := congrArg (· * d) hab
      _ = b := Nat.div_mul_cancel hdb
  have hI : I ⊆ (d ^ Y).divisors := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨m, hm, rfl⟩
    have hm' := Finset.mem_filter.mp hm
    have hmpow : m ∣ d ^ Y := Nat.dvd_of_mem_divisors hm'.1
    exact Nat.mem_divisors.mpr
      ⟨(Nat.div_dvd_of_dvd hm'.2).trans hmpow,
        pow_ne_zero _ hd.ne_zero⟩
  have heq :
      (∑ m ∈ A, ((m : ℝ))⁻¹) =
        (d : ℝ)⁻¹ * ∑ t ∈ I, ((t : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    calc
      (∑ m ∈ A, ((m : ℝ))⁻¹) =
        ∑ t ∈ I, (((d * t : ℕ) : ℝ))⁻¹ := by
          rw [Finset.sum_image hinj]
          apply Finset.sum_congr rfl
          intro m hm
          have hdm : d ∣ m := (Finset.mem_filter.mp hm).2
          rw [Nat.mul_div_cancel' hdm]
      _ = ∑ t ∈ I, (d : ℝ)⁻¹ * (t : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Nat.cast_mul, mul_inv]
      _ = _ := rfl
  rw [show (d ^ Y).divisors.filter (d ∣ ·) = A by rfl, heq]
  calc
    (d : ℝ)⁻¹ * ∑ t ∈ I, ((t : ℝ))⁻¹ ≤
      (d : ℝ)⁻¹ * ∑ t ∈ (d ^ Y).divisors, ((t : ℝ))⁻¹ := by
        gcongr
    _ ≤ (d : ℝ)⁻¹ * ((d : ℝ) / Nat.totient d) := by
      gcongr
      exact sum_inv_divisors_pow_squarefree_le hd
    _ = ((Nat.totient d : ℝ))⁻¹ := by
      have hdR : (d : ℝ) ≠ 0 := by positivity
      field_simp

/-- The squarefree kernel `∏_{p∣n} p`. -/
def natRadical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem natRadical_squarefree (n : ℕ) : Squarefree (natRadical n) := by
  unfold natRadical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

theorem natRadical_dvd (n : ℕ) : natRadical n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

theorem dvd_natRadical_pow_self {n : ℕ} (hn : n ≠ 0) :
    n ∣ natRadical n ^ n := by
  exact Nat.dvd_prod_primeFactors_pow_self hn

theorem dvd_natRadical_pow_of_le
    {n X : ℕ} (hn : 0 < n) (hnX : n ≤ X) :
    n ∣ natRadical n ^ X := by
  exact (dvd_natRadical_pow_self hn.ne').trans
    (pow_dvd_pow _ hnX)

/-- The inequality `∑_{n≤X} 1/n ≤ V₁(X)` used in Lemma 7.  The map
`n ↦ (rad n, n)` places each integer in the Euler-geometric fiber of its
squarefree kernel. -/
theorem harmonic_sum_le_totientSquarefreeMass_one
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, ((n : ℝ))⁻¹) ≤
      totientSquarefreeMass 1 X := by
  let H := Finset.Icc 1 X
  let D := H.filter Squarefree
  let T := (D ×ˢ Finset.range (X ^ X + 1)).filter fun z : ℕ × ℕ =>
    z.2 ∈ (z.1 ^ X).divisors ∧ z.1 ∣ z.2
  let f : ℕ → ℕ × ℕ := fun n => (natRadical n, n)
  have hfinj : Set.InjOn f H := by
    intro a ha b hb hab
    exact congrArg Prod.snd hab
  have hfmem : H.image f ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnH, rfl⟩
    have hn := Finset.mem_Icc.mp hnH
    have hradDvd : natRadical n ∣ n := natRadical_dvd n
    have hradPos : 0 < natRadical n :=
      Nat.pos_of_dvd_of_pos hradDvd (by omega)
    have hradLe : natRadical n ≤ X :=
      (Nat.le_of_dvd (by omega) hradDvd).trans hn.2
    have hXPow : X ≤ X ^ X := le_self_pow hX (by omega)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hn.2.trans hXPow))⟩,
      Nat.mem_divisors.mpr ⟨dvd_natRadical_pow_of_le hn.1 hn.2,
        pow_ne_zero _ hradPos.ne'⟩,
      hradDvd⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hradPos, hradLe⟩,
        natRadical_squarefree n⟩
  have himage :
      (∑ z ∈ H.image f, ((z.2 : ℝ))⁻¹) =
        ∑ n ∈ H, ((n : ℝ))⁻¹ := by
    rw [Finset.sum_image hfinj]
  have hsubset :
      (∑ z ∈ H.image f, ((z.2 : ℝ))⁻¹) ≤
        ∑ z ∈ T, ((z.2 : ℝ))⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hfmem
      (fun z hzT hzI => by positivity)
  have hfiber (d : ℕ) (hdD : d ∈ D) :
      (Finset.range (X ^ X + 1)).filter
          (fun m => m ∈ (d ^ X).divisors ∧ d ∣ m) =
        (d ^ X).divisors.filter (d ∣ ·) := by
    have hd := Finset.mem_filter.mp hdD
    have hdX := Finset.mem_Icc.mp hd.1
    ext m
    constructor
    · intro hm
      have hm' := Finset.mem_filter.mp hm
      exact Finset.mem_filter.mpr ⟨hm'.2.1, hm'.2.2⟩
    · intro hm
      have hm' := Finset.mem_filter.mp hm
      have hmle : m ≤ d ^ X := Nat.le_of_dvd
        (pow_pos (by omega) _) (Nat.dvd_of_mem_divisors hm'.1)
      have hpowle : d ^ X ≤ X ^ X := Nat.pow_le_pow_left hdX.2 _
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hm'.1, hm'.2⟩
  have htarget :
      (∑ z ∈ T, ((z.2 : ℝ))⁻¹) ≤
        ∑ d ∈ D, ((Nat.totient d : ℝ))⁻¹ := by
    unfold T
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_le_sum
    intro d hdD
    have hrewrite :
        (∑ m ∈ Finset.range (X ^ X + 1),
          if m ∈ (d ^ X).divisors ∧ d ∣ m then ((m : ℝ))⁻¹ else 0) =
          ∑ m ∈ (d ^ X).divisors.filter (d ∣ ·), ((m : ℝ))⁻¹ := by
      rw [← hfiber d hdD, Finset.sum_filter]
    rw [hrewrite]
    exact sum_inv_divisors_pow_filter_multiple_le
      (Finset.mem_filter.mp hdD).2
  rw [totientSquarefreeMass_one_eq]
  change (∑ n ∈ H, ((n : ℝ))⁻¹) ≤
    ∑ d ∈ D, ((Nat.totient d : ℝ))⁻¹
  calc
    (∑ n ∈ H, ((n : ℝ))⁻¹) =
        ∑ z ∈ H.image f, ((z.2 : ℝ))⁻¹ := himage.symm
    _ ≤ ∑ z ∈ T, ((z.2 : ℝ))⁻¹ := hsubset
    _ ≤ ∑ d ∈ D, ((Nat.totient d : ℝ))⁻¹ := htarget

theorem log_le_totientSquarefreeMass_one
    {X : ℕ} (hX : 1 ≤ X) :
    Real.log X ≤ totientSquarefreeMass 1 X := by
  calc
    Real.log X ≤ Real.log (X + 1) :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by exact_mod_cast (Nat.le_succ X))
    _ ≤ (harmonic X : ℝ) := by exact_mod_cast log_add_one_le_harmonic X
    _ = ∑ n ∈ Finset.Icc 1 X, ((n : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
    _ ≤ totientSquarefreeMass 1 X :=
      harmonic_sum_le_totientSquarefreeMass_one hX

/-- The lower bound `V_k(X) ≥ φ(k) log X / k`. -/
theorem totient_mul_log_div_le_totientSquarefreeMass
    {k X : ℕ} (hk : 0 < k) (hX : 1 ≤ X) :
    (Nat.totient k : ℝ) * Real.log X / k ≤
      totientSquarefreeMass k X := by
  have hφ : (0 : ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.mpr hk
  have hkR : (0 : ℝ) < k := by positivity
  have h := (log_le_totientSquarefreeMass_one hX).trans
    (totientSquarefreeMass_one_le hk)
  calc
    (Nat.totient k : ℝ) * Real.log X / k =
      ((Nat.totient k : ℝ) / k) * Real.log X := by ring
    _ ≤ ((Nat.totient k : ℝ) / k) *
        (((k : ℝ) / Nat.totient k) *
          totientSquarefreeMass k X) := by
      gcongr
    _ = totientSquarefreeMass k X := by
      field_simp

/-- Local divisor convolution behind the second displayed expansion of `S`
in Lemma 7. -/
theorem inv_fW_eq_sum_divisors_totient_convolution
    {k : ℕ} (hksq : Squarefree k) (hkodd : Odd k) :
    (fW k)⁻¹ =
      ∑ q ∈ k.divisors,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          (((ArithmeticFunction.moebius (k / q) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (k / q) : ℝ)) := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero hksq.ne_zero
  have hkφ : (Nat.totient k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hkpos).ne'
  symm
  calc
    (∑ q ∈ k.divisors,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          (((ArithmeticFunction.moebius (k / q) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (k / q) : ℝ))) =
      ∑ q ∈ k.divisors,
        (Nat.totient k : ℝ)⁻¹ * (fW q)⁻¹ := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqdiv : q ∣ k := Nat.dvd_of_mem_divisors hq
      have hqsq := hksq.squarefree_of_dvd hqdiv
      have hrsq := hksq.squarefree_of_dvd (Nat.div_dvd_of_dvd hqdiv)
      have hqodd := hkodd.of_dvd_nat hqdiv
      have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
      have hrpos : 0 < k / q := Nat.div_pos
        (Nat.le_of_dvd hkpos hqdiv) hqpos
      have hgd : k.gcd q = q := Nat.gcd_eq_right_iff_dvd.mpr hqdiv
      have hcop : q.Coprime (k / q) := by
        have hc : (k / q).Coprime q := by
          simpa [hgd] using
            (Nat.coprime_div_gcd_of_squarefree hksq hqpos.ne')
        exact hc.symm
      have hqμ : (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) = 1 := by
        norm_cast
        exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hqsq
      have hrμ : (((ArithmeticFunction.moebius (k / q) : ℤ) : ℝ) ^ 2) = 1 := by
        norm_cast
        exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hrsq
      rw [hqμ, hrμ]
      have hφmul : Nat.totient k =
          Nat.totient q * Nat.totient (k / q) := by
        rw [← Nat.totient_mul hcop, Nat.mul_div_cancel' hqdiv]
      rw [hφmul]
      push_cast
      have hfq : fW q ≠ 0 := (fW_pos_of_odd hqpos hqodd).ne'
      have hqφ : (Nat.totient q : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hqpos).ne'
      have hrφ : (Nat.totient (k / q) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hrpos).ne'
      field_simp
    _ = (Nat.totient k : ℝ)⁻¹ *
        ∑ q ∈ k.divisors, (fW q)⁻¹ := by
      rw [Finset.mul_sum]
    _ = (Nat.totient k : ℝ)⁻¹ *
        ((Nat.totient k : ℝ) / fW k) := by
      rw [sum_divisors_inv_fW_eq_totient_div hksq hkodd]
    _ = (fW k)⁻¹ := by
      have hfk : fW k ≠ 0 :=
        (fW_pos_of_odd hkpos hkodd).ne'
      field_simp

/-- The `V_{qx}`-type inner sum with Chen's real cutoff `R/q`. -/
noncomputable def totientSieveNumerator
    (x : ℕ) (ε : ℝ) (q : ℕ) : ℝ :=
  ∑ r ∈ sieveNumeratorIndices x ε q,
    ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 /
      (Nat.totient r : ℝ)

theorem totientSieveNumerator_eq_sum_squarefree
    (x q : ℕ) (ε : ℝ) :
    totientSieveNumerator x ε q =
      ∑ r ∈ (sieveNumeratorIndices x ε q).filter Squarefree,
        ((Nat.totient r : ℝ))⁻¹ := by
  unfold totientSieveNumerator
  let A := sieveNumeratorIndices x ε q
  let B := A.filter Squarefree
  calc
    (∑ r ∈ A,
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 /
          (Nat.totient r : ℝ)) =
      ∑ r ∈ B,
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 /
          (Nat.totient r : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r hrA hrB
      have hnonsq : ¬Squarefree r := by
        intro hsq
        exact hrB (Finset.mem_filter.mpr ⟨hrA, hsq⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnonsq]
      norm_num
    _ = ∑ r ∈ B, ((Nat.totient r : ℝ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hμ : (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2) = 1 := by
        norm_cast
        exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (Finset.mem_filter.mp hr).2
      rw [hμ]
      norm_num

noncomputable def sieveNormConvolutionSource
    (x : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  ((sieveNormIndices x ε).filter Squarefree ×ˢ Finset.range (x + 1)).filter
    fun z => z.2 ∈ z.1.divisors

noncomputable def sieveNormConvolutionTarget
    (x : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  ((sieveNormIndices x ε).filter Squarefree ×ˢ Finset.range (x + 1)).filter
    fun z => z.2 ∈ (sieveNumeratorIndices x ε z.1).filter Squarefree

/-- Reindex `(k,q)` by `(q,k/q)` in the divisor expansion of `1/f(k)`. -/
theorem sum_sieveNormConvolutionSource_eq_target
    {x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε) :
    (∑ z ∈ sieveNormConvolutionSource x ε,
        (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (fW z.2 * (Nat.totient z.2 : ℝ))) *
          (((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (z.1 / z.2) : ℝ))) =
      ∑ z ∈ sieveNormConvolutionTarget x ε,
        (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
            (fW z.1 * (Nat.totient z.1 : ℝ))) *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (Nat.totient z.2 : ℝ)) := by
  refine Finset.sum_bij (fun z _ => (z.2, z.1 / z.2)) ?_ ?_ ?_ ?_
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzprod := Finset.mem_product.mp hz'.1
    have hksq := (Finset.mem_filter.mp hzprod.1).2
    have hqdiv : z.2 ∣ z.1 := Nat.dvd_of_mem_divisors hz'.2
    have hqS := mem_sieveNormIndices_of_dvd
      (Finset.mem_filter.mp hzprod.1).1 hqdiv
    have hrN := div_mem_sieveNumeratorIndices_of_squarefree
      hksq (Finset.mem_filter.mp hzprod.1).1 hqdiv
    have hqsq := hksq.squarefree_of_dvd hqdiv
    have hrsq := hksq.squarefree_of_dvd (Nat.div_dvd_of_dvd hqdiv)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hqS, hqsq⟩, ?_⟩, ?_⟩
    · have hrN' := hrN
      simp only [sieveNumeratorIndices, Finset.mem_filter,
        Finset.mem_range] at hrN'
      exact Finset.mem_range.mpr hrN'.1
    · exact Finset.mem_filter.mpr ⟨hrN, hrsq⟩
  · intro a ha b hb hab
    have hq : a.2 = b.2 := congrArg Prod.fst hab
    have hr : a.1 / a.2 = b.1 / b.2 := congrArg Prod.snd hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hda : a.2 ∣ a.1 := Nat.dvd_of_mem_divisors ha'.2
    have hdb : b.2 ∣ b.1 := Nat.dvd_of_mem_divisors hb'.2
    have hr' : a.1 / b.2 = b.1 / b.2 := by simpa [hq] using hr
    apply Prod.ext
    · calc
        a.1 = a.2 * (a.1 / a.2) := (Nat.mul_div_cancel' hda).symm
        _ = b.2 * (a.1 / b.2) := by rw [hq]
        _ = b.2 * (b.1 / b.2) := by rw [hr']
        _ = b.1 := Nat.mul_div_cancel' hdb
    · exact hq
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyprod := Finset.mem_product.mp hy'.1
    have hqS := (Finset.mem_filter.mp hyprod.1).1
    have hqsq := (Finset.mem_filter.mp hyprod.1).2
    have hrN := (Finset.mem_filter.mp hy'.2).1
    have hrsq := (Finset.mem_filter.mp hy'.2).2
    have hkS := mul_mem_sieveNormIndices_of_mem_numerator
      hx1 hε0 hqS hrN
    have hrN' := hrN
    simp only [sieveNumeratorIndices, Finset.mem_filter,
      Finset.mem_range] at hrN'
    have hcop : y.1.Coprime y.2 :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left y.1 x) hrN'.2.2.2).symm
    have hksq : Squarefree (y.1 * y.2) :=
      Nat.squarefree_mul_iff.mpr ⟨hcop, hqsq, hrsq⟩
    let z : ℕ × ℕ := (y.1 * y.2, y.1)
    refine ⟨z, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hkS, hksq⟩, ?_⟩, ?_⟩
      · have hqS' := hqS
        simp only [sieveNormIndices, Finset.mem_filter,
          Finset.mem_range] at hqS'
        exact Finset.mem_range.mpr hqS'.1
      · exact Nat.mem_divisors.mpr
          ⟨dvd_mul_right y.1 y.2,
            Nat.mul_ne_zero hqsq.ne_zero hrsq.ne_zero⟩
    · dsimp only [z]
      apply Prod.ext
      · rfl
      · rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hqsq.ne_zero)]
  · intro z hz
    rfl

theorem sieveNorm_eq_sum_convolutionSource
    {x : ℕ} {ε : ℝ} (hx : Even x) :
    sieveNorm x ε =
      ∑ z ∈ sieveNormConvolutionSource x ε,
        (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (fW z.2 * (Nat.totient z.2 : ℝ))) *
          (((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (z.1 / z.2) : ℝ)) := by
  let S := sieveNormIndices x ε
  let Q := S.filter Squarefree
  have hrestrict :
      sieveNorm x ε =
        ∑ k ∈ Q,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k := by
    rw [sieveNorm]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hkS hkQ
    have hnonsq : ¬Squarefree k := by
      intro hsq
      exact hkQ (Finset.mem_filter.mpr ⟨hkS, hsq⟩)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnonsq]
    norm_num
  rw [hrestrict]
  calc
    (∑ k ∈ Q,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k) =
      ∑ k ∈ Q, ∑ q ∈ k.divisors,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          (((ArithmeticFunction.moebius (k / q) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (k / q) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hkQ
      have hkS := (Finset.mem_filter.mp hkQ).1
      have hksq := (Finset.mem_filter.mp hkQ).2
      have hkS' := hkS
      simp only [S, sieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hkS'
      have hkodd : Odd k :=
        (Nat.Coprime.of_dvd_right hx.two_dvd hkS'.2.2.2).odd_of_right
      have hμ : (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2) = 1 := by
        norm_cast
        exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hksq
      rw [hμ]
      simpa only [one_div] using
        inv_fW_eq_sum_divisors_totient_convolution hksq hkodd
    _ = ∑ z ∈ sieveNormConvolutionSource x ε,
        (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (fW z.2 * (Nat.totient z.2 : ℝ))) *
          (((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (z.1 / z.2) : ℝ)) := by
      symm
      unfold sieveNormConvolutionSource
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hkQ
      let F : ℕ → ℝ := fun q =>
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          (((ArithmeticFunction.moebius (k / q) : ℤ) : ℝ) ^ 2 /
            (Nat.totient (k / q) : ℝ))
      have hkS := (Finset.mem_filter.mp hkQ).1
      have hkS' := hkS
      simp only [sieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hkS'
      have hdivsubset : k.divisors ⊆ Finset.range (x + 1) := by
        intro q hq
        exact Finset.mem_range.mpr
          ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hq)).trans_lt
            (by omega))
      change (∑ q ∈ Finset.range (x + 1),
          if q ∈ k.divisors then F q else 0) =
        ∑ q ∈ k.divisors, F q
      have hfilter : (Finset.range (x + 1)).filter (· ∈ k.divisors) =
          k.divisors := by
        ext q
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨hdivsubset h, h⟩
      rw [← Finset.sum_filter, hfilter]

theorem sum_convolutionTarget_eq_totientSieveNumerator
    {x : ℕ} {ε : ℝ} :
    (∑ z ∈ sieveNormConvolutionTarget x ε,
        (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
            (fW z.1 * (Nat.totient z.1 : ℝ))) *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (Nat.totient z.2 : ℝ))) =
      ∑ q ∈ sieveNormIndices x ε,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          totientSieveNumerator x ε q := by
  let S := sieveNormIndices x ε
  let Q := S.filter Squarefree
  calc
    (∑ z ∈ sieveNormConvolutionTarget x ε,
        (((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) ^ 2 /
            (fW z.1 * (Nat.totient z.1 : ℝ))) *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 /
            (Nat.totient z.2 : ℝ))) =
      ∑ q ∈ Q,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          ∑ r ∈ (sieveNumeratorIndices x ε q).filter Squarefree,
            ((Nat.totient r : ℝ))⁻¹ := by
      unfold sieveNormConvolutionTarget
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro q hqQ
      rw [Finset.mul_sum]
      let A := (sieveNumeratorIndices x ε q).filter Squarefree
      have hA : A ⊆ Finset.range (x + 1) := by
        intro r hr
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      change (∑ r ∈ Finset.range (x + 1),
          if r ∈ A then
            (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
                (fW q * (Nat.totient q : ℝ))) *
              (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 /
                (Nat.totient r : ℝ))
          else 0) =
        ∑ r ∈ A,
          (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
              (fW q * (Nat.totient q : ℝ))) *
            ((Nat.totient r : ℝ))⁻¹
      have hfilter : (Finset.range (x + 1)).filter (· ∈ A) = A := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact fun h => h.2
        · intro hr
          exact ⟨Finset.mem_range.mp (hA hr), hr⟩
      rw [← Finset.sum_filter, hfilter]
      apply Finset.sum_congr rfl
      intro r hrA
      have hμ : (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2) = 1 := by
        norm_cast
        exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (Finset.mem_filter.mp hrA).2
      rw [hμ]
      norm_num
    _ = ∑ q ∈ Q,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          totientSieveNumerator x ε q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [totientSieveNumerator_eq_sum_squarefree]
    _ = ∑ q ∈ S,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          totientSieveNumerator x ε q := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q hqS hqQ
      have hnonsq : ¬Squarefree q := by
        intro hsq
        exact hqQ (Finset.mem_filter.mpr ⟨hqS, hsq⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnonsq]
      norm_num

/-- Exact `V_{qx}` expansion of Chen's normalizing sum. -/
theorem sieveNorm_eq_totientSieveNumerator_sum
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε) :
    sieveNorm x ε =
      ∑ q ∈ sieveNormIndices x ε,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            (fW q * (Nat.totient q : ℝ))) *
          totientSieveNumerator x ε q := by
  rw [sieveNorm_eq_sum_convolutionSource hx,
    sum_sieveNormConvolutionSource_eq_target hx1 hε0,
    sum_convolutionTarget_eq_totientSieveNumerator]

/-- Integer endpoint of the real interval in `sieveNumeratorIndices`. -/
noncomputable def sieveNumeratorCutoff
    (x : ℕ) (ε : ℝ) (q : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) / q⌋₊

theorem sieveNumeratorIndices_eq_Icc
    {x q : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hq : 1 ≤ q) :
    sieveNumeratorIndices x ε q =
      (Finset.Icc 1 (sieveNumeratorCutoff x ε q)).filter
        (fun r => r.Coprime (x * q)) := by
  let R : ℝ := (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)
  let Y : ℝ := R / q
  have hY0 : 0 ≤ Y := by positivity
  have hexp : (1 : ℝ) / 4 - ε / 2 ≤ 1 := by linarith
  have hRleX : R ≤ x := by
    dsimp only [R]
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hx1) hexp
  have hYleX : Y ≤ x := by
    dsimp only [Y]
    exact (div_le_self (by positivity : 0 ≤ R)
      (by exact_mod_cast hq)).trans hRleX
  have hfloorX : sieveNumeratorCutoff x ε q ≤ x := by
    have hfloor : (sieveNumeratorCutoff x ε q : ℝ) ≤ Y := by
      exact Nat.floor_le hY0
    exact_mod_cast hfloor.trans hYleX
  ext r
  simp only [sieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hrange, hr1, hrY, hcop⟩
    refine ⟨⟨hr1, ?_⟩, hcop⟩
    change r ≤ ⌊Y⌋₊
    rw [Nat.le_floor_iff hY0]
    simpa [Y, R] using hrY
  · rintro ⟨⟨hr1, hrfloor⟩, hcop⟩
    refine ⟨by omega, hr1, ?_, hcop⟩
    have hrfloor' : r ≤ ⌊Y⌋₊ := by
      simpa [sieveNumeratorCutoff, Y, R] using hrfloor
    rw [← Nat.le_floor_iff hY0]
    exact hrfloor'

theorem totientSieveNumerator_eq_mass
    {x q : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hq : 1 ≤ q) :
    totientSieveNumerator x ε q =
      totientSquarefreeMass (x * q) (sieveNumeratorCutoff x ε q) := by
  unfold totientSieveNumerator totientSquarefreeMass
  rw [sieveNumeratorIndices_eq_Icc hx1 hε0 hq]

theorem one_le_sieveNumeratorCutoff_of_mem
    {x q : ℕ} {ε : ℝ}
    (hq : q ∈ sieveNormIndices x ε) :
    1 ≤ sieveNumeratorCutoff x ε q := by
  have hq' := hq
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hq'
  unfold sieveNumeratorCutoff
  rw [Nat.one_le_floor_iff]
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast (show 0 < q by omega)
  rw [le_div_iff₀ hqpos]
  simpa using hq'.2.2.1

/-- The elementary `V_k` lower bound, specialized to every inner sum in
the exact expansion of `sieveNorm`. -/
theorem totient_mul_log_cutoff_div_le_totientSieveNumerator
    {x q : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hq : q ∈ sieveNormIndices x ε) :
    (Nat.totient (x * q) : ℝ) *
          Real.log (sieveNumeratorCutoff x ε q) / (x * q) ≤
      totientSieveNumerator x ε q := by
  have hq' := hq
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hq'
  rw [totientSieveNumerator_eq_mass hx1 hε0 hq'.2.1]
  simpa only [Nat.cast_mul] using totient_mul_log_div_le_totientSquarefreeMass
    (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hx1)
      (lt_of_lt_of_le Nat.zero_lt_one hq'.2.1))
    (one_le_sieveNumeratorCutoff_of_mem hq)

/-- After the elementary `V_k` estimate, the totient factors simplify to
the weighted logarithmic sum displayed in Chen's proof. -/
theorem sieveNormCutoffTerm_eq
    {x q : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hq : q ∈ sieveNormIndices x ε) :
    ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
          (fW q * (Nat.totient q : ℝ))) *
        ((Nat.totient (x * q) : ℝ) *
          Real.log (sieveNumeratorCutoff x ε q) / (x * q))) =
      ((Nat.totient x : ℝ) / x) *
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
          ((q : ℝ) * fW q)) *
            Real.log (sieveNumeratorCutoff x ε q)) := by
  have hq' := hq
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hq'
  have hqpos : 0 < q := by omega
  have hqodd : Odd q :=
    (Nat.Coprime.of_dvd_right hx.two_dvd hq'.2.2.2).odd_of_right
  have hx0 : (x : ℝ) ≠ 0 := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hφq : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hqpos).ne'
  have hfq : fW q ≠ 0 := (fW_pos_of_odd hqpos hqodd).ne'
  rw [Nat.totient_mul hq'.2.2.2.symm]
  push_cast
  field_simp

/-- Fully finite lower bound obtained from equation (22) and the elementary
`V_k` argument.  The remaining work in Lemma 7 is the asymptotic evaluation
of this weighted logarithmic sum and of `smoothedPrimeMass`. -/
theorem sieveNorm_weightedLog_lower
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) :
    ((Nat.totient x : ℝ) / x) *
        ∑ q ∈ sieveNormIndices x ε,
          ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
            ((q : ℝ) * fW q)) *
              Real.log (sieveNumeratorCutoff x ε q)) ≤
      sieveNorm x ε := by
  rw [sieveNorm_eq_totientSieveNumerator_sum hx hx1 hε0,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hq' := hq
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hq'
  have hqpos : 0 < q := by omega
  have hqodd : Odd q :=
    (Nat.Coprime.of_dvd_right hx.two_dvd hq'.2.2.2).odd_of_right
  have hcoeff :
      0 ≤ (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (fW q * (Nat.totient q : ℝ))) := by
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (fW_pos_of_odd hqpos hqodd).le
        (by positivity))
  rw [← sieveNormCutoffTerm_eq hx hx1 hq]
  exact mul_le_mul_of_nonneg_left
    (totient_mul_log_cutoff_div_le_totientSieveNumerator hx1 hε0 hq)
    hcoeff

/-- Finite Euler-product identity for the coefficients in the weighted
logarithmic lower bound. -/
theorem sum_divisors_moebius_sq_div_nat_mul_fW
    {d : ℕ} (hd : Squarefree d) (hodd : Odd d) :
    ∑ q ∈ d.divisors,
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
          ((q : ℝ) * fW q)) =
      ∏ p ∈ d.primeFactors,
        (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hd,
    Nat.sum_divisors_filter_squarefree hd.ne_zero]
  simp only [Nat.factors_eq]
  simp_rw [Finset.prod_val]
  have hterm :
      ∀ u ∈ d.primeFactors.powerset,
        (((ArithmeticFunction.moebius (∏ p ∈ u, p) : ℤ) : ℝ) ^ 2 /
            (((∏ p ∈ u, p : ℕ) : ℝ) * fW (∏ p ∈ u, p))) =
          ∏ p ∈ u,
            (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
    intro u hu
    have husub : u ⊆ d.primeFactors := Finset.mem_powerset.mp hu
    have hudvd : (∏ p ∈ u, p) ∣ d := by
      rw [← Nat.prod_primeFactors_of_squarefree hd]
      exact Finset.prod_dvd_prod_of_subset u d.primeFactors id husub
    have husq : Squarefree (∏ p ∈ u, p) :=
      hd.squarefree_of_dvd hudvd
    have huodd : Odd (∏ p ∈ u, p) := hodd.of_dvd_nat hudvd
    have huprime : ∀ p ∈ u, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (husub hp)
    have hμ :
        (((ArithmeticFunction.moebius (∏ p ∈ u, p) : ℤ) : ℝ) ^ 2) = 1 := by
      norm_cast
      exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree husq
    rw [hμ, fW_eq_prod_sub_two_of_squarefree_odd husq huodd,
      Nat.primeFactors_prod huprime, Nat.cast_prod]
    simp only [one_div]
    rw [← Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  calc
    (∑ u ∈ d.primeFactorsList.toFinset.powerset,
        (((ArithmeticFunction.moebius (∏ p ∈ u, p) : ℤ) : ℝ) ^ 2 /
          (((∏ p ∈ u, p : ℕ) : ℝ) * fW (∏ p ∈ u, p)))) =
        ∑ u ∈ d.primeFactors.powerset,
          ∏ p ∈ u,
            (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ∏ p ∈ d.primeFactors,
        (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
      rw [Finset.prod_one_add]

theorem divisor_mem_sieveNormIndices
    {x d q : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hdR : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2))
    (hdx : d.Coprime x) (hq : q ∈ d.divisors) :
    q ∈ sieveNormIndices x ε := by
  have hqd : q ∣ d := Nat.dvd_of_mem_divisors hq
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
  have hqdle : q ≤ d := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hq).2) hqd
  have hqdleR : (q : ℝ) ≤ d := by exact_mod_cast hqdle
  have hexp : (1 : ℝ) / 4 - ε / 2 ≤ 1 := by linarith
  have hRleX : (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hx1) hexp
  simp only [sieveNormIndices, Finset.mem_filter, Finset.mem_range]
  refine ⟨by
      have hqxR : (q : ℝ) ≤ x := hqdleR.trans (hdR.trans hRleX)
      have : q ≤ x := by exact_mod_cast hqxR
      omega,
    by omega, ?_, Nat.Coprime.of_dvd_left hqd hdx⟩
  exact hqdleR.trans hdR

/-- Uniform logarithmic lower bound for divisors of a fixed finite Euler
product.  The factor `2` absorbs the integer floor. -/
theorem log_rpow_div_two_mul_le_log_sieveNumeratorCutoff
    {x d q : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (_hε0 : 0 ≤ ε)
    (_hdx : d.Coprime x)
    (h2dR : ((2 * d : ℕ) : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2))
    (hq : q ∈ d.divisors) :
    Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) /
        (2 * d : ℕ)) ≤
      Real.log (sieveNumeratorCutoff x ε q) := by
  let R : ℝ := (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)
  have hdpos : 0 < d :=
    Nat.pos_of_ne_zero (Nat.mem_divisors.mp hq).2
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
  have hqd : q ∣ d := Nat.dvd_of_mem_divisors hq
  have hqdle : q ≤ d := Nat.le_of_dvd hdpos hqd
  have hRpos : 0 < R := by
    dsimp only [R]
    positivity
  have hY2 : (2 : ℝ) ≤ R / q := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < q)]
    calc
      (2 : ℝ) * q ≤ (2 : ℝ) * d := by gcongr
      _ ≤ R := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using h2dR
  have hfloorlt : R / q < (sieveNumeratorCutoff x ε q : ℝ) + 1 := by
    simpa only [sieveNumeratorCutoff, R] using
      Nat.lt_floor_add_one (R / q)
  have hhalfFloor : R / (2 * q) ≤
      (sieveNumeratorCutoff x ε q : ℝ) := by
    have hhalf : R / (2 * q) = (R / q) / 2 := by
      field_simp
    rw [hhalf]
    linarith
  have hdenmono : R / (2 * d) ≤ R / (2 * q) := by
    exact div_le_div_of_nonneg_left hRpos.le (by positivity) (by gcongr)
  have hleftpos : 0 < R / (2 * d) := by positivity
  have hcutpos : 0 < (sieveNumeratorCutoff x ε q : ℝ) :=
    lt_of_lt_of_le hleftpos (hdenmono.trans hhalfFloor)
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr hleftpos) (Set.mem_Ioi.mpr hcutpos)
    (hdenmono.trans hhalfFloor)
  simpa only [R, Nat.cast_mul, Nat.cast_ofNat] using hlog

/-- A finite Euler product gives a concrete lower bound for `sieveNorm`.
This is the finite approximation from which the asymptotic singular-series
constant is obtained. -/
theorem finiteEulerProduct_sieveNorm_lower
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hodd : Odd d)
    (hdx : d.Coprime x)
    (h2dR : ((2 * d : ℕ) : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)) :
    ((Nat.totient x : ℝ) / x) *
        (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) /
            (2 * d : ℕ)) *
          ∏ p ∈ d.primeFactors,
            (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) ≤
      sieveNorm x ε := by
  let R : ℝ := (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)
  let L : ℝ := Real.log (R / (2 * d : ℕ))
  let w : ℕ → ℝ := fun q =>
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
      ((q : ℝ) * fW q))
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hdR : (d : ℝ) ≤ R := by
    calc
      (d : ℝ) ≤ (2 * d : ℕ) := by
        norm_num [Nat.cast_mul]
        nlinarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
      _ ≤ R := by simpa only [R] using h2dR
  have hratio : (1 : ℝ) ≤ R / (2 * d : ℕ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 * d : ℕ))]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, one_mul] using h2dR
  have hL0 : 0 ≤ L := Real.log_nonneg hratio
  have hsubset : d.divisors ⊆ sieveNormIndices x ε := by
    intro q hq
    exact divisor_mem_sieveNormIndices hx1 hε0
      (by simpa only [R] using hdR) hdx hq
  have hdivisorTerms :
      ∑ q ∈ d.divisors, L * w q ≤
        ∑ q ∈ d.divisors,
          w q * Real.log (sieveNumeratorCutoff x ε q) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
    have hqodd : Odd q := hodd.of_dvd_nat (Nat.dvd_of_mem_divisors hq)
    have hw : 0 ≤ w q := by
      dsimp only [w]
      exact div_nonneg (sq_nonneg _)
        (mul_nonneg (by positivity) (fW_pos_of_odd hqpos hqodd).le)
    have hlog : L ≤ Real.log (sieveNumeratorCutoff x ε q) := by
      simpa only [L, R] using
        log_rpow_div_two_mul_le_log_sieveNumeratorCutoff
          hx1 hε0 hdx h2dR hq
    nlinarith [mul_le_mul_of_nonneg_left hlog hw]
  have hsieveTerms :
      ∑ q ∈ d.divisors,
          w q * Real.log (sieveNumeratorCutoff x ε q) ≤
        ∑ q ∈ sieveNormIndices x ε,
          w q * Real.log (sieveNumeratorCutoff x ε q) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro q hqS hqd
    have hq' := hqS
    simp only [sieveNormIndices, Finset.mem_filter,
      Finset.mem_range] at hq'
    have hqpos : 0 < q := by omega
    have hqodd : Odd q :=
      (Nat.Coprime.of_dvd_right hx.two_dvd hq'.2.2.2).odd_of_right
    have hw : 0 ≤ w q := by
      dsimp only [w]
      exact div_nonneg (sq_nonneg _)
        (mul_nonneg (by positivity) (fW_pos_of_odd hqpos hqodd).le)
    have hlog : 0 ≤ Real.log (sieveNumeratorCutoff x ε q) :=
      Real.log_nonneg (by
        exact_mod_cast one_le_sieveNumeratorCutoff_of_mem hqS)
    exact mul_nonneg hw hlog
  have hweighted :
      L * ∏ p ∈ d.primeFactors,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) ≤
        ∑ q ∈ sieveNormIndices x ε,
          w q * Real.log (sieveNumeratorCutoff x ε q) := by
    calc
      L * ∏ p ∈ d.primeFactors,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) =
          ∑ q ∈ d.divisors, L * w q := by
        rw [← sum_divisors_moebius_sq_div_nat_mul_fW hd hodd,
          Finset.mul_sum]
      _ ≤ ∑ q ∈ d.divisors,
          w q * Real.log (sieveNumeratorCutoff x ε q) := hdivisorTerms
      _ ≤ ∑ q ∈ sieveNormIndices x ε,
          w q * Real.log (sieveNumeratorCutoff x ε q) := hsieveTerms
  calc
    ((Nat.totient x : ℝ) / x) *
        (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) /
            (2 * d : ℕ)) *
          ∏ p ∈ d.primeFactors,
            (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) =
        ((Nat.totient x : ℝ) / x) *
          (L * ∏ p ∈ d.primeFactors,
            (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) := by
      rfl
    _ ≤ ((Nat.totient x : ℝ) / x) *
        ∑ q ∈ sieveNormIndices x ε,
          w q * Real.log (sieveNumeratorCutoff x ε q) := by
      exact mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ sieveNorm x ε := by
      simpa only [w] using sieveNorm_weightedLog_lower hx hx1 hε0

/-- Exact finite-factor form of the singular-series normalization. -/
theorem totient_div_mul_chenConst_eq_finiteEulerProduct
    {x : ℕ} (hx : Even x) (hx1 : 1 ≤ x) :
    ((Nat.totient x : ℝ) / x) * chenConst x =
      twinConst / 2 *
        ∏ p ∈ x.primeFactors.filter (2 < ·),
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
  have hx0 : x ≠ 0 := by omega
  have h2mem : 2 ∈ x.primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hx.two_dvd, hx0⟩
  have herase :
      x.primeFactors.erase 2 = x.primeFactors.filter (2 < ·) := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hp2, hp⟩
      refine ⟨hp, ?_⟩
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hpge : 2 ≤ p := hpprime.two_le
      omega
    · rintro ⟨hp, hp2⟩
      exact ⟨by omega, hp⟩
  have htotientFactors :
      ∏ p ∈ x.primeFactors,
          (1 - ((p : ℝ))⁻¹) =
        (1 / 2 : ℝ) *
          ∏ p ∈ x.primeFactors.filter (2 < ·),
            ((p : ℝ) - 1) / p := by
    calc
      (∏ p ∈ x.primeFactors, (1 - ((p : ℝ))⁻¹)) =
          (∏ p ∈ x.primeFactors.erase 2, (1 - ((p : ℝ))⁻¹)) *
            (1 - ((2 : ℝ))⁻¹) :=
        (Finset.prod_erase_mul _ _ h2mem).symm
      _ = (1 / 2 : ℝ) *
          ∏ p ∈ x.primeFactors.erase 2, (1 - ((p : ℝ))⁻¹) := by
        norm_num
        ring
      _ = (1 / 2 : ℝ) *
          ∏ p ∈ x.primeFactors.erase 2, ((p : ℝ) - 1) / p := by
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        have hpprime := Nat.prime_of_mem_primeFactors
          (Finset.mem_of_mem_erase hp)
        have hp0 : (p : ℝ) ≠ 0 := by
          exact_mod_cast hpprime.ne_zero
        field_simp
      _ = (1 / 2 : ℝ) *
          ∏ p ∈ x.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / p := by
        rw [herase]
  have hxR : (x : ℝ) ≠ 0 := by positivity
  have htotientRatio : (Nat.totient x : ℝ) / x =
      ∏ p ∈ x.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    rw [totient_cast_eq_mul_primeFactors]
    field_simp [hxR]
  have hlocal :
      (∏ p ∈ x.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / p) *
          (∏ p ∈ x.primeFactors.filter (2 < ·),
            ((p : ℝ) - 1) / ((p : ℝ) - 2)) =
        ∏ p ∈ x.primeFactors.filter (2 < ·),
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : 2 < p := (Finset.mem_filter.mp hp).2
    have hpR : (0 : ℝ) < p := by positivity
    have hp2R' : (2 : ℝ) < p := by exact_mod_cast hp2
    have hp2R : (0 : ℝ) < (p : ℝ) - 2 := sub_pos.mpr hp2R'
    field_simp
    ring
  rw [htotientRatio, htotientFactors, chenConst]
  calc
    (((1 / 2) *
          (∏ p ∈ x.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / p)) *
        ((∏ p ∈ x.primeFactors.filter (2 < ·),
          ((p : ℝ) - 1) / ((p : ℝ) - 2)) * twinConst)) =
      (1 / 2) *
        ((∏ p ∈ x.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / p) *
          ∏ p ∈ x.primeFactors.filter (2 < ·),
            ((p : ℝ) - 1) / ((p : ℝ) - 2)) * twinConst := by ring
    _ = (1 / 2) *
        (∏ p ∈ x.primeFactors.filter (2 < ·),
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) * twinConst := by
      rw [hlocal]
    _ = twinConst / 2 *
        ∏ p ∈ x.primeFactors.filter (2 < ·),
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by ring

theorem totient_div_mul_eulerProduct_mul_chenConst
    {x d : ℕ} (hx : Even x) (hx1 : 1 ≤ x)
    (_hodd : Odd d) (hdx : d.Coprime x) :
    (((Nat.totient x : ℝ) / x) *
        (∏ p ∈ d.primeFactors,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) *
        chenConst x) =
      twinConst / 2 *
        ∏ p ∈ (x.primeFactors.filter (2 < ·) ∪ d.primeFactors),
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
  have hdisj :
      Disjoint (x.primeFactors.filter (2 < ·)) d.primeFactors := by
    exact (hdx.symm.disjoint_primeFactors.mono_left
      (Finset.filter_subset _ _))
  rw [Finset.prod_union hdisj]
  rw [mul_assoc, mul_comm
    (∏ p ∈ d.primeFactors,
      (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))))
    (chenConst x), ← mul_assoc,
    totient_div_mul_chenConst_eq_finiteEulerProduct hx hx1]
  ring

/-- Product of a fixed finite set of odd primes after removing the primes
which divide `x`. -/
noncomputable def eulerApproxProduct (s : Finset ℕ) (x : ℕ) : ℕ :=
  ∏ p ∈ s.filter (fun p => ¬p ∣ x), p

theorem primeFactors_eulerApproxProduct
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime) (x : ℕ) :
    (eulerApproxProduct s x).primeFactors =
      s.filter (fun p => ¬p ∣ x) := by
  unfold eulerApproxProduct
  exact Nat.primeFactors_prod fun p hp =>
    hsprime p (Finset.mem_filter.mp hp).1

theorem squarefree_eulerApproxProduct
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime) (x : ℕ) :
    Squarefree (eulerApproxProduct s x) := by
  unfold eulerApproxProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp => ?_)
  · simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (hsprime p (Finset.mem_filter.mp hp).1)
      (hsprime q (Finset.mem_filter.mp hq).1)).mpr hpq
  · exact (hsprime p (Finset.mem_filter.mp hp).1).squarefree

theorem odd_eulerApproxProduct
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime)
    (hs2 : ∀ p ∈ s, 2 < p) (x : ℕ) :
    Odd (eulerApproxProduct s x) := by
  rw [← Nat.coprime_two_right]
  unfold eulerApproxProduct
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  have hps := (Finset.mem_filter.mp hp).1
  exact (hsprime p hps).odd_of_ne_two (ne_of_gt (hs2 p hps)) |>.coprime_two_right

theorem coprime_eulerApproxProduct
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime) (x : ℕ) :
    (eulerApproxProduct s x).Coprime x := by
  unfold eulerApproxProduct
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  exact (hsprime p (Finset.mem_filter.mp hp).1).coprime_iff_not_dvd.mpr
    (Finset.mem_filter.mp hp).2

theorem eulerApproxProduct_le_prod
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime) (x : ℕ) :
    eulerApproxProduct s x ≤ ∏ p ∈ s, p := by
  unfold eulerApproxProduct
  apply Finset.prod_le_prod_of_subset_of_one_le
    (Finset.filter_subset _ _)
  · intro p hp
    exact Nat.zero_le p
  · intro p hps hp
    exact (hsprime p hps).one_le

/-- The prime factors already present in `x`, together with the fixed primes
not dividing `x`, cover the whole fixed approximation set. -/
theorem finiteEulerProduct_le_x_union_approx
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime)
    (hs2 : ∀ p ∈ s, 2 < p) {x : ℕ} (hx1 : 1 ≤ x) :
    (∏ p ∈ s,
        (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) ≤
      ∏ p ∈
          (x.primeFactors.filter (2 < ·) ∪
            (eulerApproxProduct s x).primeFactors),
        (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
  have hx0 : x ≠ 0 := by omega
  have hsubset :
      s ⊆ x.primeFactors.filter (2 < ·) ∪
        (eulerApproxProduct s x).primeFactors := by
    intro p hp
    by_cases hpx : p ∣ x
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨by
        simp [Nat.mem_primeFactors, hsprime p hp, hpx, hx0], hs2 p hp⟩
    · apply Finset.mem_union_right
      rw [primeFactors_eulerApproxProduct hsprime]
      exact Finset.mem_filter.mpr ⟨hp, hpx⟩
  apply Finset.prod_le_prod_of_subset_of_one_le hsubset
  · intro p hp
    have hp2 := hs2 p hp
    have hp2R : (2 : ℝ) < p := by exact_mod_cast hp2
    have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 2) := by
      exact mul_pos (by positivity) (sub_pos.mpr hp2R)
    exact add_nonneg zero_le_one (div_nonneg zero_le_one hden.le)
  · intro p hpU hpS
    have hp2 : 2 < p := by
      rcases Finset.mem_union.mp hpU with hpX | hpD
      · exact (Finset.mem_filter.mp hpX).2
      · rw [primeFactors_eulerApproxProduct hsprime] at hpD
        exact hs2 p (Finset.mem_filter.mp hpD).1
    have hp2R : (2 : ℝ) < p := by exact_mod_cast hp2
    have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 2) := by
      exact mul_pos (by positivity) (sub_pos.mpr hp2R)
    have hterm : (0 : ℝ) ≤
        (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) :=
      div_nonneg zero_le_one hden.le
    linarith

/-- Uniform coefficient comparison: primes dividing `x` are supplied by
`chenConst`, and all other primes in `s` are supplied by
`eulerApproxProduct s x`. -/
theorem fixedEulerProduct_coefficient_lower
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime)
    (hs2 : ∀ p ∈ s, 2 < p) {x : ℕ}
    (hx : Even x) (hx1 : 1 ≤ x) :
    twinConst / 2 *
        ∏ p ∈ s,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) ≤
      ((Nat.totient x : ℝ) / x) *
        (∏ p ∈ (eulerApproxProduct s x).primeFactors,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) *
        chenConst x := by
  calc
    twinConst / 2 *
        ∏ p ∈ s,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) ≤
      twinConst / 2 *
        ∏ p ∈
            (x.primeFactors.filter (2 < ·) ∪
              (eulerApproxProduct s x).primeFactors),
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
      exact mul_le_mul_of_nonneg_left
        (finiteEulerProduct_le_x_union_approx hsprime hs2 hx1)
        (by positivity [twinConst_pos])
    _ = ((Nat.totient x : ℝ) / x) *
        (∏ p ∈ (eulerApproxProduct s x).primeFactors,
          (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) *
        chenConst x := by
      symm
      exact totient_div_mul_eulerProduct_mul_chenConst hx hx1
        (odd_eulerApproxProduct hsprime hs2 x)
        (coprime_eulerApproxProduct hsprime x)

/-- Uniform finite-product lower bound.  All dependence on `x` is now in
`chenConst x` and the main logarithm; the finite approximation set `s` is
fixed in advance. -/
theorem fixedEulerProduct_sieveNorm_lower
    {s : Finset ℕ} (hsprime : ∀ p ∈ s, p.Prime)
    (hs2 : ∀ p ∈ s, 2 < p) {x : ℕ} {ε : ℝ}
    (hx : Even x) (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (h2KR : ((2 * ∏ p ∈ s, p : ℕ) : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)) :
    ((twinConst / 2 *
          ∏ p ∈ s,
            (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) /
        chenConst x) *
        Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) /
          (2 * ∏ p ∈ s, p : ℕ)) ≤
      sieveNorm x ε := by
  let K : ℕ := ∏ p ∈ s, p
  let d : ℕ := eulerApproxProduct s x
  let R : ℝ := (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)
  let B : ℝ := twinConst / 2 *
    ∏ p ∈ s,
      (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))
  let P : ℝ := ∏ p ∈ d.primeFactors,
    (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))
  have hKpos : 0 < K := by
    dsimp only [K]
    exact Finset.prod_pos fun p hp => (hsprime p hp).pos
  have hdpos : 0 < d := by
    dsimp only [d, eulerApproxProduct]
    exact Finset.prod_pos fun p hp =>
      (hsprime p (Finset.mem_filter.mp hp).1).pos
  have hdK : d ≤ K := by
    simpa only [d, K] using eulerApproxProduct_le_prod hsprime x
  have h2dR : ((2 * d : ℕ) : ℝ) ≤ R := by
    calc
      ((2 * d : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 hdK
      _ ≤ R := by simpa only [K, R] using h2KR
  have hfinite :
      ((Nat.totient x : ℝ) / x) *
          (Real.log (R / (2 * d : ℕ)) * P) ≤ sieveNorm x ε := by
    simpa only [R, d, P] using
      finiteEulerProduct_sieveNorm_lower hx hx1 hε0
        (squarefree_eulerApproxProduct hsprime x)
        (odd_eulerApproxProduct hsprime hs2 x)
        (coprime_eulerApproxProduct hsprime x) h2dR
  have hCx : 0 < chenConst x :=
    twinConst_pos.trans_le (twinConst_le_chenConst x)
  have hcoef :
      B ≤ ((Nat.totient x : ℝ) / x) * P * chenConst x := by
    simpa only [B, P, d] using
      fixedEulerProduct_coefficient_lower hsprime hs2 hx hx1
  have hcoefDiv :
      B / chenConst x ≤ ((Nat.totient x : ℝ) / x) * P := by
    exact (div_le_iff₀ hCx).2 hcoef
  have hRpos : 0 < R := by
    dsimp only [R]
    positivity
  have hratioK : (1 : ℝ) ≤ R / (2 * K : ℕ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 * K : ℕ))]
    simpa only [K, R, one_mul] using h2KR
  have hlogK0 : 0 ≤ Real.log (R / (2 * K : ℕ)) :=
    Real.log_nonneg hratioK
  have hratio : R / (2 * K : ℕ) ≤ R / (2 * d : ℕ) := by
    exact div_le_div_of_nonneg_left hRpos.le (by positivity)
      (by exact_mod_cast Nat.mul_le_mul_left 2 hdK)
  have hlog :
      Real.log (R / (2 * K : ℕ)) ≤
        Real.log (R / (2 * d : ℕ)) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) hratio
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    apply Finset.prod_nonneg
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpdiv : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpne : p ≠ 2 :=
      (odd_eulerApproxProduct hsprime hs2 x).ne_two_of_dvd_nat hpdiv
    have hpge : 2 ≤ p := hpprime.two_le
    have hp2 : 2 < p := lt_of_le_of_ne hpge hpne.symm
    have hp2R : (2 : ℝ) < p := by exact_mod_cast hp2
    have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 2) := by
      exact mul_pos (by positivity) (sub_pos.mpr hp2R)
    have : (0 : ℝ) ≤
        (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by positivity
    linarith
  have hA0 : 0 ≤ ((Nat.totient x : ℝ) / x) * P :=
    mul_nonneg (by positivity) hP0
  calc
    ((twinConst / 2 *
          ∏ p ∈ s,
            (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))) /
        chenConst x) *
        Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) /
          (2 * ∏ p ∈ s, p : ℕ)) =
      (B / chenConst x) * Real.log (R / (2 * K : ℕ)) := by rfl
    _ ≤ (((Nat.totient x : ℝ) / x) * P) *
        Real.log (R / (2 * K : ℕ)) :=
      mul_le_mul_of_nonneg_right hcoefDiv hlogK0
    _ ≤ (((Nat.totient x : ℝ) / x) * P) *
        Real.log (R / (2 * d : ℕ)) :=
      mul_le_mul_of_nonneg_left hlog hA0
    _ = ((Nat.totient x : ℝ) / x) *
        (Real.log (R / (2 * d : ℕ)) * P) := by ring
    _ ≤ sieveNorm x ε := hfinite

/-- The asymptotic lower bound for Chen's normalizing sum, retaining enough
slack for the prime-number-theorem step at the end of Lemma 7. -/
theorem eventually_log_div_coefficient_le_sieveNorm
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, Even x →
      Real.log x / ((8 + 20 * ε) * chenConst x) ≤ sieveNorm x ε := by
  obtain ⟨s, hsprime, hs2, hsprod⟩ :=
    exists_finiteEulerProduct_ge_one_sub (show 0 < ε / 8 by positivity)
  let K : ℕ := ∏ p ∈ s, p
  let α : ℝ := (1 : ℝ) / 4 - ε / 2
  have hα : 0 < α := by
    dsimp only [α]
    linarith
  have hKpos : 0 < K := by
    dsimp only [K]
    exact Finset.prod_pos fun p hp => (hsprime p hp).pos
  have hrpow :
      ∀ᶠ x : ℕ in atTop,
        ((2 * K : ℕ) : ℝ) ≤ (x : ℝ) ^ α :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop ((2 * K : ℕ) : ℝ))
  let C : ℝ := (16 / ε) * Real.log (2 * K : ℕ)
  have hlogReal :
      ∀ᶠ y : ℝ in atTop, C ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop C)
  have hlogNat :
      ∀ᶠ x : ℕ in atTop, C ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hrpow, hlogNat, eventually_gt_atTop 1] with
      x hxR hxlog hx1
  intro hxEven
  have hx1' : 1 ≤ x := by omega
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx1)
  have hlogloss :
      Real.log (2 * K : ℕ) ≤ (ε / 16) * Real.log (x : ℝ) := by
    dsimp only [C] at hxlog
    have hεpos : 0 < ε / 16 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hxlog hεpos.le
    field_simp at hmul
    nlinarith
  have hL :
      (α - ε / 16) * Real.log (x : ℝ) ≤
        Real.log ((x : ℝ) ^ α / (2 * K : ℕ)) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_rpow hxpos]
    linarith
  have hαloss : 0 < α - ε / 16 := by
    dsimp only [α]
    linarith
  have hL0 : 0 ≤
      Real.log ((x : ℝ) ^ α / (2 * K : ℕ)) :=
    (mul_pos hαloss hlogpos).le.trans hL
  have hnorm := fixedEulerProduct_sieveNorm_lower
    hsprime hs2 hxEven hx1' hε.le (by simpa only [K, α] using hxR)
  have hCx : 0 < chenConst x :=
    twinConst_pos.trans_le (twinConst_le_chenConst x)
  let P : ℝ := ∏ p ∈ s,
    (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))
  have hprod' : 1 - ε / 8 ≤ twinConst * P := by
    simpa only [P] using hsprod
  have hprod0 : 0 ≤ twinConst * P := by
    have : 0 < 1 - ε / 8 := by linarith
    linarith
  have hnumeric :
      (1 : ℝ) / (8 + 20 * ε) ≤
        ((1 - ε / 8) / 2) * (α - ε / 16) := by
    have hden : 0 < 8 + 20 * ε := by positivity
    rw [div_le_iff₀ hden]
    dsimp only [α]
    have hpoly : 0 < 8 - 362 * ε + 45 * ε ^ 2 := by
      nlinarith [sq_nonneg ε]
    have hmul : 0 ≤ ε * (8 - 362 * ε + 45 * ε ^ 2) :=
      mul_nonneg hε.le hpoly.le
    nlinarith
  have hproduct :
      (((1 : ℝ) / (8 + 20 * ε)) * Real.log x) ≤
        (twinConst * P / 2) *
          Real.log ((x : ℝ) ^ α / (2 * K : ℕ)) := by
    calc
      ((1 : ℝ) / (8 + 20 * ε)) * Real.log x ≤
          (((1 - ε / 8) / 2) * (α - ε / 16)) *
            Real.log x := mul_le_mul_of_nonneg_right hnumeric hlogpos.le
      _ = ((1 - ε / 8) / 2) *
          ((α - ε / 16) * Real.log x) := by ring
      _ ≤ ((1 - ε / 8) / 2) *
          Real.log ((x : ℝ) ^ α / (2 * K : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hL (by linarith)
      _ ≤ (twinConst * P / 2) *
          Real.log ((x : ℝ) ^ α / (2 * K : ℕ)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hL0
  calc
    Real.log x / ((8 + 20 * ε) * chenConst x) =
        (((1 : ℝ) / (8 + 20 * ε)) * Real.log x) /
          chenConst x := by
      field_simp [hCx.ne']
    _ ≤ ((twinConst * P / 2) *
          Real.log ((x : ℝ) ^ α / (2 * K : ℕ))) /
        chenConst x := (div_le_div_iff_of_pos_right hCx).2 hproduct
    _ = ((twinConst / 2 * P) / chenConst x) *
        Real.log ((x : ℝ) ^ α / (2 * K : ℕ)) := by ring
    _ ≤ sieveNorm x ε := by
      simpa only [P, K, α] using hnorm

theorem eventually_sieveMainCoefficient_le
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, Even x →
      sieveMainCoefficient x ε ≤
        (8 + 20 * ε) * chenConst x / Real.log x := by
  filter_upwards [eventually_log_div_coefficient_le_sieveNorm ε hε hε',
      eventually_gt_atTop 1] with x hnorm hx1
  intro hxEven
  have hx1' : 1 ≤ x := by omega
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx1)
  have hCx : 0 < chenConst x :=
    twinConst_pos.trans_le (twinConst_le_chenConst x)
  have hcoef : 0 < 8 + 20 * ε := by positivity
  have hlower :
      0 < Real.log x / ((8 + 20 * ε) * chenConst x) := by positivity
  have hS : 0 < sieveNorm x ε :=
    zero_lt_one.trans_le (one_le_sieveNorm hxEven hx1' hε.le
      (by linarith : ε ≤ 1 / 2))
  rw [sieveMainCoefficient_eq_inv_sieveNorm hxEven hx1' hε.le
    (by linarith : ε ≤ 1 / 2)]
  calc
    (sieveNorm x ε)⁻¹ ≤
        (Real.log x / ((8 + 20 * ε) * chenConst x))⁻¹ :=
      (inv_le_inv₀ hS hlower).2 (hnorm hxEven)
    _ = (8 + 20 * ε) * chenConst x / Real.log x := by
      field_simp

end Chen
