import ChenTheorem.Lemma5.Boundary.Weights
import ChenTheorem.Lemma5.EulerPenalty
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Lower bounds for the Selberg normalization in Chen's Lemma 5

This file supplies the squarefree harmonic-mass and Euler-penalty
estimates used to lower-bound the truncated dimension-two Selberg mass.
-/

open Finset Real Filter
open scoped Nat.Prime Classical ArithmeticFunction

namespace Chen

noncomputable def coprimeDivisorCountAF (x : ℕ) :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p =>
    if p ∣ x then 1 else 2

theorem coprimeDivisorCountAF_isMultiplicative (x : ℕ) :
    (coprimeDivisorCountAF x).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem coprimeDivisorCountAF_prime
    (x : ℕ) {p : ℕ} (hp : p.Prime) :
    coprimeDivisorCountAF x p =
      if p ∣ x then 1 else 2 := by
  unfold coprimeDivisorCountAF
  simp [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp]

theorem smoothingTransitionNu_eq_coprimeDivisorCount_div
    {x l : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hq : q ∈ chenPairs x)
    (hlP : l ∣ transitionSieveProduct x)
    (hlsf : Squarefree l) :
    smoothingTransitionNu x q l =
      coprimeDivisorCountAF x l / l := by
  have hlocal :
      ∀ p ∈ l.primeFactors,
        smoothingTransitionNu x q p =
          coprimeDivisorCountAF x p / p := by
    intro p hpL
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
    have hpl : p ∣ l :=
      (Nat.mem_primeFactors.mp hpL).2.1
    have hpP : p ∣ transitionSieveProduct x := hpl.trans hlP
    rw [smoothingTransitionNu_prime hp
      (transitionSievePrime_not_dvd_pair hx hq hp hpP),
      coprimeDivisorCountAF_prime x hp]
  have hnu :=
    (smoothingTransitionNu_isMultiplicative x q).prod_primeFactors hlsf
  have hcount :=
    (coprimeDivisorCountAF_isMultiplicative x).prod_primeFactors hlsf
  rw [← hnu]
  calc
    ∏ p ∈ l.primeFactors, smoothingTransitionNu x q p =
        ∏ p ∈ l.primeFactors,
          coprimeDivisorCountAF x p / p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hlocal p hp
    _ = (∏ p ∈ l.primeFactors, coprimeDivisorCountAF x p) /
        ∏ p ∈ l.primeFactors, (p : ℝ) := by
      rw [Finset.prod_div_distrib]
    _ = coprimeDivisorCountAF x l / l := by
      rw [hcount, ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree hlsf]

theorem coprimeDivisorCount_div_le_selbergTerms
    {x l : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hxEven : Even x) (hq : q ∈ chenPairs x)
    (hlP : l ∣ transitionSieveProduct x)
    (hlsf : Squarefree l) :
    coprimeDivisorCountAF x l / l ≤
      (smoothingTransitionBoundingSieve x q hx hxEven hq).selbergTerms l := by
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  have hnu :
      s.nu l = coprimeDivisorCountAF x l / l := by
    exact smoothingTransitionNu_eq_coprimeDivisorCount_div
      hx hq hlP hlsf
  have hnupos : 0 < s.nu l := s.nu_pos_of_dvd_prodPrimes hlP
  have hprod :
      1 ≤ ∏ p ∈ l.primeFactors, (1 - s.nu p)⁻¹ := by
    apply Finset.one_le_prod
    intro p hpL
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
    have hpl : p ∣ l := (Nat.mem_primeFactors.mp hpL).2.1
    have hpP : p ∣ s.prodPrimes := hpl.trans hlP
    have hnuppos : 0 < s.nu p := s.nu_pos_of_dvd_prodPrimes hpP
    have hnult : s.nu p < 1 := s.nu_lt_one_of_prime p hp hpP
    exact (one_le_inv₀ (sub_pos.mpr hnult)).2 (by linarith)
  rw [(s.selbergTerms_apply l), ← hnu]
  nlinarith

theorem sum_squarefreeDivisors_inv_eq_powerset
    {x : ℕ} (hx : x ≠ 0) :
    ∑ d ∈ x.divisors.filter Squarefree, (d : ℝ)⁻¹ =
      ∑ t ∈ x.primeFactors.powerset,
        ((∏ p ∈ t, p : ℕ) : ℝ)⁻¹ := by
  refine Finset.sum_bij'
    (fun d _ => d.primeFactors)
    (fun t _ => ∏ p ∈ t, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_powerset]
    intro p hp
    have hd' := Finset.mem_filter.mp hd
    have hdvd : d ∣ x := Nat.dvd_of_mem_divisors hd'.1
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨hp'.1, hp'.2.1.trans hdvd, hx⟩
  · intro t ht
    have ht' := Finset.mem_powerset.mp ht
    apply Finset.mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      constructor
      · exact Nat.dvd_trans
          (Finset.prod_dvd_prod_of_subset
            t x.primeFactors id ht')
          (Nat.prod_primeFactors_dvd x)
      · exact hx
    · apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        change IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        exact (Nat.coprime_primes
          (Nat.prime_of_mem_primeFactors (ht' hp))
          (Nat.prime_of_mem_primeFactors (ht' hq))).2 hpq
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors (ht' hp)).squarefree
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree
      (Finset.mem_filter.mp hd).2
  · intro t ht
    exact Nat.primeFactors_prod (fun p hp =>
      Nat.prime_of_mem_primeFactors
        (Finset.mem_powerset.mp ht hp))
  · intro d hd
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_of_squarefree
      (Finset.mem_filter.mp hd).2).symm

theorem sum_squarefreeDivisors_inv_eq_penalty
    {x : ℕ} (hx : x ≠ 0) :
    ∑ d ∈ x.divisors.filter Squarefree, (d : ℝ)⁻¹ =
      primeFactorEulerPenalty x := by
  rw [sum_squarefreeDivisors_inv_eq_powerset hx]
  unfold primeFactorEulerPenalty
  calc
    ∑ t ∈ x.primeFactors.powerset,
        ((∏ p ∈ t, p : ℕ) : ℝ)⁻¹ =
      ∑ t ∈ x.primeFactors.powerset,
        (∏ p ∈ t, (p : ℝ)⁻¹) *
          ∏ _p ∈ x.primeFactors \ t, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Nat.cast_prod]
      simp
    _ = ∏ p ∈ x.primeFactors, ((p : ℝ)⁻¹ + 1) := by
      rw [← Finset.prod_add]
    _ = ∏ p ∈ x.primeFactors, (1 + (p : ℝ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro p hp
      ring

def squarefreeUpTo (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Squarefree

def squarefreeCoprimeUpTo (x Y : ℕ) : Finset ℕ :=
  (squarefreeUpTo Y).filter fun n => n.Coprime x

noncomputable def squarefreeHarmonic (Y : ℕ) : ℝ :=
  ∑ n ∈ squarefreeUpTo Y, (n : ℝ)⁻¹

noncomputable def squarefreeCoprimeHarmonic (x Y : ℕ) : ℝ :=
  ∑ n ∈ squarefreeCoprimeUpTo x Y, (n : ℝ)⁻¹

theorem squarefreeHarmonic_le_penalty_mul_coprime
    {x Y : ℕ} (hx : x ≠ 0) :
    squarefreeHarmonic Y ≤
      primeFactorEulerPenalty x *
        squarefreeCoprimeHarmonic x Y := by
  let S := squarefreeUpTo Y
  let D := x.divisors.filter Squarefree
  let B := squarefreeCoprimeUpTo x Y
  let f : ℕ → ℕ × ℕ := fun n => (n.gcd x, n / n.gcd x)
  have hfprod (n : ℕ) :
      (f n).1 * (f n).2 = n := by
    dsimp only [f]
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n x)]
  have hfinj :
      ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b := by
    intro a ha b hb hab
    have hprod := congrArg (fun z : ℕ × ℕ => z.1 * z.2) hab
    simpa only [hfprod] using hprod
  have hfmem :
      S.image f ⊆ D ×ˢ B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnS, rfl⟩
    have hn := Finset.mem_filter.mp hnS
    have hnIcc := Finset.mem_Icc.mp hn.1
    have hnsf := hn.2
    have hgcdpos : 0 < n.gcd x :=
      Nat.gcd_pos_of_pos_left x (by omega)
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n x, hx⟩
      · exact hnsf.squarefree_of_dvd (Nat.gcd_dvd_left n x)
    · unfold B squarefreeCoprimeUpTo
      apply Finset.mem_filter.mpr
      constructor
      · unfold squarefreeUpTo
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          constructor
          · exact Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_of_gt
                (Nat.div_pos
                  (Nat.gcd_le_left x (by omega)) hgcdpos))
          · exact (Nat.div_le_self n _).trans hnIcc.2
        · exact hnsf.squarefree_of_dvd
            (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n x))
      · exact Nat.coprime_div_gcd_of_squarefree hnsf hx
  have himage :
      (∑ z ∈ S.image f,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹)) =
        ∑ n ∈ S, (n : ℝ)⁻¹ := by
    rw [Finset.sum_image hfinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hfprod]
  have hsubset :
      (∑ z ∈ S.image f,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹)) ≤
        ∑ z ∈ D ×ˢ B,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hfmem
    intro z hzDB hzImage
    positivity
  have hproduct :
      (∑ z ∈ D ×ˢ B,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹)) =
        (∑ d ∈ D, (d : ℝ)⁻¹) *
          ∑ b ∈ B, (b : ℝ)⁻¹ := by
    rw [Finset.sum_product]
    simp_rw [Nat.cast_mul, mul_inv]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  unfold squarefreeHarmonic squarefreeCoprimeHarmonic
  change (∑ n ∈ S, (n : ℝ)⁻¹) ≤
    primeFactorEulerPenalty x * ∑ n ∈ B, (n : ℝ)⁻¹
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) =
        ∑ z ∈ S.image f,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := himage.symm
    _ ≤ ∑ z ∈ D ×ˢ B,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := hsubset
    _ = (∑ d ∈ D, (d : ℝ)⁻¹) *
          ∑ b ∈ B, (b : ℝ)⁻¹ := hproduct
    _ = primeFactorEulerPenalty x *
          ∑ b ∈ B, (b : ℝ)⁻¹ := by
      rw [show D = x.divisors.filter Squarefree by rfl,
        sum_squarefreeDivisors_inv_eq_penalty hx]

theorem exists_prime_sq_dvd_of_not_squarefree
    {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p : ℕ, p.Prime ∧ p * p ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at hn
  push Not at hn
  exact hn

noncomputable def repeatedPrime (n : ℕ) : ℕ :=
  if hn : ¬ Squarefree n then
    Classical.choose (exists_prime_sq_dvd_of_not_squarefree hn)
  else 2

theorem repeatedPrime_prime
    {n : ℕ} (hn : ¬ Squarefree n) :
    (repeatedPrime n).Prime := by
  unfold repeatedPrime
  rw [dif_pos hn]
  exact (Classical.choose_spec
    (exists_prime_sq_dvd_of_not_squarefree hn)).1

theorem repeatedPrime_sq_dvd
    {n : ℕ} (hn : ¬ Squarefree n) :
    repeatedPrime n * repeatedPrime n ∣ n := by
  unfold repeatedPrime
  rw [dif_pos hn]
  exact (Classical.choose_spec
    (exists_prime_sq_dvd_of_not_squarefree hn)).2

theorem sum_inv_sq_Icc_le_aux
    {Y : ℕ} (hY : 2 ≤ Y) :
    ∑ p ∈ Finset.Icc 2 Y, ((p : ℝ) ^ 2)⁻¹ ≤
      3 / 4 - 1 / (Y : ℝ) := by
  induction Y, hY using Nat.le_induction with
  | base =>
      simp
      norm_num
  | succ Y hY ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hYpos : (0 : ℝ) < Y := by positivity
      have hYsuccpos : (0 : ℝ) < Y + 1 := by positivity
      have hstep :
          (((Y + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
            1 / (Y : ℝ) - 1 / ((Y + 1 : ℕ) : ℝ) := by
        field_simp
        norm_num only [Nat.cast_add, Nat.cast_one] at *
        nlinarith
      calc
        ∑ p ∈ Finset.Icc 2 Y, ((p : ℝ) ^ 2)⁻¹ +
            ((((Y + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤
          (3 / 4 - 1 / (Y : ℝ)) +
            (1 / (Y : ℝ) - 1 / ((Y + 1 : ℕ) : ℝ)) :=
              add_le_add ih hstep
        _ = 3 / 4 - 1 / (((Y + 1 : ℕ) : ℝ)) := by ring

theorem sum_inv_sq_Icc_le (Y : ℕ) :
    ∑ p ∈ Finset.Icc 2 Y, ((p : ℝ) ^ 2)⁻¹ ≤ 3 / 4 := by
  by_cases hY : 2 ≤ Y
  · have hnonneg : 0 ≤ 1 / (Y : ℝ) := by positivity
    exact (sum_inv_sq_Icc_le_aux hY).trans (by linarith)
  · have hempty : Finset.Icc 2 Y = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    rw [hempty]
    norm_num

noncomputable def harmonicUpTo (Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹

noncomputable def nonsquarefreeHarmonic (Y : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Squarefree n),
    (n : ℝ)⁻¹

theorem nonsquarefreeHarmonic_le (Y : ℕ) :
    nonsquarefreeHarmonic Y ≤ (3 / 4) * harmonicUpTo Y := by
  let Bad := (Finset.Icc 1 Y).filter (fun n => ¬ Squarefree n)
  let P := Finset.Icc 2 Y
  let M := Finset.Icc 1 Y
  let f : ℕ → ℕ × ℕ := fun n =>
    let p := repeatedPrime n
    (p, n / (p * p))
  have hfprod {n : ℕ} (hn : n ∈ Bad) :
      (f n).1 ^ 2 * (f n).2 = n := by
    have hnBad := (Finset.mem_filter.mp hn).2
    dsimp only [f]
    rw [pow_two]
    rw [Nat.mul_div_cancel' (repeatedPrime_sq_dvd hnBad)]
  have hfinj :
      ∀ a ∈ Bad, ∀ b ∈ Bad, f a = f b → a = b := by
    intro a ha b hb hab
    have hprod := congrArg
      (fun z : ℕ × ℕ => z.1 ^ 2 * z.2) hab
    simpa only [hfprod ha, hfprod hb] using hprod
  have hfmem : Bad.image f ⊆ P ×ˢ M := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnBad, rfl⟩
    have hn := Finset.mem_filter.mp hnBad
    have hnIcc := Finset.mem_Icc.mp hn.1
    have hnNot := hn.2
    have hp := repeatedPrime_prime hnNot
    have hpdvd := repeatedPrime_sq_dvd hnNot
    have hpSqLe : repeatedPrime n * repeatedPrime n ≤ n :=
      Nat.le_of_dvd (by omega) hpdvd
    have hpLe : repeatedPrime n ≤ n := by
      nlinarith [hp.two_le]
    have hpSqPos : 0 < repeatedPrime n * repeatedPrime n := by
      exact Nat.mul_pos hp.pos hp.pos
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr
        ⟨hp.two_le, hpLe.trans hnIcc.2⟩
    · exact Finset.mem_Icc.mpr
        ⟨Nat.div_pos hpSqLe hpSqPos,
          (Nat.div_le_self n _).trans hnIcc.2⟩
  have himage :
      (∑ z ∈ Bad.image f,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹)) =
        ∑ n ∈ Bad, (n : ℝ)⁻¹ := by
    rw [Finset.sum_image hfinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Nat.cast_pow, ← Nat.cast_mul, hfprod hn]
  have hsubset :
      (∑ z ∈ Bad.image f,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹)) ≤
        ∑ z ∈ P ×ˢ M,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hfmem
    intro z hzPM hzImage
    positivity
  have hproduct :
      (∑ z ∈ P ×ˢ M,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹)) =
        (∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹) *
          ∑ m ∈ M, (m : ℝ)⁻¹ := by
    rw [Finset.sum_product]
    simp_rw [mul_inv]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  unfold nonsquarefreeHarmonic harmonicUpTo
  change (∑ n ∈ Bad, (n : ℝ)⁻¹) ≤
    (3 / 4) * ∑ n ∈ M, (n : ℝ)⁻¹
  calc
    (∑ n ∈ Bad, (n : ℝ)⁻¹) =
        ∑ z ∈ Bad.image f,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹) := himage.symm
    _ ≤ ∑ z ∈ P ×ˢ M,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹) := hsubset
    _ = (∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹) *
          ∑ m ∈ M, (m : ℝ)⁻¹ := hproduct
    _ ≤ (3 / 4) * ∑ m ∈ M, (m : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact sum_inv_sq_Icc_le Y
      · positivity

theorem harmonicUpTo_eq_harmonic (Y : ℕ) :
    harmonicUpTo Y = (harmonic Y : ℝ) := by
  unfold harmonicUpTo
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (harmonic_eq_sum_Icc (n := Y))
  simpa only [Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using h.symm

theorem log_add_one_le_harmonicUpTo (Y : ℕ) :
    Real.log (Y + 1) ≤ harmonicUpTo Y := by
  rw [harmonicUpTo_eq_harmonic]
  exact_mod_cast log_add_one_le_harmonic Y

theorem quarter_harmonicUpTo_le_squarefreeHarmonic (Y : ℕ) :
    (1 / 4) * harmonicUpTo Y ≤ squarefreeHarmonic Y := by
  have hbad := nonsquarefreeHarmonic_le Y
  have hpartition :
      harmonicUpTo Y =
        squarefreeHarmonic Y + nonsquarefreeHarmonic Y := by
    unfold harmonicUpTo squarefreeHarmonic nonsquarefreeHarmonic
      squarefreeUpTo
    simpa only using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.Icc 1 Y) (p := Squarefree)
        (f := fun n => (n : ℝ)⁻¹)).symm
  have hHnonneg : 0 ≤ harmonicUpTo Y := by
    unfold harmonicUpTo
    positivity
  nlinarith

theorem primeFactorEulerPenalty_le_self
    {n : ℕ} (hn : 1 ≤ n) :
    primeFactorEulerPenalty n ≤ n := by
  unfold primeFactorEulerPenalty
  calc
    ∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹) ≤
        ∏ p ∈ n.primeFactors, (p : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
        have hpPos : (0 : ℝ) < p := by positivity
        have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
          simpa [one_div] using
            (inv_le_inv₀ hpPos (by norm_num)).2 hpR
        nlinarith
    _ ≤ (n : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.zero_lt_of_lt hn)
          (Nat.prod_primeFactors_dvd n)

theorem exists_global_primeFactorEulerPenalty_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      primeFactorEulerPenalty n ≤
        C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100) := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1
      eventually_primeFactorEulerPenalty_le_log_rpow
  let N : ℕ := max N₀ 1
  have hN : ∀ n, N ≤ n →
      primeFactorEulerPenalty n ≤
        (Real.log n) ^ ((1 : ℝ) / 100) := by
    intro n hn
    exact hN₀ n ((le_max_left N₀ 1).trans hn)
  have hNone : 1 ≤ N := le_max_right N₀ 1
  let b : ℝ := (1 : ℝ) / 100
  let L : ℝ := (Real.log 2) ^ b
  let C : ℝ := max 1 ((N : ℝ) / L)
  have hb : 0 < b := by
    dsimp only [b]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n
  have hlogmono :
      Real.log 2 ≤ Real.log (n + 2) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by norm_num)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hbase :
      L ≤ (Real.log (n + 2)) ^ b := by
    exact Real.rpow_le_rpow hlog2.le hlogmono hb.le
  by_cases hnN : N ≤ n
  · have hnlarge := hN n hnN
    have hnone : 1 ≤ n := hNone.trans hnN
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hnone
    have hlogn :
        Real.log n ≤ Real.log (n + 2) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast (show n ≤ n + 2 by omega)
    have hpow :
        (Real.log n) ^ b ≤
          (Real.log (n + 2)) ^ b := by
      apply Real.rpow_le_rpow
      · exact Real.log_nonneg (by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0))
      · exact hlogn
      · exact hb.le
    calc
      primeFactorEulerPenalty n ≤ (Real.log n) ^ b := hnlarge
      _ ≤ (Real.log (n + 2)) ^ b := hpow
      _ ≤ C * (Real.log (n + 2)) ^ b := by
        exact le_mul_of_one_le_left
          (Real.rpow_nonneg (Real.log_nonneg (by
            exact_mod_cast (show 1 ≤ n + 2 by omega))) _)
          (le_max_left _ _)
      _ = C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100) := by rfl
  · have hnlt : n < N := by omega
    have hpen : primeFactorEulerPenalty n ≤ max 1 (N : ℝ) := by
      by_cases hn0 : n = 0
      · subst n
        simp [primeFactorEulerPenalty]
      · calc
          primeFactorEulerPenalty n ≤ n :=
            primeFactorEulerPenalty_le_self
              (Nat.one_le_iff_ne_zero.mpr hn0)
          _ ≤ N := by exact_mod_cast (Nat.le_of_lt hnlt)
          _ ≤ max 1 (N : ℝ) := le_max_right _ _
    have hNL : (N : ℝ) ≤ C * L := by
      dsimp only [C]
      calc
        (N : ℝ) = ((N : ℝ) / L) * L := by
          field_simp
        _ ≤ max 1 ((N : ℝ) / L) * L :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le
    have honeL : (1 : ℝ) ≤ C * L := by
      have hNoneR : (1 : ℝ) ≤ N := by exact_mod_cast hNone
      exact hNoneR.trans hNL
    calc
      primeFactorEulerPenalty n ≤ max 1 (N : ℝ) := hpen
      _ ≤ C * L := max_le honeL hNL
      _ ≤ C * (Real.log (n + 2)) ^ b :=
        mul_le_mul_of_nonneg_left hbase hC.le
      _ = C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100) := by rfl

noncomputable def coprimePairHarmonic (x Y : ℕ) : ℝ :=
  ∑ b ∈ squarefreeCoprimeUpTo x Y,
    (b : ℝ)⁻¹ * squarefreeCoprimeHarmonic b Y

theorem squarefreeHarmonic_sq_le_pairHarmonic
    {C : ℝ} (hC : 0 < C)
    (hglobal : ∀ n : ℕ,
      primeFactorEulerPenalty n ≤
        C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100))
    {x Y : ℕ} (hx : x ≠ 0) :
    (squarefreeHarmonic Y) ^ 2 ≤
      primeFactorEulerPenalty x *
        (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
          coprimePairHarmonic x Y := by
  let B := squarefreeCoprimeUpTo x Y
  let H := squarefreeHarmonic Y
  let K := C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)
  have hlog : 0 < Real.log (Y + 2) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y + 2 by omega))
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hH : 0 ≤ H := by
    dsimp only [H, squarefreeHarmonic]
    positivity
  have hB : 0 ≤ squarefreeCoprimeHarmonic x Y := by
    unfold squarefreeCoprimeHarmonic
    positivity
  have hremoveX :
      H ≤ primeFactorEulerPenalty x *
        squarefreeCoprimeHarmonic x Y := by
    exact squarefreeHarmonic_le_penalty_mul_coprime hx
  have hpoint :
      ∀ b ∈ B,
        H ≤ K * squarefreeCoprimeHarmonic b Y := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hbS := Finset.mem_filter.mp hb'.1
    have hbY := (Finset.mem_Icc.mp hbS.1).2
    have hremoveB :=
      squarefreeHarmonic_le_penalty_mul_coprime
        (x := b) (Y := Y)
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hbS.1).1)
    have hlogmono :
        Real.log (b + 2) ≤ Real.log (Y + 2) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast (show b + 2 ≤ Y + 2 by omega)
    have hrpow :
        (Real.log (b + 2)) ^ ((1 : ℝ) / 100) ≤
          (Real.log (Y + 2)) ^ ((1 : ℝ) / 100) := by
      apply Real.rpow_le_rpow
      · exact Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ b + 2 by omega))
      · exact hlogmono
      · norm_num
    have hpen : primeFactorEulerPenalty b ≤ K := by
      dsimp only [K]
      exact (hglobal b).trans
        (mul_le_mul_of_nonneg_left hrpow hC.le)
    calc
      H ≤ primeFactorEulerPenalty b *
          squarefreeCoprimeHarmonic b Y := hremoveB
      _ ≤ K * squarefreeCoprimeHarmonic b Y :=
        mul_le_mul_of_nonneg_right hpen (by
          unfold squarefreeCoprimeHarmonic
          positivity)
  have hweighted :
      H * squarefreeCoprimeHarmonic x Y ≤
        K * coprimePairHarmonic x Y := by
    have hsum :
        (∑ b ∈ B, (b : ℝ)⁻¹ * H) ≤
          ∑ b ∈ B,
            (b : ℝ)⁻¹ *
              (K * squarefreeCoprimeHarmonic b Y) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpoint b hb) (by positivity)
    unfold coprimePairHarmonic
    change H * (∑ b ∈ B, (b : ℝ)⁻¹) ≤
      K * ∑ b ∈ B,
        (b : ℝ)⁻¹ * squarefreeCoprimeHarmonic b Y
    calc
      H * (∑ b ∈ B, (b : ℝ)⁻¹) =
          ∑ b ∈ B, (b : ℝ)⁻¹ * H := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ ≤ ∑ b ∈ B,
            (b : ℝ)⁻¹ *
              (K * squarefreeCoprimeHarmonic b Y) := hsum
      _ = K * ∑ b ∈ B,
            (b : ℝ)⁻¹ * squarefreeCoprimeHarmonic b Y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
  have hpenx : 0 ≤ primeFactorEulerPenalty x := by
    unfold primeFactorEulerPenalty
    positivity
  calc
    H ^ 2 = H * H := by ring
    _ ≤ H * (primeFactorEulerPenalty x *
          squarefreeCoprimeHarmonic x Y) :=
      mul_le_mul_of_nonneg_left hremoveX hH
    _ = primeFactorEulerPenalty x *
        (H * squarefreeCoprimeHarmonic x Y) := by ring
    _ ≤ primeFactorEulerPenalty x *
        (K * coprimePairHarmonic x Y) :=
      mul_le_mul_of_nonneg_left hweighted hpenx
    _ = primeFactorEulerPenalty x *
        (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
          coprimePairHarmonic x Y := by
      dsimp only [K]
      ring

def allowedPrimeSubsets (x l : ℕ) : Finset (Finset ℕ) :=
  l.primeFactors.powerset.filter fun t =>
    ∀ p ∈ t, ¬ p ∣ x

theorem allowedPrimeSubsets_eq (x l : ℕ) :
    allowedPrimeSubsets x l =
      (l.primeFactors.filter fun p => ¬ p ∣ x).powerset := by
  ext t
  simp only [allowedPrimeSubsets, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨ht, hcop⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨ht hp, hcop p hp⟩
  · intro ht
    constructor
    · intro p hp
      exact (Finset.mem_filter.mp (ht hp)).1
    · intro p hp
      exact (Finset.mem_filter.mp (ht hp)).2

theorem allowedPrimeSubsets_card
    {x l : ℕ} (hl : Squarefree l) :
    ((allowedPrimeSubsets x l).card : ℝ) =
      coprimeDivisorCountAF x l := by
  rw [allowedPrimeSubsets_eq]
  unfold coprimeDivisorCountAF
  rw [ArithmeticFunction.prodPrimeFactors_apply hl.ne_zero]
  rw [Finset.card_powerset]
  push_cast
  rw [Finset.prod_ite]
  simp

theorem coprimePairHarmonic_le_truncatedSelbergMass
    {x Y R : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hxEven : Even x) (hq : q ∈ chenPairs x)
    (hYsq : Y ^ 2 ≤ R)
    (hRcut : R ≤ transitionSieveCutoff x) :
    coprimePairHarmonic x Y ≤
      truncatedSelbergMass
        (smoothingTransitionBoundingSieve x q hx hxEven hq) R := by
  let B := squarefreeCoprimeUpTo x Y
  let A : ℕ → Finset ℕ := fun b => squarefreeCoprimeUpTo b Y
  let D := truncatedSieveDivisors (transitionSieveProduct x) R
  let T : ℕ → Finset (Finset ℕ) := fun l => allowedPrimeSubsets x l
  let source := B.sigma A
  let target := D.sigma T
  let f : (Σ _b : ℕ, ℕ) → (Σ _l : ℕ, Finset ℕ) := fun z =>
    ⟨z.1 * z.2, z.1.primeFactors⟩
  have hsource_mem {z : Σ _b : ℕ, ℕ} (hz : z ∈ source) :
      z.1 ∈ B ∧ z.2 ∈ A z.1 :=
    Finset.mem_sigma.mp hz
  have htarget : source.image f ⊆ target := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    have hw' := hsource_mem hw
    have hb := Finset.mem_filter.mp hw'.1
    have hbS := Finset.mem_filter.mp hb.1
    have hbIcc := Finset.mem_Icc.mp hbS.1
    have hbSf := hbS.2
    have hbx := hb.2
    have ha := Finset.mem_filter.mp hw'.2
    have haS := Finset.mem_filter.mp ha.1
    have haIcc := Finset.mem_Icc.mp haS.1
    have haSf := haS.2
    have hab := ha.2
    have hlSf : Squarefree (w.1 * w.2) :=
      (Nat.squarefree_mul hab.symm).2 ⟨hbSf, haSf⟩
    have hlLe : w.1 * w.2 ≤ R := by
      have : w.1 * w.2 ≤ Y ^ 2 := by
        nlinarith
      exact this.trans hYsq
    have hlP : w.1 * w.2 ∣ transitionSieveProduct x := by
      unfold transitionSieveProduct primorial
      rw [← Nat.prod_primeFactors_of_squarefree hlSf]
      apply Finset.prod_dvd_prod_of_subset
        (w.1 * w.2).primeFactors
        ((Finset.range (transitionSieveCutoff x + 1)).filter Nat.Prime)
        id
      intro p hpL
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
      have hpl : p ∣ w.1 * w.2 :=
        (Nat.mem_primeFactors.mp hpL).2.1
      have hpLeL : p ≤ w.1 * w.2 :=
        Nat.le_of_dvd
          (Nat.mul_pos
            (Nat.zero_lt_of_lt hbIcc.1)
            (Nat.zero_lt_of_lt haIcc.1))
          hpl
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_range]
        exact Nat.lt_succ_of_le
          (hpLeL.trans (hlLe.trans hRcut))
      · exact hp
    apply Finset.mem_sigma.mpr
    constructor
    · unfold D truncatedSieveDivisors
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr
          ⟨hlP, transitionSieveProduct_ne_zero x⟩, hlLe⟩
    · unfold T allowedPrimeSubsets
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_powerset]
        intro p hpb
        have hpbDvd : p ∣ w.1 :=
          (Nat.mem_primeFactors.mp hpb).2.1
        have hp := Nat.prime_of_mem_primeFactors hpb
        exact Nat.mem_primeFactors.mpr
          ⟨hp, hpbDvd.trans (Nat.dvd_mul_right _ _),
            mul_ne_zero
              (Nat.one_le_iff_ne_zero.mp hbIcc.1)
              (Nat.one_le_iff_ne_zero.mp haIcc.1)⟩
      · intro p hpb hpx
        have hp := Nat.prime_of_mem_primeFactors hpb
        have hpgcd : p ∣ w.1.gcd x := Nat.dvd_gcd
          (Nat.mem_primeFactors.mp hpb).2.1 hpx
        rw [hbx] at hpgcd
        exact hp.not_dvd_one hpgcd
  have hfinj :
      ∀ a ∈ source, ∀ b ∈ source, f a = f b → a = b := by
    intro a ha b hb habEq
    have ha' := hsource_mem ha
    have hb' := hsource_mem hb
    have ha1 := Finset.mem_filter.mp
      (Finset.mem_filter.mp ha'.1).1
    have haIcc := Finset.mem_Icc.mp ha1.1
    have hb1 := Finset.mem_filter.mp
      (Finset.mem_filter.mp hb'.1).1
    have hpf : a.1.primeFactors = b.1.primeFactors :=
      congrArg Sigma.snd habEq
    have hfirst : a.1 = b.1 := by
      rw [← Nat.prod_primeFactors_of_squarefree ha1.2,
        ← Nat.prod_primeFactors_of_squarefree hb1.2, hpf]
    have hmul : a.1 * a.2 = b.1 * b.2 :=
      congrArg Sigma.fst habEq
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    simp only at hfirst hmul ⊢
    subst b1
    have hsecond : a2 = b2 :=
      Nat.mul_left_cancel (Nat.zero_lt_of_lt haIcc.1) hmul
    subst b2
    rfl
  have himage :
      (∑ z ∈ source.image f,
          ((z.1 : ℝ)⁻¹)) =
        ∑ z ∈ source,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    rw [Finset.sum_image hfinj]
  have hsubset :
      (∑ z ∈ source.image f, ((z.1 : ℝ)⁻¹)) ≤
        ∑ z ∈ target, ((z.1 : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg htarget
    intro z hzT hzI
    positivity
  have hsourceSum :
      coprimePairHarmonic x Y =
        ∑ z ∈ source,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    unfold coprimePairHarmonic squarefreeCoprimeHarmonic
    change
      (∑ b ∈ B, (b : ℝ)⁻¹ * ∑ a ∈ A b, (a : ℝ)⁻¹) =
        ∑ z ∈ source, (((z.1 * z.2 : ℕ) : ℝ)⁻¹)
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Nat.cast_mul, mul_inv]
  have htargetMass :
      (∑ z ∈ target, ((z.1 : ℝ)⁻¹)) ≤
        truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q hx hxEven hq) R := by
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    unfold truncatedSelbergMass
    change (∑ z ∈ D.sigma T, ((z.1 : ℝ)⁻¹)) ≤
      ∑ l ∈ D, s.selbergTerms l
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro l hlD
    have hlP : l ∣ transitionSieveProduct x :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hlD).1
    have hlsf : Squarefree l :=
      (transitionSieveProduct_squarefree x).squarefree_of_dvd hlP
    calc
      ∑ _t ∈ T l, (l : ℝ)⁻¹ =
          ((T l).card : ℝ) * (l : ℝ)⁻¹ := by simp
      _ = coprimeDivisorCountAF x l / l := by
        rw [show T l = allowedPrimeSubsets x l by rfl,
          allowedPrimeSubsets_card hlsf]
        ring
      _ ≤ s.selbergTerms l := by
        exact coprimeDivisorCount_div_le_selbergTerms
          hx hxEven hq hlP hlsf
  calc
    coprimePairHarmonic x Y =
        ∑ z ∈ source, (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := hsourceSum
    _ = ∑ z ∈ source.image f, ((z.1 : ℝ)⁻¹) := himage.symm
    _ ≤ ∑ z ∈ target, ((z.1 : ℝ)⁻¹) := hsubset
    _ ≤ truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q hx hxEven hq) R :=
      htargetMass

end Chen
