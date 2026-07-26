/-
Preparatory definitions and elementary reductions for Lemma 5 of Chen's paper.

This file deliberately stays on the finite-sum side of the argument.  The
vertical-integral representation of `mTwo` belongs to Lemma 6.
-/
import ChenTheorem.SieveLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.NumberTheory.Harmonic.Bounds

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! ### Support of Chen's sieve weights -/

@[simp]
theorem fW_one : fW 1 = 1 := by
  simp [fW]

theorem fW_pos_of_odd {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < fW n := by
  unfold fW
  apply mul_pos
  · exact_mod_cast Nat.totient_pos.mpr hn
  · apply Finset.prod_pos
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpne : p ≠ 2 := hodd.ne_two_of_dvd_nat hpd
    have hp2 := hpprime.two_le
    have hp3 : 3 ≤ p := by omega
    have hp2r : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
    have hp1r : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    exact div_pos (sub_pos.mpr hp2r) (sub_pos.mpr hp1r)

theorem fW_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.Coprime b) :
    fW (a * b) = fW a * fW b := by
  unfold fW
  rw [Nat.totient_mul hab, Nat.primeFactors_mul ha hb,
    Finset.prod_union hab.disjoint_primeFactors]
  simp only [Nat.cast_mul]
  ring

theorem totient_cast_eq_prod_sub_one_of_squarefree {n : ℕ}
    (hn : Squarefree n) :
    (Nat.totient n : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
  have hnat :
      Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree hn,
      Nat.div_self (Nat.pos_of_ne_zero hn.ne_zero), one_mul]
  rw [hnat, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp))]
  norm_num

theorem fW_eq_prod_sub_two_of_squarefree_odd {n : ℕ}
    (hn : Squarefree n) (hodd : Odd n) :
    fW n = ∏ p ∈ n.primeFactors, ((p : ℝ) - 2) := by
  unfold fW
  rw [totient_cast_eq_prod_sub_one_of_squarefree hn,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hpne : p ≠ 2 := hodd.ne_two_of_dvd_nat hpd
  have hp2 := hpprime.two_le
  have hp1r : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp1r)
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ ((p : ℝ) - 2) hne

set_option maxHeartbeats 800000 in
theorem sum_divisors_inv_fW_eq_totient_div
    {d : ℕ} (hd : Squarefree d) (hodd : Odd d) :
    ∑ t ∈ d.divisors, (fW t)⁻¹ =
      (Nat.totient d : ℝ) / fW d := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hd,
    Nat.sum_divisors_filter_squarefree hd.ne_zero]
  simp only [Nat.factors_eq]
  simp_rw [Finset.prod_val]
  have hterm :
      ∀ u ∈ d.primeFactors.powerset,
        (fW (∏ p ∈ u, p))⁻¹ =
          ∏ p ∈ u, (((p : ℝ) - 2)⁻¹) := by
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
    rw [fW_eq_prod_sub_two_of_squarefree_odd husq huodd,
      Nat.primeFactors_prod huprime,
      Finset.prod_inv_distrib]
  calc
    (∑ u ∈ d.primeFactorsList.toFinset.powerset,
        (fW (∏ p ∈ u, p))⁻¹) =
        ∑ u ∈ d.primeFactors.powerset,
          ∏ p ∈ u, (((p : ℝ) - 2)⁻¹) := by
            apply Finset.sum_congr rfl
            exact hterm
    _ = ∏ p ∈ d.primeFactors, (1 + ((p : ℝ) - 2)⁻¹) := by
      rw [Finset.prod_one_add]
    _ = (Nat.totient d : ℝ) / fW d := by
      rw [totient_cast_eq_prod_sub_one_of_squarefree hd,
        fW_eq_prod_sub_two_of_squarefree_odd hd hodd,
        ← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hpne : p ≠ 2 := hodd.ne_two_of_dvd_nat hpd
      have hp2 := hpprime.two_le
      have hp2r : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
      have hne : (p : ℝ) - 2 ≠ 0 := ne_of_gt (sub_pos.mpr hp2r)
      field_simp
      ring

@[simp]
theorem sieveWeight_one (x : ℕ) (ε : ℝ) :
    sieveWeight x ε 1 = 1 := by
  simp [sieveWeight]

theorem sieveWeight_eq_zero_of_ne_one_of_cutoff
    {x d : ℕ} {ε : ℝ} (hd1 : d ≠ 1)
    (hd : (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) < d) :
    sieveWeight x ε d = 0 := by
  rw [sieveWeight, if_neg hd1, if_neg (not_le.mpr hd)]

theorem sieveWeight_eq_zero_of_not_squarefree
    {x d : ℕ} {ε : ℝ} (hd1 : d ≠ 1) (hd : ¬Squarefree d) :
    sieveWeight x ε d = 0 := by
  rw [sieveWeight]
  simp only [hd1, ↓reduceIte]
  split_ifs
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
  · rfl

theorem sieveWeight_support
    {x d : ℕ} {ε : ℝ} (hd : sieveWeight x ε d ≠ 0) :
    d = 1 ∨ (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · exact Or.inr <| by
      by_contra hcut
      exact hd (sieveWeight_eq_zero_of_ne_one_of_cutoff hd1 (lt_of_not_ge hcut))

theorem sieveWeight_support_squarefree
    {x d : ℕ} {ε : ℝ} (hd : sieveWeight x ε d ≠ 0) :
    Squarefree d := by
  by_cases hd1 : d = 1
  · simp [hd1]
  · by_contra hsq
    exact hd (sieveWeight_eq_zero_of_not_squarefree hd1 hsq)

private theorem sieveSummand_nonneg_of_coprime_even
    {x n : ℕ} (hx : Even x) (hn : 1 ≤ n) (hnx : n.Coprime x) :
    0 ≤ ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
  have hn2 : n.Coprime 2 :=
    Nat.Coprime.of_dvd_right hx.two_dvd hnx
  have hodd : Odd n := hn2.odd_of_right
  exact div_nonneg (sq_nonneg _)
    (le_of_lt (fW_pos_of_odd (by omega) hodd))

private theorem sieveProduct_mul_injective
    {x d : ℕ} {ε : ℝ} :
    Set.InjOn (fun z : ℕ × ℕ => z.1 * z.2)
      (↑(d.divisors ×ˢ sieveNumeratorIndices x ε d) : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  have ha' := Finset.mem_product.mp ha
  have hb' := Finset.mem_product.mp hb
  have had : a.1 ∣ d := Nat.dvd_of_mem_divisors ha'.1
  have hbd : b.1 ∣ d := Nat.dvd_of_mem_divisors hb'.1
  have hakxd : a.2.Coprime (x * d) := by
    have hak := ha'.2
    simp only [sieveNumeratorIndices, Finset.mem_filter,
      Finset.mem_range] at hak
    exact hak.2.2.2
  have hbkxd : b.2.Coprime (x * d) := by
    have hbk := hb'.2
    simp only [sieveNumeratorIndices, Finset.mem_filter,
      Finset.mem_range] at hbk
    exact hbk.2.2.2
  have hakd : a.2.Coprime d :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_left d x) hakxd
  have hbkd : b.2.Coprime d :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_left d x) hbkxd
  have hfirst : a.1 = b.1 := by
    calc
      a.1 = (a.2 * a.1).gcd d := by
        symm
        exact Nat.gcd_mul_of_coprime_of_dvd hakd had
      _ = (a.1 * a.2).gcd d := by rw [mul_comm]
      _ = (b.1 * b.2).gcd d := by
        exact congrArg (fun n => n.gcd d) hab
      _ = (b.2 * b.1).gcd d := by rw [mul_comm]
      _ = b.1 := Nat.gcd_mul_of_coprime_of_dvd hbkd hbd
  apply Prod.ext
  · exact hfirst
  · simp only [hfirst] at hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_dvd_of_pos hbd
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hb'.1).2)) hab

private theorem sieveProduct_image_subset_norm
    {x d : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hd0 : d ≠ 0) (hdx : d.Coprime x) :
    (d.divisors ×ˢ sieveNumeratorIndices x ε d).image
        (fun z : ℕ × ℕ => z.1 * z.2) ⊆
      sieveNormIndices x ε := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
  have ha' := Finset.mem_product.mp ha
  have htd : a.1 ∣ d := Nat.dvd_of_mem_divisors ha'.1
  have htpos : 0 < a.1 :=
    Nat.pos_of_dvd_of_pos htd (Nat.pos_of_ne_zero hd0)
  have hk := ha'.2
  simp only [sieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range] at hk
  have hRleX :
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) ≤ x := by
    have hexp : (1 : ℝ) / 4 - ε / 2 ≤ 1 := by linarith
    simpa using
      (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hx1) hexp)
  have hprodR :
      ((a.1 * a.2 : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    have hdposR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have hkd :
        (a.2 : ℝ) * d ≤
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) :=
      (le_div_iff₀ hdposR).mp hk.2.2.1
    have htle : a.1 ≤ d :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) htd
    have htler : (a.1 : ℝ) ≤ d := by exact_mod_cast htle
    calc
      ((a.1 * a.2 : ℕ) : ℝ) = (a.2 : ℝ) * a.1 := by
        norm_num [mul_comm]
      _ ≤ (a.2 : ℝ) * d := by
        exact mul_le_mul_of_nonneg_left htler (by positivity)
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := hkd
  have hprodX : a.1 * a.2 ≤ x := by
    exact_mod_cast hprodR.trans hRleX
  have htx : a.1.Coprime x :=
    Nat.Coprime.of_dvd_left htd hdx
  have hkx : a.2.Coprime x :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_right x d) hk.2.2.2
  simp only [sieveNormIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.mul_pos htpos (by omega), hprodR,
    htx.mul_left hkx⟩

private theorem sieveSummand_mul_eq
    {x d t k : ℕ} {ε : ℝ} (hd : Squarefree d)
    (ht : t ∈ d.divisors) (hk : k ∈ sieveNumeratorIndices x ε d) :
    ((ArithmeticFunction.moebius (t * k) : ℤ) : ℝ) ^ 2 / fW (t * k) =
      (fW t)⁻¹ *
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k) := by
  have htd : t ∣ d := Nat.dvd_of_mem_divisors ht
  have ht0 : t ≠ 0 := by
    exact ne_of_gt (Nat.pos_of_dvd_of_pos htd
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp ht).2))
  have hk' := hk
  simp only [sieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range] at hk'
  have hk0 : k ≠ 0 := by omega
  have hkd : k.Coprime d :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_left d x) hk'.2.2.2
  have htk : t.Coprime k :=
    (Nat.Coprime.of_dvd_right htd hkd).symm
  have htsq : Squarefree t := hd.squarefree_of_dvd htd
  have hmu :
      (((ArithmeticFunction.moebius t : ℤ) : ℝ) ^ 2) = 1 := by
    exact_mod_cast
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree htsq
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      htk.gcd_eq_one,
    fW_mul_of_coprime ht0 hk0 htk]
  push_cast
  rw [mul_pow, hmu]
  simp only [one_mul, div_eq_mul_inv, mul_inv]
  ring

/-- The normalization sum contains disjoint copies, indexed by the divisors
of `d`, of the numerator sum occurring in `λ_d`. -/
theorem totient_div_mul_sieveNumerator_le_sieveNorm
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hdx : d.Coprime x) :
    (Nat.totient d : ℝ) / fW d * sieveNumerator x ε d ≤
      sieveNorm x ε := by
  have hdodd : Odd d :=
    (Nat.Coprime.of_dvd_right hx.two_dvd hdx).odd_of_right
  let P := d.divisors ×ˢ sieveNumeratorIndices x ε d
  let imageP := P.image (fun z : ℕ × ℕ => z.1 * z.2)
  calc
    (Nat.totient d : ℝ) / fW d * sieveNumerator x ε d =
        (∑ t ∈ d.divisors, (fW t)⁻¹) *
          (∑ k ∈ sieveNumeratorIndices x ε d,
            ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k) := by
      rw [sum_divisors_inv_fW_eq_totient_div hd hdodd]
      rfl
    _ = ∑ t ∈ d.divisors,
          ∑ k ∈ sieveNumeratorIndices x ε d,
            (fW t)⁻¹ *
              (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
    _ = ∑ z ∈ P,
          ((ArithmeticFunction.moebius (z.1 * z.2) : ℤ) : ℝ) ^ 2 /
            fW (z.1 * z.2) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro k hk
      exact (sieveSummand_mul_eq hd ht hk).symm
    _ = ∑ n ∈ imageP,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
      dsimp only [imageP, P]
      exact (Finset.sum_image
        (f := fun n : ℕ =>
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n)
        (g := fun z : ℕ × ℕ => z.1 * z.2)
        sieveProduct_mul_injective).symm
    _ ≤ ∑ n ∈ sieveNormIndices x ε,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (sieveProduct_image_subset_norm hx1 hε0 hd.ne_zero hdx)
      intro n hn _
      have hn' := hn
      simp only [sieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      exact sieveSummand_nonneg_of_coprime_even hx hn'.2.1 hn'.2.2.2
    _ = sieveNorm x ε := rfl

theorem sieveNorm_nonneg
    {x : ℕ} {ε : ℝ} (hx : Even x) :
    0 ≤ sieveNorm x ε := by
  unfold sieveNorm
  apply Finset.sum_nonneg
  intro n hn
  have hn' := hn
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hn'
  exact sieveSummand_nonneg_of_coprime_even hx hn'.2.1 hn'.2.2.2

theorem sieveNumerator_nonneg
    {x d : ℕ} {ε : ℝ} (hx : Even x) :
    0 ≤ sieveNumerator x ε d := by
  unfold sieveNumerator
  apply Finset.sum_nonneg
  intro k hk
  have hk' := hk
  simp only [sieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range] at hk'
  have hkx : k.Coprime x :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_right x d) hk'.2.2.2
  exact sieveSummand_nonneg_of_coprime_even hx hk'.2.1 hkx

/-- Chen's elementary sieve weights satisfy the pointwise bound
`|λ_d| ≤ 1` on the range used in the paper. -/
theorem abs_sieveWeight_le_one
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hdx : d.Coprime x) :
    |sieveWeight x ε d| ≤ 1 := by
  by_cases hd1 : d = 1
  · simp [hd1]
  by_cases hcut :
      (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)
  · by_cases hdsq : Squarefree d
    · have hdodd : Odd d :=
        (Nat.Coprime.of_dvd_right hx.two_dvd hdx).odd_of_right
      have hfd : 0 < fW d :=
        fW_pos_of_odd (Nat.pos_of_ne_zero hdsq.ne_zero) hdodd
      have hA :
          0 ≤ (Nat.totient d : ℝ) / fW d :=
        div_nonneg (by positivity) hfd.le
      have hN : 0 ≤ sieveNumerator x ε d :=
        sieveNumerator_nonneg hx
      have hS0 : 0 ≤ sieveNorm x ε := sieveNorm_nonneg hx
      by_cases hS : sieveNorm x ε = 0
      · simp [sieveWeight, hd1, hS]
      · have hSpos : 0 < sieveNorm x ε := lt_of_le_of_ne hS0 (Ne.symm hS)
        have hnorm :=
          totient_div_mul_sieveNumerator_le_sieveNorm
            hx hx1 hε0 hdsq hdx
        have hB :
            0 ≤ (Nat.totient d : ℝ) / fW d *
              (sieveNumerator x ε d / sieveNorm x ε) :=
          mul_nonneg hA (div_nonneg hN hSpos.le)
        have hB1 :
            (Nat.totient d : ℝ) / fW d *
                (sieveNumerator x ε d / sieveNorm x ε) ≤ 1 := by
          have hdiv :
              ((Nat.totient d : ℝ) / fW d *
                  sieveNumerator x ε d) / sieveNorm x ε ≤ 1 :=
            (div_le_one hSpos).2 hnorm
          simpa [div_eq_mul_inv, mul_assoc] using hdiv
        have hmu :
            |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
          rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hdsq]
          norm_num
        rw [sieveWeight, if_neg hd1, if_pos hcut]
        have hform :
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                (Nat.totient d : ℝ) / fW d *
                  (sieveNumerator x ε d / sieveNorm x ε) =
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                ((Nat.totient d : ℝ) / fW d *
                  (sieveNumerator x ε d / sieveNorm x ε)) := by
          ring
        rw [hform, abs_mul, hmu, one_mul, abs_of_nonneg hB]
        exact hB1
    · simp [sieveWeight, hd1,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
  · rw [sieveWeight, if_neg hd1,
      if_neg (by simpa only [one_div] using hcut)]
    simp

/-! ### The `3^ν(d)` multiplicity in the `M₄` estimate -/

/-- Finite Dirichlet-character orthogonality for the residue class
`m ≡ x (mod d)`, written in the normalization used in equation (6). -/
theorem residueIndicator_eq_character_average
    {d x m : ℕ} (hd : 0 < d) (hxd : x.Coprime d) :
    ((if x ≡ m [MOD d] then 1 else 0 : ℝ) : ℂ) =
      (∑ χ : DirichletCharacter ℂ d,
          χ (x : ZMod d)⁻¹ * χ (m : ZMod d)) /
        (Nat.totient d : ℂ) := by
  letI : NeZero d := ⟨hd.ne'⟩
  have hxunit : IsUnit (x : ZMod d) :=
    (ZMod.isUnit_iff_coprime x d).2 hxd
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hxunit]
  by_cases hxm : x ≡ m [MOD d]
  · have heq : (x : ZMod d) = (m : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff x m d).2 hxm
    rw [if_pos hxm, if_pos heq]
    have hφ : (Nat.totient d : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hd).ne'
    simp [hφ]
  · have hne : (x : ZMod d) ≠ (m : ZMod d) := by
      simpa [ZMod.natCast_eq_natCast_iff] using hxm
    rw [if_neg hxm, if_neg hne]
    norm_num

theorem characterSum_eq_principal_add_nontrivial
    {d : ℕ} (hd : d ≠ 0) (F : DirichletCharacter ℂ d → ℂ) :
    ∑ χ : DirichletCharacter ℂ d, F χ =
      F 1 + nontrivialCharSum d F := by
  rw [nontrivialCharSum, dif_neg hd]
  calc
    ∑ χ : DirichletCharacter ℂ d, F χ =
        ∑ χ : DirichletCharacter ℂ d,
          ((if χ = 1 then F 1 else 0) +
            if χ = 1 then 0 else F χ) := by
      apply Finset.sum_congr rfl
      intro χ _
      split_ifs <;> simp_all
    _ = (∑ χ : DirichletCharacter ℂ d,
          if χ = 1 then F 1 else 0) +
        ∑ χ : DirichletCharacter ℂ d,
          if χ = 1 then 0 else F χ := by
      rw [Finset.sum_add_distrib]
    _ = F 1 + ∑ χ : DirichletCharacter ℂ d,
          if χ = 1 then 0 else F χ := by
      simp

/-- Orthogonality with the principal character separated.  The coprimality of
`m` removes the exceptional zero of the principal character; terms failing
this condition form `M₃` in the paper. -/
theorem residueIndicator_eq_principal_add_nontrivial
    {d x m : ℕ} (hd : 0 < d) (hxd : x.Coprime d)
    (hmd : m.Coprime d) :
    ((if x ≡ m [MOD d] then 1 else 0 : ℝ) : ℂ) =
      (1 + nontrivialCharSum d (fun χ =>
        χ (x : ZMod d)⁻¹ * χ (m : ZMod d))) /
          (Nat.totient d : ℂ) := by
  rw [residueIndicator_eq_character_average hd hxd,
    characterSum_eq_principal_add_nontrivial hd.ne']
  congr 2
  have hxunit : IsUnit (x : ZMod d) :=
    (ZMod.isUnit_iff_coprime x d).2 hxd
  have hmunit : IsUnit (m : ZMod d) :=
    (ZMod.isUnit_iff_coprime m d).2 hmd
  have hxunit' : IsUnit ((x : ℤ) : ZMod d) := by
    simpa using hxunit
  have hxinvunit : IsUnit ((x : ZMod d)⁻¹) := by
    simpa using ZMod.isUnit_inv hxunit'
  rw [MulChar.one_apply hxinvunit, MulChar.one_apply hmunit, one_mul]

/-- Weighted finite form of equation (6): character orthogonality converts a
residue-class sum into its principal-character average plus one explicitly
nontrivial character sum. -/
theorem weighted_mappedResidueSum_eq_principal_add_nontrivial
    {ι : Type*} [DecidableEq ι]
    {d x : ℕ} (hd : 0 < d) (hxd : x.Coprime d)
    (s : Finset ι) (a : ι → ℕ) (w : ι → ℝ)
    (hcop : ∀ i ∈ s, (a i).Coprime d) :
    ∑ i ∈ s, (w i : ℂ) *
        ((if x ≡ a i [MOD d] then 1 else 0 : ℝ) : ℂ) =
      ((∑ i ∈ s, (w i : ℂ)) +
        nontrivialCharSum d (fun χ =>
          χ (x : ZMod d)⁻¹ *
            ∑ i ∈ s, (w i : ℂ) * χ (a i : ZMod d))) /
        (Nat.totient d : ℂ) := by
  have horth :
      ∀ i ∈ s,
        ((if x ≡ a i [MOD d] then 1 else 0 : ℝ) : ℂ) =
          (∑ χ : DirichletCharacter ℂ d,
              χ (x : ZMod d)⁻¹ * χ (a i : ZMod d)) /
            (Nat.totient d : ℂ) :=
    fun _ _ => residueIndicator_eq_character_average hd hxd
  calc
    ∑ i ∈ s, (w i : ℂ) *
        ((if x ≡ a i [MOD d] then 1 else 0 : ℝ) : ℂ) =
        ∑ i ∈ s, (w i : ℂ) *
          ((∑ χ : DirichletCharacter ℂ d,
              χ (x : ZMod d)⁻¹ * χ (a i : ZMod d)) /
            (Nat.totient d : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [horth i hi]
    _ = (∑ χ : DirichletCharacter ℂ d,
          χ (x : ZMod d)⁻¹ *
            ∑ i ∈ s, (w i : ℂ) * χ (a i : ZMod d)) /
          (Nat.totient d : ℂ) := by
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      congr 1
      calc
        ∑ i ∈ s, (w i : ℂ) *
            ∑ χ : DirichletCharacter ℂ d,
              χ (x : ZMod d)⁻¹ * χ (a i : ZMod d) =
            ∑ i ∈ s, ∑ χ : DirichletCharacter ℂ d,
              (w i : ℂ) *
                (χ (x : ZMod d)⁻¹ * χ (a i : ZMod d)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ = ∑ χ : DirichletCharacter ℂ d, ∑ i ∈ s,
              (w i : ℂ) *
                (χ (x : ZMod d)⁻¹ * χ (a i : ZMod d)) := by
          rw [Finset.sum_comm]
        _ = ∑ χ : DirichletCharacter ℂ d,
              χ (x : ZMod d)⁻¹ *
                ∑ i ∈ s, (w i : ℂ) * χ (a i : ZMod d) := by
          apply Finset.sum_congr rfl
          intro χ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ((∑ i ∈ s, (w i : ℂ)) +
          nontrivialCharSum d (fun χ =>
            χ (x : ZMod d)⁻¹ *
              ∑ i ∈ s, (w i : ℂ) * χ (a i : ZMod d))) /
        (Nat.totient d : ℂ) := by
      rw [characterSum_eq_principal_add_nontrivial hd.ne']
      congr 2
      have hxunit : IsUnit (x : ZMod d) :=
        (ZMod.isUnit_iff_coprime x d).2 hxd
      have hxunit' : IsUnit ((x : ℤ) : ZMod d) := by
        simpa using hxunit
      have hxinvunit : IsUnit ((x : ZMod d)⁻¹) := by
        simpa using ZMod.isUnit_inv hxunit'
      rw [MulChar.one_apply hxinvunit, one_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hiunit : IsUnit (a i : ZMod d) :=
        (ZMod.isUnit_iff_coprime (a i) d).2 (hcop i hi)
      rw [MulChar.one_apply hiunit, mul_one]

theorem weighted_residueSum_eq_principal_add_nontrivial
    {d x : ℕ} (hd : 0 < d) (hxd : x.Coprime d)
    (s : Finset ℕ) (w : ℕ → ℝ)
    (hcop : ∀ m ∈ s, m.Coprime d) :
    ∑ m ∈ s, (w m : ℂ) *
        ((if x ≡ m [MOD d] then 1 else 0 : ℝ) : ℂ) =
      ((∑ m ∈ s, (w m : ℂ)) +
        nontrivialCharSum d (fun χ =>
          χ (x : ZMod d)⁻¹ *
            ∑ m ∈ s, (w m : ℂ) * χ (m : ZMod d))) /
        (Nat.totient d : ℂ) := by
  exact weighted_mappedResidueSum_eq_principal_add_nontrivial
    hd hxd s id w (by simpa using hcop)

/-- A residue class coprime to `d` contains only integers coprime to `d`.
This is the finite step that removes the `M₃` indices before applying
character orthogonality. -/
theorem weighted_residueSum_eq_filter_coprime
    {ι : Type*} [DecidableEq ι]
    {d x : ℕ} (hxd : x.Coprime d)
    (s : Finset ι) (a : ι → ℕ) (w : ι → ℂ) :
    ∑ i ∈ s, w i *
        ((if x ≡ a i [MOD d] then 1 else 0 : ℝ) : ℂ) =
      ∑ i ∈ s.filter (fun i => (a i).Coprime d), w i *
        ((if x ≡ a i [MOD d] then 1 else 0 : ℝ) : ℂ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hai : (a i).Coprime d
  · simp [hai]
  · have hmod : ¬x ≡ a i [MOD d] := by
      intro h
      have heq : (x : ZMod d) = (a i : ZMod d) :=
        (ZMod.natCast_eq_natCast_iff x (a i) d).2 h
      have hxunit : IsUnit (x : ZMod d) :=
        (ZMod.isUnit_iff_coprime x d).2 hxd
      have haunit : IsUnit (a i : ZMod d) := heq ▸ hxunit
      exact hai ((ZMod.isUnit_iff_coprime (a i) d).1 haunit)
    simp [hai, hmod]

/-- A Dirichlet character vanishes off the integers coprime to its level, so
filtering a finite character sum by coprimality does not change it. -/
theorem weighted_characterSum_filter_coprime
    {ι : Type*} [DecidableEq ι]
    {d : ℕ} (χ : DirichletCharacter ℂ d)
    (s : Finset ι) (a : ι → ℕ) (w : ι → ℂ) :
    ∑ i ∈ s.filter (fun i => (a i).Coprime d),
        w i * χ (a i : ZMod d) =
      ∑ i ∈ s, w i * χ (a i : ZMod d) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hai : (a i).Coprime d
  · simp [hai]
  · have hnonunit : ¬IsUnit (a i : ZMod d) := by
      intro haunit
      exact hai ((ZMod.isUnit_iff_coprime (a i) d).1 haunit)
    have hzero : χ (a i : ZMod d) = 0 :=
      MulChar.apply_eq_zero_iff.mpr hnonunit
    simp [hai, hzero]

/-- The finite-sum content of equation (6), before replacing imprimitive
characters by their primitive associates.  The principal term is restricted
to `(p₁p₂n,d)=1`; the character term may be summed over all triples because
Dirichlet characters vanish on the complementary set. -/
theorem smoothedM_equation_six
    {x d : ℕ} (hd : 0 < d) (hxd : x.Coprime d) :
    ∑ z ∈ smoothedMTriples x,
        (smoothedMKernel x z.1 z.2 : ℂ) *
          ((if x ≡ smoothedMArgument z [MOD d] then 1 else 0 : ℝ) : ℂ) =
      ((∑ z ∈ smoothedMGoodTriples x d,
          (smoothedMKernel x z.1 z.2 : ℂ)) +
        nontrivialCharSum d (fun χ =>
          χ (x : ZMod d)⁻¹ *
            ∑ z ∈ smoothedMTriples x,
              (smoothedMKernel x z.1 z.2 : ℂ) *
                χ (smoothedMArgument z : ZMod d))) /
        (Nat.totient d : ℂ) := by
  rw [weighted_residueSum_eq_filter_coprime hxd
    (smoothedMTriples x) smoothedMArgument
    (fun z => (smoothedMKernel x z.1 z.2 : ℂ))]
  rw [show (smoothedMTriples x).filter
      (fun z => (smoothedMArgument z).Coprime d) =
        smoothedMGoodTriples x d by rfl]
  rw [weighted_mappedResidueSum_eq_principal_add_nontrivial
    hd hxd (smoothedMGoodTriples x d) smoothedMArgument
    (fun z => smoothedMKernel x z.1 z.2)]
  · congr 3
    funext χ
    congr 1
    exact weighted_characterSum_filter_coprime χ
      (smoothedMTriples x) smoothedMArgument
      (fun z => (smoothedMKernel x z.1 z.2 : ℂ))
  · intro z hz
    exact (Finset.mem_filter.mp hz).2

/-- Flattening the nested `(p₁,p₂)` and `n` sums introduces no
multiplicity. -/
theorem sum_smoothedMTriples_eq_nested
    {R : Type*} [AddCommMonoid R]
    (x : ℕ) (f : (ℕ × ℕ) → ℕ → R) :
    ∑ z ∈ smoothedMTriples x, f z.1 z.2 =
      ∑ q ∈ chenPairs x, ∑ n ∈ smoothedMIndices x q, f q n := by
  simp only [smoothedMTriples, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp [smoothedMIndices]

/-- Kernel specialization of `sum_smoothedMTriples_eq_nested`. -/
theorem sum_smoothedMTriples_eq (x : ℕ) :
    ∑ z ∈ smoothedMTriples x, smoothedMKernel x z.1 z.2 =
      ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n :=
  sum_smoothedMTriples_eq_nested x (smoothedMKernel x)

/-- The principal mass is the full smoothed mass minus the bad-coprimality
mass `M₃`. -/
theorem smoothedMGoodMass_add_badMass (x d : ℕ) :
    smoothedMGoodMass x d + smoothedMBadMass x d =
      ∑ z ∈ smoothedMTriples x, smoothedMKernel x z.1 z.2 := by
  unfold smoothedMGoodMass smoothedMBadMass
  unfold smoothedMGoodTriples smoothedMBadTriples
  simpa only using Finset.sum_filter_add_sum_filter_not
    (s := smoothedMTriples x)
    (p := fun z => (smoothedMArgument z).Coprime d)
    (f := fun z => smoothedMKernel x z.1 z.2)

/-- For squarefree `d`, the pairs of divisors `(d₁,d₂)` with
`lcm(d₁,d₂)=d` are obtained by assigning each prime divisor to the left
factor, the right factor, or both. -/
theorem card_lcm_divisor_pairs {d : ℕ} (hd : Squarefree d) :
    ((d.divisors ×ˢ d.divisors).filter
      (fun q : ℕ × ℕ => q.1.lcm q.2 = d)).card =
        3 ^ distinctPrimeFactors d := by
  have homega :
      ArithmeticFunction.cardDistinctFactors d =
        distinctPrimeFactors d := by
    rw [distinctPrimeFactors,
      ArithmeticFunction.cardDistinctFactors_apply,
      ← List.card_toFinset, Nat.toFinset_factors]
  simpa [homega] using Nat.card_pair_lcm_eq hd

/-- The total absolute contribution of all sieve-weight pairs having lcm `d`
is at most `3^ν(d)`.  This is the finite combinatorial step used when the
paper passes from `M₄` to a sum indexed only by `d`. -/
theorem sum_abs_sieveWeight_lcm_le
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hdx : d.Coprime x) :
    ∑ q ∈ (d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
      |sieveWeight x ε q.1 * sieveWeight x ε q.2| ≤
        3 ^ distinctPrimeFactors d := by
  calc
    ∑ q ∈ (d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
      |sieveWeight x ε q.1 * sieveWeight x ε q.2| ≤
        ∑ _q ∈ (d.divisors ×ˢ d.divisors).filter
          (fun q : ℕ × ℕ => q.1.lcm q.2 = d), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqprod := (Finset.mem_filter.mp hq).1
      have hqdiv := Finset.mem_product.mp hqprod
      have hq1x : q.1.Coprime x :=
        Nat.Coprime.of_dvd_left
          (Nat.dvd_of_mem_divisors hqdiv.1) hdx
      have hq2x : q.2.Coprime x :=
        Nat.Coprime.of_dvd_left
          (Nat.dvd_of_mem_divisors hqdiv.2) hdx
      rw [abs_mul]
      have hq1 := abs_sieveWeight_le_one hx hx1 hε0 hq1x
      have hq2 := abs_sieveWeight_le_one hx hx1 hε0 hq2x
      nlinarith [abs_nonneg (sieveWeight x ε q.1),
        abs_nonneg (sieveWeight x ε q.2)]
    _ = (((d.divisors ×ˢ d.divisors).filter
          (fun q : ℕ × ℕ => q.1.lcm q.2 = d)).card : ℝ) := by
      simp
    _ = 3 ^ distinctPrimeFactors d := by
      exact_mod_cast card_lcm_divisor_pairs hd

/-- Absolute-value version of `sum_abs_sieveWeight_lcm_le`. -/
theorem abs_sum_sieveWeight_lcm_le
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hdx : d.Coprime x) :
    |∑ q ∈ (d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
      sieveWeight x ε q.1 * sieveWeight x ε q.2| ≤
        3 ^ distinctPrimeFactors d := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (sum_abs_sieveWeight_lcm_le hx hx1 hε0 hd hdx)

theorem abs_sieveLcmCoeff_le
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hdx : d.Coprime x) :
    |sieveLcmCoeff x ε d| ≤ 3 ^ distinctPrimeFactors d := by
  exact abs_sum_sieveWeight_lcm_le hx hx1 hε0 hd hdx

private theorem squarefree_lcm {a b : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (a.lcm b) := by
  rw [Nat.squarefree_iff_factorization_le_one
    (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
  exact sup_le (ha.natFactorization_le_one p)
    (hb.natFactorization_le_one p)

theorem sieveLcmCoeff_eq_zero_of_not_squarefree
    {x d : ℕ} {ε : ℝ} (hd : ¬Squarefree d) :
    sieveLcmCoeff x ε d = 0 := by
  unfold sieveLcmCoeff
  apply Finset.sum_eq_zero
  intro q hq
  have hlcm := (Finset.mem_filter.mp hq).2
  by_cases hq1 : sieveWeight x ε q.1 = 0
  · simp [hq1]
  by_cases hq2 : sieveWeight x ε q.2 = 0
  · simp [hq2]
  have hsq1 := sieveWeight_support_squarefree hq1
  have hsq2 := sieveWeight_support_squarefree hq2
  exact (hd (hlcm ▸ squarefree_lcm hsq1 hsq2)).elim

/-- Uniform version of the `3^ν(d)` coefficient bound.  The Möbius factor
records that the coefficient vanishes unless `d` is squarefree. -/
theorem abs_sieveLcmCoeff_le_moebius
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hdx : d.Coprime x) :
    |sieveLcmCoeff x ε d| ≤
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        3 ^ distinctPrimeFactors d := by
  by_cases hd : Squarefree d
  · have hmu :
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs,
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd]
      norm_num
    rw [hmu, one_mul]
    exact abs_sieveLcmCoeff_le hx hx1 hε0 hd hdx
  · rw [sieveLcmCoeff_eq_zero_of_not_squarefree hd, abs_zero,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num

private theorem sieve_coefficient_eq_primeFactors
    {d : ℕ} (hd : Squarefree d) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ) =
      ∏ p ∈ d.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
  have hmu :
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
    rw [← Int.cast_abs,
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd]
    norm_num
  rw [hmu, one_mul, distinctPrimeFactors,
    totient_cast_eq_prod_sub_one_of_squarefree hd]
  rw [← Finset.prod_const, Finset.prod_div_distrib]

private theorem prime_factor_decay_six
    {p : ℕ} (hp : p.Prime) :
    (3 : ℝ) / ((p : ℝ) - 1) ≤
      6 * (p : ℝ) ^ (-(5 : ℝ) / 6) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpowpos : 0 < (p : ℝ) ^ ((5 : ℝ) / 6) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hpowle : (p : ℝ) ^ ((5 : ℝ) / 6) ≤ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le hp1
      (by norm_num : (5 : ℝ) / 6 ≤ 1)
  have hden : 0 < (p : ℝ) - 1 :=
    sub_pos.mpr (lt_of_lt_of_le (by norm_num) hp2)
  rw [show -(5 : ℝ) / 6 = -((5 : ℝ) / 6) by ring,
    Real.rpow_neg (by positivity)]
  rw [← div_eq_mul_inv]
  exact (div_le_div_iff₀ hden hpowpos).2 (by nlinarith)

private theorem prime_factor_decay_one
    {p : ℕ} (hp : p.Prime) (hpbig : 46656 ≤ p) :
    (3 : ℝ) / ((p : ℝ) - 1) ≤
      (p : ℝ) ^ (-(5 : ℝ) / 6) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpbigR : (46656 : ℝ) ≤ p := by exact_mod_cast hpbig
  have hroot :
      (6 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 6) := by
    calc
      (6 : ℝ) =
          ((6 : ℝ) ^ (6 : ℕ)) ^ (((6 : ℕ) : ℝ)⁻¹) := by
        symm
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
      _ = (46656 : ℝ) ^ ((1 : ℝ) / 6) := by norm_num
      _ ≤ (p : ℝ) ^ ((1 : ℝ) / 6) :=
        Real.rpow_le_rpow (by positivity) hpbigR (by norm_num)
  have hmul :
      (p : ℝ) ^ ((5 : ℝ) / 6) *
          (p : ℝ) ^ ((1 : ℝ) / 6) = p := by
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have hpowpos : 0 < (p : ℝ) ^ ((5 : ℝ) / 6) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hthree :
      3 * (p : ℝ) ^ ((5 : ℝ) / 6) ≤ (p : ℝ) - 1 := by
    have hhalf :
        2 * (p : ℝ) ^ ((5 : ℝ) / 6) ≤ p := by
      nlinarith [mul_le_mul_of_nonneg_left hroot
        (show 0 ≤ (p : ℝ) ^ ((5 : ℝ) / 6) by positivity)]
    nlinarith
  have hden : 0 < (p : ℝ) - 1 :=
    sub_pos.mpr (lt_of_lt_of_le (by norm_num) hp2)
  rw [show -(5 : ℝ) / 6 = -((5 : ℝ) / 6) by ring,
    Real.rpow_neg (by positivity)]
  rw [← one_div]
  exact (div_le_div_iff₀ hden hpowpos).2 (by simpa using hthree)

/-- A uniform power-decay form of the elementary estimate
`|μ(d)|3^ν(d)/φ(d) ≪ d⁻⁵⁄⁶`.  The explicit constant is immaterial; the
finite set of primes below `6⁶` is absorbed into `6^(6⁶)`. -/
theorem sieveCoefficient_le_decay
    {d : ℕ} (hd : Squarefree d) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        (d : ℝ) ^ (-(5 : ℝ) / 6) := by
  rw [sieve_coefficient_eq_primeFactors hd]
  let e : ℝ := -(5 : ℝ) / 6
  let small : Finset ℕ := d.primeFactors.filter (· < 46656)
  have hterm :
      ∀ p ∈ d.primeFactors,
        (3 : ℝ) / ((p : ℝ) - 1) ≤
          (if p < 46656 then 6 else 1) * (p : ℝ) ^ e := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    by_cases hpsmall : p < 46656
    · simpa [e, hpsmall] using prime_factor_decay_six hpprime
    · have hpbig : 46656 ≤ p := by omega
      simpa [e, hpsmall] using prime_factor_decay_one hpprime hpbig
  have hprod :
      ∏ p ∈ d.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) ≤
        ∏ p ∈ d.primeFactors,
          (if p < 46656 then 6 else 1) * (p : ℝ) ^ e := by
    apply Finset.prod_le_prod
    · intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact div_nonneg (by norm_num) (sub_nonneg.mpr (by
        exact_mod_cast hpprime.one_le))
    · exact hterm
  have hsmallcard : small.card ≤ 46656 := by
    calc
      small.card ≤ (Finset.range 46656).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = 46656 := Finset.card_range _
  have hsmallpow :
      (6 : ℝ) ^ small.card ≤ (6 : ℝ) ^ (46656 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by exact_mod_cast hsmallcard)
  have hfactor :
      ∏ p ∈ d.primeFactors,
          (if p < 46656 then (6 : ℝ) else 1) =
        (6 : ℝ) ^ small.card := by
    simp [small, Finset.prod_ite]
  have hrpow :
      ∏ p ∈ d.primeFactors, (p : ℝ) ^ e = (d : ℝ) ^ e := by
    have hcast :
        (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
      simpa only [Nat.cast_prod] using
        congrArg (fun n : ℕ => (n : ℝ))
          (Nat.prod_primeFactors_of_squarefree hd)
    calc
      (∏ p ∈ d.primeFactors, (p : ℝ) ^ e) =
          (∏ p ∈ d.primeFactors, (p : ℝ)) ^ e := by
        apply Real.finsetProd_rpow
        intro p hp
        positivity
      _ = (d : ℝ) ^ e := by rw [hcast]
  calc
    (∏ p ∈ d.primeFactors, (3 : ℝ) / ((p : ℝ) - 1)) ≤
        ∏ p ∈ d.primeFactors,
          (if p < 46656 then 6 else 1) * (p : ℝ) ^ e := hprod
    _ = (∏ p ∈ d.primeFactors,
          (if p < 46656 then (6 : ℝ) else 1)) *
        ∏ p ∈ d.primeFactors, (p : ℝ) ^ e := by
      rw [Finset.prod_mul_distrib]
    _ = (6 : ℝ) ^ small.card * (d : ℝ) ^ e := by
      rw [hfactor, hrpow]
    _ ≤ (6 : ℝ) ^ (46656 : ℝ) * (d : ℝ) ^ e := by
      exact mul_le_mul_of_nonneg_right hsmallpow (by positivity)
    _ = (6 : ℝ) ^ (46656 : ℝ) *
        (d : ℝ) ^ (-(5 : ℝ) / 6) := by rfl

/-- Uniform version of `sieveCoefficient_le_decay`; when `d` is not
squarefree the Möbius factor makes the left side zero. -/
theorem sieveCoefficient_le_decay_uniform (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ) ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        (d : ℝ) ^ (-(5 : ℝ) / 6) := by
  by_cases hd : Squarefree d
  · exact sieveCoefficient_le_decay hd
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
    positivity

/-- The reciprocal sum over positive multiples of `p` up to `x`, expressed
by scaling the harmonic sum. -/
theorem sum_inv_multiples (x p : ℕ) (hp : 0 < p) :
    ∑ d ∈ (Finset.Icc 1 x).filter (p ∣ ·), (d : ℝ)⁻¹ =
      (p : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (x / p), (k : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun d _ => d / p) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdIcc, hpd⟩
    rcases hpd with ⟨k, rfl⟩
    simp only [Finset.mem_Icc] at hdIcc ⊢
    have hkpos : 0 < k := by
      by_contra hk
      simp only [not_lt, nonpos_iff_eq_zero] at hk
      simp [hk] at hdIcc
    rw [Nat.mul_div_cancel_left _ hp]
    constructor
    · exact hkpos
    · exact (Nat.le_div_iff_mul_le hp).2 (by
        simpa [mul_comm] using hdIcc.2)
  · intro d hd e he hde
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, hk⟩
    rcases (Finset.mem_filter.mp he).2 with ⟨l, hl⟩
    subst d
    subst e
    simpa [Nat.mul_div_cancel_left _ hp] using congrArg (p * ·) hde
  · intro k hk
    have hkIcc := Finset.mem_Icc.mp hk
    refine ⟨p * k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero hp.ne' (by omega))
        · simpa [mul_comm] using
            (Nat.le_div_iff_mul_le hp).1 hkIcc.2
      · exact dvd_mul_right p k
    · simp [Nat.mul_div_cancel_left _ hp]
  · intro d hd
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left _ hp]
    rw [Nat.cast_mul, mul_inv]

/-- Summing the coefficient decay over moduli divisible by a fixed prime
costs only `x^(1/12)` and one harmonic factor. -/
theorem sum_sieveModuli_decay_of_dvd
    {x p : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hp : 0 < p)
    (hε : 0 ≤ ε) :
    ∑ d ∈ (sieveModuli x ε).filter (p ∣ ·),
        (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
      (x : ℝ) ^ ((1 : ℝ) / 12) * (p : ℝ)⁻¹ *
        (harmonic x : ℝ) := by
  let S := (sieveModuli x ε).filter (p ∣ ·)
  let T := (Finset.Icc 1 x).filter (p ∣ ·)
  have hx1R : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hpoint :
      ∀ d ∈ S,
        (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
          (x : ℝ) ^ ((1 : ℝ) / 12) * (d : ℝ)⁻¹ := by
    intro d hd
    have hdmod := (Finset.mem_filter.mp hd).1
    have hddata := (Finset.mem_filter.mp hdmod).2
    have hdpos : 0 < d := by omega
    have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hdcut :
        (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
      hddata.2.2
    have hdpow :
        (d : ℝ) ^ ((1 : ℝ) / 6) ≤
          (x : ℝ) ^ ((1 : ℝ) / 12) := by
      calc
        (d : ℝ) ^ ((1 : ℝ) / 6) ≤
            ((x : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^
              ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by positivity) hdcut (by norm_num)
        _ = (x : ℝ) ^ (((1 : ℝ) / 2 - ε) *
              ((1 : ℝ) / 6)) := by
          rw [← Real.rpow_mul (by positivity)]
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := by
          apply Real.rpow_le_rpow_of_exponent_le hx1R
          nlinarith
    rw [show -(5 : ℝ) / 6 = (1 : ℝ) / 6 + (-1) by ring,
      Real.rpow_add hdposR, Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_right hdpow (by positivity)
  have hST : S ⊆ T := by
    intro d hd
    have hdmod := (Finset.mem_filter.mp hd).1
    have hpd := (Finset.mem_filter.mp hd).2
    have hddata := Finset.mem_filter.mp hdmod
    have hdrange := Finset.mem_range.mp hddata.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hddata.2.1, by omega⟩, hpd⟩
  have hsumS :
      ∑ d ∈ S, (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
        (x : ℝ) ^ ((1 : ℝ) / 12) *
          ∑ d ∈ S, (d : ℝ)⁻¹ := by
    calc
      ∑ d ∈ S, (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
          ∑ d ∈ S,
            (x : ℝ) ^ ((1 : ℝ) / 12) * (d : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro d hd
        exact hpoint d hd
      _ = (x : ℝ) ^ ((1 : ℝ) / 12) *
          ∑ d ∈ S, (d : ℝ)⁻¹ := by rw [Finset.mul_sum]
  have hsumST :
      ∑ d ∈ S, (d : ℝ)⁻¹ ≤ ∑ d ∈ T, (d : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hST
    intro d hdT hdS
    positivity
  have hharmonic :
      ∑ k ∈ Finset.Icc 1 (x / p), (k : ℝ)⁻¹ ≤
        (harmonic x : ℝ) := by
    have hharmX :
        ∑ k ∈ Finset.Icc 1 x, (k : ℝ)⁻¹ =
          (harmonic x : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
    rw [← hharmX]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc_right (Nat.div_le_self x p)
    · intro k hk hk'
      positivity
  change (∑ d ∈ S, (d : ℝ) ^ (-(5 : ℝ) / 6)) ≤ _
  calc
    (∑ d ∈ S, (d : ℝ) ^ (-(5 : ℝ) / 6)) ≤
        (x : ℝ) ^ ((1 : ℝ) / 12) *
          ∑ d ∈ S, (d : ℝ)⁻¹ := hsumS
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 12) *
          ∑ d ∈ T, (d : ℝ)⁻¹ := by gcongr
    _ = (x : ℝ) ^ ((1 : ℝ) / 12) * (p : ℝ)⁻¹ *
          ∑ k ∈ Finset.Icc 1 (x / p), (k : ℝ)⁻¹ := by
      rw [show (∑ d ∈ T, (d : ℝ)⁻¹) =
          (p : ℝ)⁻¹ *
            ∑ k ∈ Finset.Icc 1 (x / p), (k : ℝ)⁻¹ by
        exact sum_inv_multiples x p hp]
      ring
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 12) * (p : ℝ)⁻¹ *
          (harmonic x : ℝ) := by gcongr

/-- Union-bound form of `sum_sieveModuli_decay_of_dvd`: failure of
coprimality is covered by the prime divisors of the fixed integer `a`. -/
theorem sum_sieveModuli_decay_not_coprime_le
    {x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (ha : a ≠ 0)
    (hε : 0 ≤ ε) :
    ∑ d ∈ (sieveModuli x ε).filter (fun d => ¬a.Coprime d),
        (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
      (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
        ∑ p ∈ a.primeFactors, (p : ℝ)⁻¹ := by
  let D := sieveModuli x ε
  let B := D.filter (fun d => ¬a.Coprime d)
  let W : ℕ → ℝ := fun d => (d : ℝ) ^ (-(5 : ℝ) / 6)
  have hbad :
      ∀ d ∈ B, W d ≤
        ∑ p ∈ a.primeFactors, if p ∣ d then W d else 0 := by
    intro d hd
    have hdcop : ¬a.Coprime d := (Finset.mem_filter.mp hd).2
    have hgcd : a.gcd d ≠ 1 := by
      simpa [Nat.coprime_iff_gcd_eq_one] using hdcop
    obtain ⟨p, hpprime, hpgcd⟩ :=
      Nat.ne_one_iff_exists_prime_dvd.mp hgcd
    have hpa : p ∣ a := hpgcd.trans (Nat.gcd_dvd_left a d)
    have hpd : p ∣ d := hpgcd.trans (Nat.gcd_dvd_right a d)
    have hpmem : p ∈ a.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, hpa, ha⟩
    calc
      W d = if p ∣ d then W d else 0 := by simp [hpd]
      _ ≤ ∑ r ∈ a.primeFactors,
          if r ∣ d then W d else 0 := by
        exact Finset.single_le_sum
          (s := a.primeFactors)
          (f := fun r => if r ∣ d then W d else 0)
          (fun r hr => by positivity) hpmem
  have hunion :
      ∑ d ∈ B, W d ≤
        ∑ p ∈ a.primeFactors,
          ∑ d ∈ D.filter (p ∣ ·), W d := by
    calc
      ∑ d ∈ B, W d ≤
          ∑ d ∈ B, ∑ p ∈ a.primeFactors,
            if p ∣ d then W d else 0 := by
        apply Finset.sum_le_sum
        intro d hd
        exact hbad d hd
      _ ≤ ∑ d ∈ D, ∑ p ∈ a.primeFactors,
            if p ∣ d then W d else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro d hdD hdB
          positivity
      _ = ∑ p ∈ a.primeFactors,
          ∑ d ∈ D.filter (p ∣ ·), W d := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_filter]
  have hprime :
      ∀ p ∈ a.primeFactors,
        ∑ d ∈ D.filter (p ∣ ·), W d ≤
          (x : ℝ) ^ ((1 : ℝ) / 12) * (p : ℝ)⁻¹ *
            (harmonic x : ℝ) := by
    intro p hp
    exact sum_sieveModuli_decay_of_dvd hx1
      (Nat.prime_of_mem_primeFactors hp).pos hε
  change (∑ d ∈ B, W d) ≤ _
  calc
    (∑ d ∈ B, W d) ≤
        ∑ p ∈ a.primeFactors,
          ∑ d ∈ D.filter (p ∣ ·), W d := hunion
    _ ≤ ∑ p ∈ a.primeFactors,
          ((x : ℝ) ^ ((1 : ℝ) / 12) * (p : ℝ)⁻¹ *
            (harmonic x : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hprime p hp
    _ = (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
          ∑ p ∈ a.primeFactors, (p : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- A prime power contributes only its base prime to the prime-factor sum;
possible coincidences with `p₁` or `p₂` can only decrease the union sum. -/
theorem sum_inv_primeFactors_mul_primePow_le
    {p₁ p₂ p k : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hp : p.Prime) (hk : 0 < k) :
    ∑ r ∈ (p₁ * p₂ * p ^ k).primeFactors, (r : ℝ)⁻¹ ≤
      (p₁ : ℝ)⁻¹ + (p₂ : ℝ)⁻¹ + (p : ℝ)⁻¹ := by
  rw [Nat.primeFactors_mul
      (mul_ne_zero hp₁.ne_zero hp₂.ne_zero) (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_mul hp₁.ne_zero hp₂.ne_zero,
    hp₁.primeFactors, hp₂.primeFactors,
    Nat.primeFactors_prime_pow hk.ne' hp]
  have hunion :
      ∀ s t : Finset ℕ,
        (∑ r ∈ s ∪ t, (r : ℝ)⁻¹) ≤
          (∑ r ∈ s, (r : ℝ)⁻¹) + ∑ r ∈ t, (r : ℝ)⁻¹ := by
    intro s t
    have h := Finset.sum_union_inter
      (s₁ := s) (s₂ := t) (f := fun r : ℕ => (r : ℝ)⁻¹)
    have hnonneg :
        0 ≤ ∑ r ∈ s ∩ t, (r : ℝ)⁻¹ := by positivity
    linarith
  calc
    (∑ r ∈ {p₁, p₂} ∪ {p}, (r : ℝ)⁻¹) ≤
        (∑ r ∈ {p₁, p₂}, (r : ℝ)⁻¹) +
          ∑ r ∈ {p}, (r : ℝ)⁻¹ := hunion _ _
    _ ≤ ((∑ r ∈ {p₁}, (r : ℝ)⁻¹) +
          ∑ r ∈ {p₂}, (r : ℝ)⁻¹) +
          ∑ r ∈ {p}, (r : ℝ)⁻¹ := by
      gcongr
      simpa only [Finset.singleton_union] using
        (hunion ({p₁} : Finset ℕ) ({p₂} : Finset ℕ))
    _ = (p₁ : ℝ)⁻¹ + (p₂ : ℝ)⁻¹ + (p : ℝ)⁻¹ := by simp

/-- Weighted form of `sum_inv_primeFactors_mul_primePow_le`.  If `Λ(n)` is
nonzero, `n` is a prime power and its unique prime divisor is `minFac n`. -/
theorem vonMangoldt_mul_sum_inv_primeFactors_le
    {q : ℕ × ℕ} {n : ℕ} (hq₁ : q.1.Prime) (hq₂ : q.2.Prime) :
    ArithmeticFunction.vonMangoldt n *
        (∑ p ∈ (q.1 * q.2 * n).primeFactors, (p : ℝ)⁻¹) ≤
      ArithmeticFunction.vonMangoldt n *
        ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹ + (n.minFac : ℝ)⁻¹) := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · have hnpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hnpp
    have hsum := sum_inv_primeFactors_mul_primePow_le hq₁ hq₂ hp hk
    have hminfac : (p ^ k).minFac = p := by
      rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
    rw [hminfac]
    exact mul_le_mul_of_nonneg_left hsum
      ArithmeticFunction.vonMangoldt_nonneg

private theorem primePow_exponent_le
    {p k x : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hx : 2 ≤ x) (hpk : p ^ k ≤ x) :
    k ≤ ⌈Real.log x / Real.log 2⌉₊ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hxR : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ≤ Real.log p :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr hpR)
      (by exact_mod_cast hp.two_le)
  have hlogpow :
      Real.log ((p ^ k : ℕ) : ℝ) =
        (k : ℝ) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlogs :
      (k : ℝ) * Real.log 2 ≤ Real.log x := by
    calc
      (k : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log p := by gcongr
      _ = Real.log ((p ^ k : ℕ) : ℝ) := hlogpow.symm
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by exact_mod_cast pow_pos hp.pos k))
        (Set.mem_Ioi.mpr hxR) (by exact_mod_cast hpk)
  have hkR :
      (k : ℝ) ≤ Real.log x / Real.log 2 :=
    (le_div_iff₀ hlog2).2 hlogs
  exact_mod_cast hkR.trans (Nat.le_ceil _)

/-- Elementary prime-power estimate, with no prime number theorem:
`Σ_{n≤x} Λ(n)/minFac(n)` is bounded by an exponent count times
`log x · H_x`. -/
theorem sum_vonMangoldt_div_minFac_le
    {x : ℕ} (hx : 2 ≤ x) :
    ∑ n ∈ (Finset.Icc 2 x).filter IsPrimePow,
        ArithmeticFunction.vonMangoldt n * (n.minFac : ℝ)⁻¹ ≤
      (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
        Real.log x * (harmonic x : ℝ) := by
  let K : ℕ := ⌈Real.log x / Real.log 2⌉₊
  let S : Finset ℕ := (Finset.Icc 2 x).filter IsPrimePow
  let enc : ℕ → ℕ × ℕ :=
    fun n => (n.minFac, n.factorization n.minFac)
  let box : Finset (ℕ × ℕ) :=
    Finset.Icc 2 x ×ˢ Finset.Icc 1 K
  let T : Finset (ℕ × ℕ) := S.image enc
  let g : ℕ × ℕ → ℝ :=
    fun z => Real.log x * (z.1 : ℝ)⁻¹
  have henc : ∀ n ∈ S, enc n ∈ box := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnIcc := Finset.mem_Icc.mp hn'.1
    have hnpp : IsPrimePow n := hn'.2
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hp : n.minFac.Prime := Nat.minFac_prime hn1
    have hk : 0 < n.factorization n.minFac :=
      hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
    have hp_le_n : n.minFac ≤ n :=
      Nat.minFac_le (by omega)
    have hk_le :
        n.factorization n.minFac ≤ K := by
      apply primePow_exponent_le hp hk hx
      rw [hnpp.minFac_pow_factorization_eq]
      exact hnIcc.2
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr
        ⟨hp.two_le, hp_le_n.trans hnIcc.2⟩
    · exact Finset.mem_Icc.mpr ⟨hk, hk_le⟩
  have hencinj :
      ∀ n ∈ S, ∀ m ∈ S, enc n = enc m → n = m := by
    intro n hn m hm h
    have hnpp : IsPrimePow n := (Finset.mem_filter.mp hn).2
    have hmpp : IsPrimePow m := (Finset.mem_filter.mp hm).2
    have h1 : n.minFac = m.minFac := congrArg Prod.fst h
    have h2 :
        n.factorization n.minFac =
          m.factorization m.minFac := congrArg Prod.snd h
    calc
      n = n.minFac ^ n.factorization n.minFac :=
        hnpp.minFac_pow_factorization_eq.symm
      _ = m.minFac ^ m.factorization m.minFac :=
        congrArg₂ (fun a b : ℕ => a ^ b) h1 h2
      _ = m := hmpp.minFac_pow_factorization_eq
  have hTbox : T ⊆ box := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
    exact henc n hn
  have hpoint :
      ∀ n ∈ S,
        ArithmeticFunction.vonMangoldt n * (n.minFac : ℝ)⁻¹ ≤
          g (enc n) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnIcc := Finset.mem_Icc.mp hn'.1
    have hnpp : IsPrimePow n := hn'.2
    have hn1 : n ≠ 1 := by omega
    have hp : n.minFac.Prime := Nat.minFac_prime hn1
    have hp_le_n : n.minFac ≤ n := Nat.minFac_le (by omega)
    have hlog :
        Real.log n.minFac ≤ Real.log x :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by exact_mod_cast hp.pos))
        (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < x)))
        (by exact_mod_cast hp_le_n.trans hnIcc.2)
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hnpp]
    exact mul_le_mul_of_nonneg_right hlog (by positivity)
  have hsum_image :
      ∑ n ∈ S, g (enc n) = ∑ z ∈ T, g z := by
    apply Finset.sum_bij (fun n _ => enc n)
    · intro n hn
      exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
    · intro n hn m hm
      exact hencinj n hn m hm
    · intro z hz
      rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
    · intro n hn
      rfl
  have hsum_box :
      ∑ z ∈ T, g z ≤ ∑ z ∈ box, g z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hTbox
    intro z hzbox hzT
    dsimp only [g]
    positivity
  have hharm :
      ∑ p ∈ Finset.Icc 2 x, (p : ℝ)⁻¹ ≤
        (harmonic x : ℝ) := by
    have hharmX :
        ∑ p ∈ Finset.Icc 1 x, (p : ℝ)⁻¹ =
          (harmonic x : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
    rw [← hharmX]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc_left (by omega)
    · intro p hp hp'
      positivity
  change (∑ n ∈ S,
      ArithmeticFunction.vonMangoldt n * (n.minFac : ℝ)⁻¹) ≤ _
  calc
    (∑ n ∈ S,
        ArithmeticFunction.vonMangoldt n * (n.minFac : ℝ)⁻¹) ≤
        ∑ n ∈ S, g (enc n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hpoint n hn
    _ = ∑ z ∈ T, g z := hsum_image
    _ ≤ ∑ z ∈ box, g z := hsum_box
    _ = (K : ℝ) * Real.log x *
          ∑ p ∈ Finset.Icc 2 x, (p : ℝ)⁻¹ := by
      simp only [box, g, Finset.sum_product]
      calc
        (∑ p ∈ Finset.Icc 2 x, ∑ k ∈ Finset.Icc 1 K,
            Real.log x * (p : ℝ)⁻¹) =
            ∑ p ∈ Finset.Icc 2 x,
              (K : ℝ) * (Real.log x * (p : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp
        _ = (K : ℝ) * Real.log x *
              ∑ p ∈ Finset.Icc 2 x, (p : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ ≤ (K : ℝ) * Real.log x * (harmonic x : ℝ) := by
      gcongr

/-- The same prime-power estimate on any one of the smoothed `n`-index
sets. -/
theorem sum_smoothedMIndices_vonMangoldt_div_minFac_le
    {x : ℕ} (hx : 2 ≤ x) (q : ℕ × ℕ) :
    ∑ n ∈ smoothedMIndices x q,
        ArithmeticFunction.vonMangoldt n * (n.minFac : ℝ)⁻¹ ≤
      (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
        Real.log x * (harmonic x : ℝ) := by
  let S := smoothedMIndices x q
  let P := (Finset.Icc 2 x).filter IsPrimePow
  let f : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n * (n.minFac : ℝ)⁻¹
  have heq :
      ∑ n ∈ S, f n = ∑ n ∈ S.filter IsPrimePow, f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hpp : IsPrimePow n
    · simp [hpp]
    · rw [if_neg hpp]
      simp [f, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  have hsubset : S.filter IsPrimePow ⊆ P := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hnpp := (Finset.mem_filter.mp hn).2
    have hnrange : n < x + 1 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hnS).1
    have hn2 : 2 ≤ n := by
      by_contra h
      interval_cases n <;>
        simp_all [not_isPrimePow_zero, not_isPrimePow_one]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hn2, by omega⟩, hnpp⟩
  rw [heq]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun n hnP hnS => by
      dsimp only [f]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (inv_nonneg.mpr (Nat.cast_nonneg _)))).trans
    (sum_vonMangoldt_div_minFac_le hx)

/-- Crude Chebyshev-free bound for the total von Mangoldt mass in a
smoothed interval. -/
theorem sum_smoothedMIndices_vonMangoldt_le
    {x : ℕ} (hx : 2 ≤ x) (q : ℕ × ℕ) :
    ∑ n ∈ smoothedMIndices x q,
        ArithmeticFunction.vonMangoldt n ≤
      ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) * Real.log x := by
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  let S := smoothedMIndices x q
  have hY0 : 0 ≤ Y := by positivity
  have hcardNat : S.card ≤ ⌈Y⌉₊ + 1 := by
    calc
      S.card ≤ (Finset.range (⌈Y⌉₊ + 1)).card := by
        apply Finset.card_le_card
        intro n hn
        apply Finset.mem_range.mpr
        have hnY : (n : ℝ) ≤ Y :=
          (Finset.mem_filter.mp hn).2
        have hnceil : n ≤ ⌈Y⌉₊ := by
          exact_mod_cast hnY.trans (Nat.le_ceil Y)
        omega
      _ = ⌈Y⌉₊ + 1 := Finset.card_range _
  have hcard :
      (S.card : ℝ) ≤ Y + 2 := by
    apply le_of_lt
    calc
      (S.card : ℝ) ≤ (⌈Y⌉₊ + 1 : ℕ) := by exact_mod_cast hcardNat
      _ = (⌈Y⌉₊ : ℝ) + 1 := by norm_num
      _ < (Y + 1) + 1 := by
        gcongr
        exact Nat.ceil_lt_add_one hY0
      _ = Y + 2 := by ring
  have hlog0 : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hterm :
      ∀ n ∈ S,
        ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
    intro n hn
    have hnrange : n < x + 1 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    by_cases hn0 : n = 0
    · simp [hn0, hlog0]
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0))
          (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < x)))
          (by exact_mod_cast (by omega : n ≤ x)))
  change (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) ≤ _
  calc
    (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) ≤
        ∑ _n ∈ S, Real.log x := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n hn
    _ = (S.card : ℝ) * Real.log x := by simp
    _ ≤ (Y + 2) * Real.log x :=
      mul_le_mul_of_nonneg_right hcard hlog0

/-- Abstract finite form of the `M₄` regrouping estimate. Any nonnegative
remainder term indexed by `d` may be pulled through the sieve coefficient and
majorized by the paper's factor `|μ(d)| 3^ν(d) / φ(d)`. -/
theorem abs_sum_sieveLcmCoeff_div_totient_le
    {x : ℕ} {ε : ℝ} (D : Finset ℕ) (F : ℕ → ℝ)
    (hx : Even x) (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d.Coprime x) :
    |∑ d ∈ D, sieveLcmCoeff x ε d / (Nat.totient d : ℝ) * F d| ≤
      ∑ d ∈ D,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) * |F d| := by
  calc
    |∑ d ∈ D,
        sieveLcmCoeff x ε d / (Nat.totient d : ℝ) * F d| ≤
        ∑ d ∈ D,
          |sieveLcmCoeff x ε d / (Nat.totient d : ℝ) * F d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) * |F d| := by
      apply Finset.sum_le_sum
      intro d hd
      have hddata := hD d hd
      have hcoeff :=
        abs_sieveLcmCoeff_le_moebius hx hx1 hε0 hddata.2
      have hφ : 0 ≤ (Nat.totient d : ℝ) := by positivity
      rw [abs_mul, abs_div, abs_of_nonneg hφ]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hcoeff hφ) (abs_nonneg _)

/-- The signed remainder `M₃` is bounded by its positive
`|μ(d)|3^ν(d)/φ(d)` majorant. -/
theorem abs_mThree_le_majorant
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) :
    |mThree x ε| ≤ mThreeMajorant x ε := by
  unfold mThree mThreeMajorant
  apply abs_sum_sieveLcmCoeff_div_totient_le
      (D := sieveModuli x ε) (F := smoothedMBadMass x)
      hx hx1 hε0
  intro d hd
  exact ⟨(Finset.mem_filter.mp hd).2.1,
    (Finset.mem_filter.mp hd).2.2.1⟩

/-- Since each nonzero sieve weight is supported on
`dᵢ ≤ x^(1/4-ε/2)`, their lcm is supported on
`d ≤ x^(1/2-ε)`. -/
theorem sieveLcmCoeff_eq_zero_of_cutoff
    {x d : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : ε ≤ 1 / 2)
    (hdcut : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) < d) :
    sieveLcmCoeff x ε d = 0 := by
  unfold sieveLcmCoeff
  apply Finset.sum_eq_zero
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hqdiv := Finset.mem_product.mp hq'.1
  by_cases hq1zero : sieveWeight x ε q.1 = 0
  · simp [hq1zero]
  by_cases hq2zero : sieveWeight x ε q.2 = 0
  · simp [hq2zero]
  have hexp0 : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
  have hx1r : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hRone :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) :=
    Real.one_le_rpow hx1r hexp0
  have hq1cut :
      (q.1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases sieveWeight_support hq1zero with hq1 | hq1
    · simpa only [hq1, Nat.cast_one, one_div] using hRone
    · exact hq1
  have hq2cut :
      (q.2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases sieveWeight_support hq2zero with hq2 | hq2
    · simpa only [hq2, Nat.cast_one, one_div] using hRone
    · exact hq2
  have hdposR : (0 : ℝ) < d :=
    (Real.rpow_nonneg (by positivity) _).trans_lt hdcut
  have hdpos : 0 < d := by exact_mod_cast hdposR
  have hq1pos : 0 < q.1 :=
    Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hqdiv.1) hdpos
  have hq2pos : 0 < q.2 :=
    Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hqdiv.2) hdpos
  have hlcmle : q.1.lcm q.2 ≤ q.1 * q.2 :=
    Nat.lcm_le_mul hq1pos hq2pos
  have hprod :
      ((q.1 * q.2 : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    norm_num only [Nat.cast_mul]
    exact mul_le_mul hq1cut hq2cut (by positivity) (by positivity)
  have hpow :
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) =
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hdle :
      (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    calc
      (d : ℝ) = (q.1.lcm q.2 : ℕ) := by
        exact_mod_cast hq'.2.symm
      _ ≤ (q.1 * q.2 : ℕ) := by exact_mod_cast hlcmle
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := hprod
      _ = (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hpow
  exact (not_lt_of_ge hdle hdcut).elim

/-! ### The elementary `Ω → M` reduction -/

theorem omegaSmallThirdPrimes_card_le
    (x : ℕ) (ε : ℝ) (q : ℕ × ℕ) :
    (omegaSmallThirdPrimes x ε q).card ≤
      ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊ := by
  calc
    (omegaSmallThirdPrimes x ε q).card ≤
        (Finset.range
          ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_range]
      apply Nat.lt_ceil.mpr
      exact (Finset.mem_filter.mp hp).2
    _ = ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊ := by
      simp

theorem sieveMSmallTail_le_majorant (x : ℕ) (ε : ℝ) :
    sieveMSmallTail x ε ≤ sieveMSmallMajorant x ε := by
  unfold sieveMSmallTail sieveMSmallMajorant
  apply Finset.sum_le_sum
  intro q _
  exact omegaSmallThirdPrimes_card_le x ε q

theorem sieveMSmallMajorant_cast_le (x : ℕ) (ε : ℝ) :
    (sieveMSmallMajorant x ε : ℝ) ≤
      ∑ q ∈ chenPairs x,
        (((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) + 1) := by
  unfold sieveMSmallMajorant
  simp only [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro q _
  exact (Nat.ceil_lt_add_one
    (Real.rpow_nonneg (by positivity) _)).le

private theorem inv_rpow_one_sub
    {a ε : ℝ} (ha : 0 < a) :
    (a ^ (1 - ε))⁻¹ = a ^ ε * a⁻¹ := by
  calc
    (a ^ (1 - ε))⁻¹ = a ^ (-(1 - ε)) :=
      (Real.rpow_neg ha.le (1 - ε)).symm
    _ = a ^ (ε - 1) := by ring_nf
    _ = a ^ ε / a ^ (1 : ℝ) := Real.rpow_sub ha ε 1
    _ = a ^ ε * a⁻¹ := by rw [Real.rpow_one, div_eq_mul_inv]

private theorem quotient_rpow_le_harmonicKernel
    {x a b ε : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b)
    (hε : 0 ≤ ε) (haX : a ≤ x ^ ((1 : ℝ) / 3))
    (hbX : b ≤ x ^ ((1 : ℝ) / 2)) :
    (x / (a * b)) ^ (1 - ε) ≤
      x ^ (1 - ε / 6) * a⁻¹ * b⁻¹ := by
  have haε : a ^ ε ≤ x ^ (ε / 3) := by
    calc
      a ^ ε ≤ (x ^ ((1 : ℝ) / 3)) ^ ε :=
        Real.rpow_le_rpow ha.le haX hε
      _ = x ^ (ε / 3) := by
        rw [← Real.rpow_mul hx.le]
        congr 1
        ring_nf
  have hbε : b ^ ε ≤ x ^ (ε / 2) := by
    calc
      b ^ ε ≤ (x ^ ((1 : ℝ) / 2)) ^ ε :=
        Real.rpow_le_rpow hb.le hbX hε
      _ = x ^ (ε / 2) := by
        rw [← Real.rpow_mul hx.le]
        congr 1
        ring_nf
  rw [Real.div_rpow hx.le (mul_nonneg ha.le hb.le),
    Real.mul_rpow ha.le hb.le, div_eq_mul_inv,
    mul_inv, inv_rpow_one_sub ha, inv_rpow_one_sub hb]
  calc
    x ^ (1 - ε) * (a ^ ε * a⁻¹ * (b ^ ε * b⁻¹)) =
        x ^ (1 - ε) * a ^ ε * b ^ ε * a⁻¹ * b⁻¹ := by ring
    _ ≤ x ^ (1 - ε) * x ^ (ε / 3) * x ^ (ε / 2) *
          a⁻¹ * b⁻¹ := by
      gcongr
    _ = x ^ (1 - ε / 6) * a⁻¹ * b⁻¹ := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 2
      ring_nf

theorem pairQuotient_rpow_le_harmonicKernel
    {x : ℕ} {q : ℕ × ℕ} {ε : ℝ}
    (hq : q ∈ chenPairs x) (hε : 0 ≤ ε) :
    ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) ≤
      (x : ℝ) ^ (1 - ε / 6) * (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with ⟨hp₁, hp₂, _hp₁lo, hp₁hi, _hp₂lo, hp₂hi⟩
  have hq₁range : q.1 < x + 1 := hq'.1.1
  have hp₁two : 2 ≤ q.1 := hp₁.two_le
  have hxnat : 0 < x := by omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxnat
  have hp₁pos : (0 : ℝ) < q.1 := by exact_mod_cast hp₁.pos
  have hp₂pos : (0 : ℝ) < q.2 := by exact_mod_cast hp₂.pos
  have hp₁one : (1 : ℝ) ≤ q.1 := by exact_mod_cast hp₁.one_le
  have hdiv : (x : ℝ) / q.1 ≤ x :=
    div_le_self (by positivity) hp₁one
  have hp₂sqrt :
      (q.2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    hp₂hi.trans <|
      Real.rpow_le_rpow (by positivity) hdiv (by norm_num)
  exact quotient_rpow_le_harmonicKernel
    hxpos hp₁pos hp₂pos hε hp₁hi hp₂sqrt

theorem sum_pairQuotient_rpow_le_harmonic
    (x : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∑ q ∈ chenPairs x,
        ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) ≤
      (x : ℝ) ^ (1 - ε / 6) * (harmonic x : ℝ) ^ 2 := by
  let box : Finset (ℕ × ℕ) :=
    Finset.Icc 1 x ×ˢ Finset.Icc 1 x
  have hsubset : chenPairs x ⊆ box := by
    intro q hq
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    rcases hq'.2 with ⟨hp₁, hp₂, _⟩
    simp only [box, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hp₁.one_le, by omega⟩, ⟨hp₂.one_le, by omega⟩⟩
  have hharm :
      ∑ i ∈ Finset.Icc 1 x, ((i : ℝ)⁻¹) =
        (harmonic x : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
  calc
    ∑ q ∈ chenPairs x,
        ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) ≤
        ∑ q ∈ chenPairs x,
          (x : ℝ) ^ (1 - ε / 6) *
            (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact pairQuotient_rpow_le_harmonicKernel hq hε
    _ ≤ ∑ q ∈ box,
          (x : ℝ) ^ (1 - ε / 6) *
            (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q _ _
      positivity
    _ = (x : ℝ) ^ (1 - ε / 6) *
          (harmonic x : ℝ) ^ 2 := by
      simp only [box, Finset.sum_product]
      calc
        (∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
            (x : ℝ) ^ (1 - ε / 6) * (a : ℝ)⁻¹ * (b : ℝ)⁻¹) =
            (x : ℝ) ^ (1 - ε / 6) *
              (∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
                (a : ℝ)⁻¹ * (b : ℝ)⁻¹) := by
          symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = (x : ℝ) ^ (1 - ε / 6) *
              ((∑ a ∈ Finset.Icc 1 x, (a : ℝ)⁻¹) *
                ∑ b ∈ Finset.Icc 1 x, (b : ℝ)⁻¹) := by
          rw [Finset.sum_mul_sum]
        _ = (x : ℝ) ^ (1 - ε / 6) *
              (harmonic x : ℝ) ^ 2 := by
          rw [hharm]
          ring

/-- For every admissible pair, `p₁p₂ < x`; hence the logarithmic denominator
in `M` is positive. -/
theorem one_lt_pairQuotient {x : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) :
    1 < (x : ℝ) / ((q.1 : ℝ) * q.2) := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with ⟨hp₁, hp₂, _hp₁lo, _hp₁hi, _hp₂lo, hp₂hi⟩
  have hp₁pos : (0 : ℝ) < q.1 := by exact_mod_cast hp₁.pos
  have hp₂one : (1 : ℝ) < q.2 := by exact_mod_cast hp₂.one_lt
  have hdiv0 : 0 ≤ (x : ℝ) / (q.1 : ℝ) := by positivity
  rw [← Real.sqrt_eq_rpow] at hp₂hi
  have hp₂sq :
      (q.2 : ℝ) ^ 2 ≤ (x : ℝ) / (q.1 : ℝ) := by
    nlinarith [Real.sq_sqrt hdiv0]
  have hprodSq :
      (q.1 : ℝ) * (q.2 : ℝ) ^ 2 ≤ (x : ℝ) := by
    simpa [mul_comm] using (le_div_iff₀ hp₁pos).mp hp₂sq
  have hprod : (q.1 : ℝ) * q.2 < (x : ℝ) := by
    nlinarith [mul_pos hp₁pos (sub_pos.mpr hp₂one)]
  exact (lt_div_iff₀ (mul_pos hp₁pos (zero_lt_one.trans hp₂one))).2 <| by
    simpa using hprod

/-- The pair range gives the stronger uniform lower bound
`x^(1/3) < x/(p₁p₂)`. -/
theorem rpow_third_lt_pairQuotient
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    (x : ℝ) ^ ((1 : ℝ) / 3) <
      (x : ℝ) / ((q.1 : ℝ) * q.2) := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with
    ⟨hp₁, hp₂, _hp₁lo, _hp₁hi, hp₂lo, hp₂hi⟩
  have hp₁pos : (0 : ℝ) < q.1 := by exact_mod_cast hp₁.pos
  have hp₂pos : (0 : ℝ) < q.2 := by exact_mod_cast hp₂.pos
  have hdiv0 : 0 ≤ (x : ℝ) / (q.1 : ℝ) := by positivity
  rw [← Real.sqrt_eq_rpow] at hp₂hi
  have hp₂sq :
      (q.2 : ℝ) ^ 2 ≤ (x : ℝ) / (q.1 : ℝ) := by
    nlinarith [Real.sq_sqrt hdiv0]
  have hprodSq :
      (q.1 : ℝ) * (q.2 : ℝ) ^ 2 ≤ (x : ℝ) := by
    simpa [mul_comm] using (le_div_iff₀ hp₁pos).mp hp₂sq
  apply (lt_div_iff₀ (mul_pos hp₁pos hp₂pos)).2
  calc
    (x : ℝ) ^ ((1 : ℝ) / 3) * ((q.1 : ℝ) * q.2) <
        (q.2 : ℝ) * ((q.1 : ℝ) * q.2) :=
      mul_lt_mul_of_pos_right hp₂lo (mul_pos hp₁pos hp₂pos)
    _ = (q.1 : ℝ) * (q.2 : ℝ) ^ 2 := by ring
    _ ≤ (x : ℝ) := hprodSq

/-- The two fixed prime divisors in `p₁p₂n` produce a saving of at least
`x^(-1/10)` after summing over the admissible pair range. -/
theorem pair_badPrimeFactor_weight_le
    {x : ℕ} {q : ℕ × ℕ} (hx1 : 1 ≤ x)
    (hq : q ∈ chenPairs x) :
    ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
        ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) ≤
      6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
        (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ := by
  have hq' := hq
  simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq'
  rcases hq'.2 with
    ⟨hp₁, hp₂, hp₁lo, _hp₁hi, hp₂lo, _hp₂hi⟩
  let X : ℝ := x
  let a : ℝ := q.1
  let b : ℝ := q.2
  let Y : ℝ := X / (a * b)
  have hX1 : (1 : ℝ) ≤ X := by
    change (1 : ℝ) ≤ (x : ℝ)
    exact_mod_cast hx1
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hapos : 0 < a := by
    change (0 : ℝ) < (q.1 : ℝ)
    exact_mod_cast hp₁.pos
  have hbpos : 0 < b := by
    change (0 : ℝ) < (q.2 : ℝ)
    exact_mod_cast hp₂.pos
  have hY : 1 < Y := one_lt_pairQuotient hq
  have hYadd : Y + 2 ≤ 3 * Y := by linarith
  have haInv :
      a⁻¹ ≤ X ^ (-(1 : ℝ) / 10) := by
    calc
      a⁻¹ ≤ (X ^ ((1 : ℝ) / 10))⁻¹ :=
        inv_anti₀ (by positivity) hp₁lo.le
      _ = X ^ (-((1 : ℝ) / 10)) :=
        (Real.rpow_neg hXpos.le _).symm
      _ = X ^ (-(1 : ℝ) / 10) := by ring_nf
  have hbInv :
      b⁻¹ ≤ X ^ (-(1 : ℝ) / 3) := by
    calc
      b⁻¹ ≤ (X ^ ((1 : ℝ) / 3))⁻¹ :=
        inv_anti₀ (by positivity) hp₂lo.le
      _ = X ^ (-((1 : ℝ) / 3)) :=
        (Real.rpow_neg hXpos.le _).symm
      _ = X ^ (-(1 : ℝ) / 3) := by ring_nf
  have hXmul₁ :
      X * X ^ (-(1 : ℝ) / 10) = X ^ ((9 : ℝ) / 10) := by
    calc
      X * X ^ (-(1 : ℝ) / 10) =
          X ^ (1 : ℝ) * X ^ (-(1 : ℝ) / 10) := by
        rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (-(1 : ℝ) / 10)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X ^ ((9 : ℝ) / 10) := by ring_nf
  have hXmul₂ :
      X * X ^ (-(1 : ℝ) / 3) = X ^ ((2 : ℝ) / 3) := by
    calc
      X * X ^ (-(1 : ℝ) / 3) =
          X ^ (1 : ℝ) * X ^ (-(1 : ℝ) / 3) := by
        rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (-(1 : ℝ) / 3)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X ^ ((2 : ℝ) / 3) := by ring_nf
  have hterm₁ :
      X * a⁻¹ * a⁻¹ * b⁻¹ ≤
        X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ := by
    calc
      X * a⁻¹ * a⁻¹ * b⁻¹ ≤
          X * X ^ (-(1 : ℝ) / 10) * a⁻¹ * b⁻¹ := by
        gcongr
      _ = X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ := by
        rw [hXmul₁]
  have hterm₂ :
      X * a⁻¹ * b⁻¹ * b⁻¹ ≤
        X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ := by
    calc
      X * a⁻¹ * b⁻¹ * b⁻¹ ≤
          X * a⁻¹ * X ^ (-(1 : ℝ) / 3) * b⁻¹ := by
        gcongr
      _ = (X * X ^ (-(1 : ℝ) / 3)) * a⁻¹ * b⁻¹ := by ring
      _ = X ^ ((2 : ℝ) / 3) * a⁻¹ * b⁻¹ := by rw [hXmul₂]
      _ ≤ X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num))
            (inv_nonneg.mpr hapos.le))
          (inv_nonneg.mpr hbpos.le)
  have hmain :
      Y * (a⁻¹ + b⁻¹) ≤
        2 * X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ := by
    calc
      Y * (a⁻¹ + b⁻¹) =
          X * a⁻¹ * a⁻¹ * b⁻¹ +
            X * a⁻¹ * b⁻¹ * b⁻¹ := by
        dsimp only [Y]
        rw [div_eq_mul_inv, mul_inv]
        ring
      _ ≤ X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ +
          X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ :=
        add_le_add hterm₁ hterm₂
      _ = 2 * X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ := by ring
  change (Y + 2) * (a⁻¹ + b⁻¹) ≤ _
  calc
    (Y + 2) * (a⁻¹ + b⁻¹) ≤
        3 * Y * (a⁻¹ + b⁻¹) :=
      mul_le_mul_of_nonneg_right hYadd
        (add_nonneg (inv_nonneg.mpr hapos.le) (inv_nonneg.mpr hbpos.le))
    _ ≤ 3 * (2 * X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ 3)
    _ = 6 * X ^ ((9 : ℝ) / 10) * a⁻¹ * b⁻¹ := by ring

/-- Summed form of `pair_badPrimeFactor_weight_le`. -/
theorem sum_pair_badPrimeFactor_weight_le
    (x : ℕ) (hx1 : 1 ≤ x) :
    ∑ q ∈ chenPairs x,
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹)) ≤
      6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
        (harmonic x : ℝ) ^ 2 := by
  let box : Finset (ℕ × ℕ) :=
    Finset.Icc 1 x ×ˢ Finset.Icc 1 x
  have hsubset : chenPairs x ⊆ box := by
    intro q hq
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    rcases hq'.2 with ⟨hp₁, hp₂, _⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp₁.one_le, by omega⟩,
        Finset.mem_Icc.mpr ⟨hp₂.one_le, by omega⟩⟩
  have hharm :
      ∑ i ∈ Finset.Icc 1 x, ((i : ℝ)⁻¹) =
        (harmonic x : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
  calc
    ∑ q ∈ chenPairs x,
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹)) ≤
        ∑ q ∈ chenPairs x,
          6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
            (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact pair_badPrimeFactor_weight_le hx1 hq
    _ ≤ ∑ q ∈ box,
          6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
            (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q hqbox hq
      positivity
    _ = 6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
        (harmonic x : ℝ) ^ 2 := by
      simp only [box, Finset.sum_product]
      calc
        (∑ a ∈ Finset.Icc 1 x, ∑ b ∈ Finset.Icc 1 x,
            6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
              (a : ℝ)⁻¹ * (b : ℝ)⁻¹) =
            6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
              ((∑ a ∈ Finset.Icc 1 x, (a : ℝ)⁻¹) *
                ∑ b ∈ Finset.Icc 1 x, (b : ℝ)⁻¹) := by
          rw [Finset.sum_mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = 6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
            (harmonic x : ℝ) ^ 2 := by
          rw [hharm]
          ring

/-- Elementary cardinality bound for the admissible prime-pair set. -/
theorem chenPairs_card_cast_le (x : ℕ) (hx1 : 1 ≤ x) :
    ((chenPairs x).card : ℝ) ≤
      9 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
  let A : ℝ := (x : ℝ) ^ ((1 : ℝ) / 3)
  let B : ℝ := (x : ℝ) ^ ((1 : ℝ) / 2)
  let box : Finset (ℕ × ℕ) :=
    Finset.range (⌈A⌉₊ + 1) ×ˢ Finset.range (⌈B⌉₊ + 1)
  have hsubset : chenPairs x ⊆ box := by
    intro q hq
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    rcases hq'.2 with
      ⟨hp₁, hp₂, _hp₁lo, hp₁hi, _hp₂lo, hp₂hi⟩
    have hp₁ceil : q.1 ≤ ⌈A⌉₊ := by
      exact_mod_cast hp₁hi.trans (Nat.le_ceil A)
    have hdiv :
        (x : ℝ) / q.1 ≤ (x : ℝ) := by
      exact div_le_self (by positivity) (by exact_mod_cast hp₁.one_le)
    have hp₂B : (q.2 : ℝ) ≤ B :=
      hp₂hi.trans
        (Real.rpow_le_rpow (by positivity) hdiv (by norm_num))
    have hp₂ceil : q.2 ≤ ⌈B⌉₊ := by
      exact_mod_cast hp₂B.trans (Nat.le_ceil B)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩
  have hcardNat : (chenPairs x).card ≤ box.card :=
    Finset.card_le_card hsubset
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hcard :
      ((chenPairs x).card : ℝ) ≤ (A + 2) * (B + 2) := by
    calc
      ((chenPairs x).card : ℝ) ≤ (box.card : ℝ) := by
        exact_mod_cast hcardNat
      _ = ((⌈A⌉₊ + 1 : ℕ) : ℝ) *
          ((⌈B⌉₊ + 1 : ℕ) : ℝ) := by
        simp [box]
      _ ≤ (A + 2) * (B + 2) := by
        gcongr
        · exact le_of_lt (by
            norm_num only [Nat.cast_add, Nat.cast_one]
            linarith [Nat.ceil_lt_add_one hA0])
        · exact le_of_lt (by
            norm_num only [Nat.cast_add, Nat.cast_one]
            linarith [Nat.ceil_lt_add_one hB0])
  have hx1R : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hA1 : 1 ≤ A := Real.one_le_rpow hx1R (by norm_num)
  have hB1 : 1 ≤ B := Real.one_le_rpow hx1R (by norm_num)
  calc
    ((chenPairs x).card : ℝ) ≤ (A + 2) * (B + 2) := hcard
    _ ≤ (3 * A) * (3 * B) := by nlinarith
    _ = 9 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
      dsimp only [A, B]
      calc
        3 * (x : ℝ) ^ ((1 : ℝ) / 3) *
            (3 * (x : ℝ) ^ ((1 : ℝ) / 2)) =
            9 * ((x : ℝ) ^ ((1 : ℝ) / 3) *
              (x : ℝ) ^ ((1 : ℝ) / 2)) := by ring
        _ = 9 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          ring_nf

/-- Once `x` is large, the smoothing kernel is pointwise bounded by the von
Mangoldt weight.  The pair range makes the logarithmic inverse at most one,
while Lemma 1 gives `0 ≤ Φ ≤ 1`. -/
theorem abs_smoothedMKernel_le_vonMangoldt
    {x : ℕ} {q : ℕ × ℕ} {n : ℕ}
    (hx : Real.exp 3 ≤ (x : ℝ)) (hq : q ∈ chenPairs x) :
    |smoothedMKernel x q n| ≤ ArithmeticFunction.vonMangoldt n := by
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  have hxpos : (0 : ℝ) < x := (Real.exp_pos 3).trans_le hx
  have hx1 : (1 : ℝ) < x := by
    have : (1 : ℝ) < Real.exp 3 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 3)
    exact this.trans_le hx
  have hlogx : (3 : ℝ) ≤ Real.log x := by
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (Real.exp_pos 3)) (Set.mem_Ioi.mpr hxpos) hx
  have hY : (x : ℝ) ^ ((1 : ℝ) / 3) < Y :=
    rpow_third_lt_pairQuotient hq
  have hlogY : (1 : ℝ) ≤ Real.log Y := by
    have hlogpow :
        Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) =
          (1 : ℝ) / 3 * Real.log x := by
      rw [Real.log_rpow hxpos]
    have hpowpos :
        0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have hmono :
        Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤ Real.log Y :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hpowpos)
        (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
    rw [hlogpow] at hmono
    nlinarith
  have hinvnonneg : 0 ≤ (Real.log Y)⁻¹ := by positivity
  have hinvle : (Real.log Y)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hlogY
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hy : 0 ≤
      (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
  have hΦ0 : 0 ≤
      chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) :=
    chenPhi_nonneg x hx1 hy
  have hΦ1 :
      chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) ≤ 1 :=
    chenPhi_le_one x hx1 hy
  rw [smoothedMKernel, abs_mul, abs_mul,
    abs_of_nonneg hinvnonneg, abs_of_nonneg hΛ,
    abs_of_nonneg hΦ0]
  calc
    (Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt n *
        chenPhi x ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) ≤
      1 * ArithmeticFunction.vonMangoldt n * 1 := by
        gcongr
    _ = ArithmeticFunction.vonMangoldt n := by ring

/-- The absolute bad mass is bounded by the corresponding von Mangoldt
mass. -/
theorem abs_smoothedMBadMass_le
    {x d : ℕ} (hx : Real.exp 3 ≤ (x : ℝ)) :
    |smoothedMBadMass x d| ≤
      ∑ z ∈ smoothedMBadTriples x d,
        ArithmeticFunction.vonMangoldt z.2 := by
  unfold smoothedMBadMass
  calc
    |∑ z ∈ smoothedMBadTriples x d,
        smoothedMKernel x z.1 z.2| ≤
        ∑ z ∈ smoothedMBadTriples x d,
          |smoothedMKernel x z.1 z.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ smoothedMBadTriples x d,
        ArithmeticFunction.vonMangoldt z.2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hzT := (Finset.mem_filter.mp hz).1
      have hzprod := (Finset.mem_filter.mp hzT).1
      have hq : z.1 ∈ chenPairs x :=
        (Finset.mem_product.mp hzprod).1
      exact abs_smoothedMKernel_le_vonMangoldt hx hq

theorem sieveMSmallMajorant_le_harmonic
    (x : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (sieveMSmallMajorant x ε : ℝ) ≤
      2 * (x : ℝ) ^ (1 - ε / 6) * (harmonic x : ℝ) ^ 2 := by
  calc
    (sieveMSmallMajorant x ε : ℝ) ≤
        ∑ q ∈ chenPairs x,
          (((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) + 1) :=
      sieveMSmallMajorant_cast_le x ε
    _ ≤ ∑ q ∈ chenPairs x,
        2 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) := by
      apply Finset.sum_le_sum
      intro q hq
      have hY := one_lt_pairQuotient hq
      have hone :
          (1 : ℝ) ≤
            ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) :=
        Real.one_le_rpow hY.le (sub_nonneg.mpr hε1.le)
      linarith
    _ = 2 * ∑ q ∈ chenPairs x,
        ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * ((x : ℝ) ^ (1 - ε / 6) *
        (harmonic x : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (sum_pairQuotient_rpow_le_harmonic x hε0) (by norm_num)
    _ = 2 * (x : ℝ) ^ (1 - ε / 6) *
        (harmonic x : ℝ) ^ 2 := by ring

theorem eventually_harmonic_sq_le_rpow
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (harmonic n : ℝ) ^ 2 ≤ (n : ℝ) ^ δ := by
  have hlogReal :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x ^ (2 : ℝ)‖ ≤
          (1 / 4 : ℝ) * ‖x ^ δ‖ :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hδ).def
      (by norm_num)
  have hlogNat :
      ∀ᶠ n : ℕ in atTop,
        ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤
          (1 / 4 : ℝ) * ‖(n : ℝ) ^ δ‖ :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  have hlogOneReal :
      ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [hlogNat, hlogOne] with n hnlog hnlogone
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlogsq :
      Real.log (n : ℝ) ^ 2 ≤
        (1 / 4 : ℝ) * (n : ℝ) ^ δ := by
    simpa [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0 δ)] using hnlog
  have hHnonneg : 0 ≤ (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hH := harmonic_le_one_add_log n
  have hHlog :
      (harmonic n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    linarith
  nlinarith [sq_nonneg
    ((harmonic n : ℝ) - 2 * Real.log (n : ℝ))]

theorem eventually_sieveMSmallTail_le_rpow
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ x : ℕ in atTop,
      (sieveMSmallTail x ε : ℝ) ≤
        2 * (x : ℝ) ^ (1 - ε / 12) := by
  have hδ : 0 < ε / 12 := by positivity
  filter_upwards [eventually_harmonic_sq_le_rpow hδ,
    eventually_gt_atTop 0] with x hH hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have htailNat := sieveMSmallTail_le_majorant x ε
  have htail :
      (sieveMSmallTail x ε : ℝ) ≤
        (sieveMSmallMajorant x ε : ℝ) := by
    exact_mod_cast htailNat
  calc
    (sieveMSmallTail x ε : ℝ) ≤
        (sieveMSmallMajorant x ε : ℝ) := htail
    _ ≤ 2 * (x : ℝ) ^ (1 - ε / 6) *
        (harmonic x : ℝ) ^ 2 :=
      sieveMSmallMajorant_le_harmonic x hε0.le hε1
    _ ≤ 2 * (x : ℝ) ^ (1 - ε / 6) *
        (x : ℝ) ^ (ε / 12) := by
      exact mul_le_mul_of_nonneg_left hH (by positivity)
    _ = 2 * (x : ℝ) ^ (1 - ε / 12) := by
      rw [mul_assoc, ← Real.rpow_add hxpos]
      congr 2
      ring_nf

/-- Any fixed power saving absorbs any fixed logarithmic power.  This is the
asymptotic conversion used for the `x^(1-cε)` bounds on the small tail, `M₃`,
and `M₅`. -/
theorem eventually_rpow_one_sub_le_div_log_rpow
    {δ r : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 - δ) ≤
        (n : ℝ) / (Real.log n) ^ r := by
  have hlog :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x ^ r‖ ≤ ‖x ^ δ‖ :=
    (isLittleO_log_rpow_rpow_atTop r hδ).eventuallyLE
  have hreal :
      ∀ᶠ x : ℝ in atTop,
        x ^ (1 - δ) ≤ x / Real.log x ^ r := by
    filter_upwards [hlog, eventually_gt_atTop 1] with x hxlog hx1
    have hxpos : 0 < x := zero_lt_one.trans hx1
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hLpos : 0 < Real.log x ^ r :=
      Real.rpow_pos_of_pos hlogpos r
    have hxpow :
        Real.log x ^ r ≤ x ^ δ := by
      simpa [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le r),
        Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le δ)] using hxlog
    apply (le_div_iff₀ hLpos).2
    calc
      x ^ (1 - δ) * Real.log x ^ r ≤
          x ^ (1 - δ) * x ^ δ :=
        mul_le_mul_of_nonneg_left hxpow
          (Real.rpow_nonneg hxpos.le _)
      _ = x := by
        rw [← Real.rpow_add hxpos]
        have hexp : (1 - δ) + δ = (1 : ℝ) := by ring
        rw [hexp, Real.rpow_one]
  exact tendsto_natCast_atTop_atTop.eventually hreal

/-- Exact finite-sum reduction underlying the display
`Ω ≤ M/(1-ε) + N` before equation (5).

The only analytic input needed at this stage is positivity of
`log (x/(p₁p₂))` for every admissible pair.  A separate range lemma supplies
this hypothesis for all sufficiently large `x`. -/
theorem one_sub_mul_sieveOmega_le_sieveM_add_smallTail
    {x : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hratio : ∀ q ∈ chenPairs x,
      1 < (x : ℝ) / ((q.1 : ℝ) * q.2)) :
    (1 - ε) * (sieveOmega x : ℝ) ≤
      sieveM x + (sieveMSmallTail x ε : ℝ) := by
  simp only [sieveOmega, sieveM, sieveMSmallTail, Nat.cast_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  have hY : 1 < Y := by simpa only [Y] using hratio q hq
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hsubset : omegaThirdPrimes x q ⊆ sieveMIndices x q := by
    intro p hp
    simp only [omegaThirdPrimes, Finset.mem_filter, Finset.mem_range] at hp
    simp only [sieveMIndices, Finset.mem_filter, Finset.mem_range]
    exact ⟨hp.1, hp.2.2.1, hp.2.2.2⟩
  have hΛsum :
      ∑ p ∈ omegaThirdPrimes x q, ArithmeticFunction.vonMangoldt p ≤
        ∑ n ∈ sieveMIndices x q, ArithmeticFunction.vonMangoldt n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  calc
    (1 - ε) * (omegaThirdPrimes x q).card =
        ∑ p ∈ omegaThirdPrimes x q, (1 - ε) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ p ∈ omegaThirdPrimes x q,
        ((Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt p +
          if (p : ℝ) < Y ^ (1 - ε) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata :
          p.Prime ∧ (p : ℝ) ≤ Y ∧ chenRough x (x - q.1 * q.2 * p) := by
        have hp' := hp
        simp only [omegaThirdPrimes, Finset.mem_filter, Finset.mem_range] at hp'
        simpa only [Y] using hp'.2
      have hw0 :
          0 ≤ (Real.log Y)⁻¹ * ArithmeticFunction.vonMangoldt p :=
        mul_nonneg (le_of_lt (inv_pos.mpr hlogY))
          ArithmeticFunction.vonMangoldt_nonneg
      by_cases hsmall : (p : ℝ) < Y ^ (1 - ε)
      · simp only [hsmall, ↓reduceIte]
        linarith
      · simp only [hsmall, ↓reduceIte, add_zero]
        have hpow : Y ^ (1 - ε) ≤ (p : ℝ) := le_of_not_gt hsmall
        have hlogpow :
            Real.log (Y ^ (1 - ε)) ≤ Real.log (p : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hY0 _) hpow
        rw [Real.log_rpow hY0] at hlogpow
        have hdiv :
            1 - ε ≤ Real.log (p : ℝ) / Real.log Y :=
          (le_div_iff₀ hlogY).2 (by simpa [mul_comm] using hlogpow)
        simpa [ArithmeticFunction.vonMangoldt_apply_prime hpdata.1,
          div_eq_mul_inv, mul_comm] using hdiv
    _ = (Real.log Y)⁻¹ *
          (∑ p ∈ omegaThirdPrimes x q, ArithmeticFunction.vonMangoldt p) +
        (omegaSmallThirdPrimes x ε q).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [omegaSmallThirdPrimes, Y]
    _ ≤ (Real.log Y)⁻¹ *
          (∑ n ∈ sieveMIndices x q, ArithmeticFunction.vonMangoldt n) +
        (omegaSmallThirdPrimes x ε q).card := by
      gcongr
    _ = (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ sieveMIndices x q, ArithmeticFunction.vonMangoldt n +
        (omegaSmallThirdPrimes x ε q).card := by
      rfl

/-- Version of `one_sub_mul_sieveOmega_le_sieveM_add_smallTail` with the
pair-range hypothesis discharged from the definition of `chenPairs`. -/
theorem one_sub_mul_sieveOmega_le_sieveM_add_smallTail'
    {x : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) :
    (1 - ε) * (sieveOmega x : ℝ) ≤
      sieveM x + (sieveMSmallTail x ε : ℝ) :=
  one_sub_mul_sieveOmega_le_sieveM_add_smallTail hε0
    (fun _ hq => one_lt_pairQuotient hq)

/-- Algebraic assembly of Lemma 5 after the two remaining estimates have been
proved: a decomposition of `M` and a bound for the small-`p₃` tail. -/
theorem sieveOmega_le_of_sieveM_le
    {x : ℕ} {ε E_M E_tail : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hM : sieveM x ≤ mOne x ε + mTwo x ε + E_M)
    (htail : (sieveMSmallTail x ε : ℝ) ≤ E_tail) :
    (sieveOmega x : ℝ) ≤
      (mOne x ε + mTwo x ε + E_M + E_tail) / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε1)).2
  have hbase := one_sub_mul_sieveOmega_le_sieveM_add_smallTail'
    (x := x) hε0
  linarith

end Chen
