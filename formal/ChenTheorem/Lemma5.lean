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

/-- A finite nontrivial-character sum commutes with any other finite sum. -/
theorem nontrivialCharSum_sum_comm
    {ι : Type*} [DecidableEq ι] {d : ℕ} (hd : d ≠ 0)
    (s : Finset ι) (F : DirichletCharacter ℂ d → ι → ℂ) :
    nontrivialCharSum d (fun χ => ∑ i ∈ s, F χ i) =
      ∑ i ∈ s, nontrivialCharSum d (fun χ => F χ i) := by
  unfold nontrivialCharSum
  simp only [dif_neg hd]
  calc
    (∑ χ : DirichletCharacter ℂ d,
        if χ = 1 then 0 else ∑ i ∈ s, F χ i) =
        ∑ χ : DirichletCharacter ℂ d,
          ∑ i ∈ s, if χ = 1 then 0 else F χ i := by
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hχone : χ = 1 <;> simp [hχone]
    _ = ∑ i ∈ s, ∑ χ : DirichletCharacter ℂ d,
        if χ = 1 then 0 else F χ i := by
      rw [Finset.sum_comm]

/-- A scalar may be pulled through a nontrivial-character sum. -/
theorem nontrivialCharSum_const_mul
    {d : ℕ} (hd : d ≠ 0) (c : ℂ)
    (F : DirichletCharacter ℂ d → ℂ) :
    nontrivialCharSum d (fun χ => c * F χ) =
      c * nontrivialCharSum d F := by
  unfold nontrivialCharSum
  simp only [dif_neg hd]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hχone : χ = 1 <;> simp [hχone]

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

/-- The character term occurring directly in equation (6) is the nested,
pair-filtered contribution used in the definitions of `M₄` and `M₅`. -/
theorem nontrivialCharSum_eq_imprimitiveContribution
    {x d : ℕ} (hd : 0 < d) (hxd : x.Coprime d) :
    nontrivialCharSum d (fun χ =>
      χ (x : ZMod d)⁻¹ *
        ∑ z ∈ smoothedMTriples x,
          (smoothedMKernel x z.1 z.2 : ℂ) *
            χ (smoothedMArgument z : ZMod d)) =
      imprimitiveCharacterContribution x d := by
  unfold imprimitiveCharacterContribution
  simp only [nontrivialCharSum, dif_neg hd.ne']
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hχone : χ = 1
  · simp [hχone]
  simp only [hχone, ↓reduceIte]
  congr 1
  · have hxunit : IsUnit (x : ZMod d) :=
      (ZMod.isUnit_iff_coprime x d).2 hxd
    obtain ⟨u, hu⟩ := hxunit
    rw [← hu]
    have hstar := congrArg
      (fun ψ : DirichletCharacter ℂ d => ψ (u : ZMod d))
      (MulChar.star_eq_inv χ)
    simpa [MulChar.inv_apply_eq_inv] using hstar.symm
  · simp only [smoothedMArgument, Nat.cast_mul]
    rw [sum_smoothedMTriples_eq_nested x
      (fun q n => (smoothedMKernel x q n : ℂ) *
        χ (q.1 * q.2 * n : ZMod d))]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqcop : Nat.Coprime (q.1 * q.2) d
    · simp [hqcop]
    · have hnonunit : ¬IsUnit (q.1 * q.2 : ZMod d) := by
        intro hu
        have hu' : IsUnit ((q.1 * q.2 : ℕ) : ZMod d) := by
          simpa using hu
        exact hqcop
          ((ZMod.isUnit_iff_coprime (q.1 * q.2) d).1 hu')
      have hzero : χ (q.1 * q.2 : ZMod d) = 0 :=
        MulChar.apply_eq_zero_iff.mpr hnonunit
      simp only [hqcop, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro n hn
      rw [show (q.1 * q.2 * n : ZMod d) =
          (q.1 * q.2 : ZMod d) * (n : ZMod d) by norm_num,
        map_mul, hzero, zero_mul, mul_zero]

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

/-- Real form of equation (6) for one modulus. -/
theorem smoothedResidueMass_eq
    {x d : ℕ} (hd : 0 < d) (hxd : x.Coprime d) :
    ∑ z ∈ smoothedMTriples x,
        smoothedMKernel x z.1 z.2 *
          (if x ≡ smoothedMArgument z [MOD d] then 1 else 0) =
      (smoothedMGoodMass x d +
          (imprimitiveCharacterContribution x d).re) /
        (Nat.totient d : ℝ) := by
  have h6 := smoothedM_equation_six hd hxd
  rw [nontrivialCharSum_eq_imprimitiveContribution hd hxd] at h6
  have hre := congrArg Complex.re h6
  have hφ : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  simpa [smoothedMGoodMass, div_eq_mul_inv, hφ] using hre

/-- Equations (6)–(7), before taking absolute values: the smoothed residue
expansion is exactly the principal term minus `M₃` plus the signed
nonprincipal term. -/
theorem smoothedSieveExpansion_eq
    (x : ℕ) (ε : ℝ) :
    smoothedSieveExpansion x ε =
      mOne x ε - mThree x ε + mFourSigned x ε := by
  unfold smoothedSieveExpansion mOne mThree mFourSigned
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hddata := (Finset.mem_filter.mp hd).2
  have hdpos : 0 < d := by omega
  have hres := smoothedResidueMass_eq hdpos hddata.2.1.symm
  have hmass := smoothedMGoodMass_add_badMass x d
  rw [sum_smoothedMTriples_eq x] at hmass
  rw [hres]
  have hgood :
      smoothedMGoodMass x d =
        (∑ q ∈ chenPairs x,
          ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n) -
          smoothedMBadMass x d := by
    linarith
  rw [hgood]
  ring

/-- Equation (9) in finite-sum form: replacing every imprimitive character
by its primitive associate leaves precisely the discrepancy `M₅`. -/
theorem mFour_le_mTwo_add_mFive (x : ℕ) (ε : ℝ) :
    mFour x ε ≤ mTwo x ε + mFive x ε := by
  unfold mFour mTwo mFive
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  let A : ℝ :=
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)
  let F : ℂ := imprimitiveCharacterContribution x d
  let G : ℂ := primitiveCharacterContribution x d
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have htriangle : ‖F‖ ≤ ‖G‖ + ‖F - G‖ := by
    have h := norm_add_le G (F - G)
    simpa [add_sub_cancel_left] using h
  change A * ‖F‖ ≤ A * ‖G‖ + A * ‖F - G‖
  calc
    A * ‖F‖ ≤ A * (‖G‖ + ‖F - G‖) :=
      mul_le_mul_of_nonneg_left htriangle hA
    _ = A * ‖G‖ + A * ‖F - G‖ := by ring

/-- The imprimitive-to-primitive discrepancy is supported exactly on the
indices not coprime to the original level `d`. -/
theorem imprimitive_sub_primitive_eq_neg_bad
    {x d : ℕ} (hd : 0 < d) (hxd : x.Coprime d) :
    imprimitiveCharacterContribution x d -
        primitiveCharacterContribution x d =
      -primitiveBadCharacterContribution x d := by
  unfold imprimitiveCharacterContribution primitiveCharacterContribution
    primitiveBadCharacterContribution
  simp only [nontrivialCharSum, dif_neg hd.ne']
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hχone : χ = 1
  · simp [hχone]
  simp only [hχone, ↓reduceIte]
  have hxcop : IsCoprime (x : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hxd
  have hxval := χ.primitiveCharacter_apply_of_isCoprime hxcop
  have hxstar :
      starRingEnd ℂ (χ (x : ZMod d)) =
        starRingEnd ℂ (χ.primitiveCharacter x) := by
    congr 1
    simpa only [Int.cast_natCast] using hxval.symm
  rw [hxstar]
  rw [← mul_sub, ← mul_neg]
  congr 1
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqcop : Nat.Coprime (q.1 * q.2) d
  · rw [if_pos hqcop, if_pos hqcop, if_pos hqcop]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hncop : n.Coprime d
    · rw [if_neg (not_not.mpr hncop), neg_zero]
      have hprod : (q.1 * q.2 * n).Coprime d :=
        Nat.Coprime.mul_left hqcop hncop
      have hprodZ : IsCoprime (q.1 * q.2 * n : ℤ) (d : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr hprod
      have hval :=
        χ.primitiveCharacter_apply_of_isCoprime hprodZ
      have hval' :
          χ ((q.1 : ZMod d) * q.2 * n) =
            χ.primitiveCharacter (q.1 * q.2 * n) := by
        simpa only [Int.cast_natCast, Int.cast_mul, Nat.cast_mul]
          using hval.symm
      rw [hval']
      ring
    · rw [if_pos hncop]
      have hnotprod : ¬(q.1 * q.2 * n).Coprime d := by
        intro hprod
        exact hncop (Nat.Coprime.of_dvd_left
          (by exact dvd_mul_left n (q.1 * q.2)) hprod)
      have hnonunit :
          ¬IsUnit ((q.1 * q.2 * n : ℕ) : ZMod d) := by
        intro hu
        exact hnotprod
          ((ZMod.isUnit_iff_coprime (q.1 * q.2 * n) d).1 hu)
      have hzero :
          χ ((q.1 * q.2 * n : ℕ) : ZMod d) = 0 :=
        MulChar.apply_eq_zero_iff.mpr hnonunit
      have hzero' :
          χ ((q.1 : ZMod d) * q.2 * n) = 0 := by
        simpa using hzero
      rw [hzero', mul_zero, zero_sub, neg_eq_neg_one_mul]
  · rw [if_neg hqcop, if_neg hqcop, if_neg hqcop]
    simp

/-- `M₅` written using only the bad-index primitive character sum. -/
theorem mFive_eq_badContribution
    {x : ℕ} {ε : ℝ} :
    mFive x ε =
      ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (3 : ℝ) ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) *
          ‖primitiveBadCharacterContribution x d‖ := by
  unfold mFive
  apply Finset.sum_congr rfl
  intro d hd
  have hddata := (Finset.mem_filter.mp hd).2
  have hdpos : 0 < d := by omega
  rw [imprimitive_sub_primitive_eq_neg_bad
    hdpos hddata.2.1.symm, norm_neg]

/-- Lift a primitive character at a divisor of `d` to level `d`. -/
private noncomputable def primitiveLift
    (d : ℕ) [NeZero d]
    (z : Σ k : ↥d.divisors,
      {χ : DirichletCharacter ℂ k.1 // χ.IsPrimitive}) :
    DirichletCharacter ℂ d :=
  DirichletCharacter.changeLevel
    (Nat.dvd_of_mem_divisors z.1.2) z.2.1

/-- Every character modulo a nonzero `d` is obtained uniquely by lifting its
primitive character from its conductor. -/
private theorem primitiveLift_bijective
    (d : ℕ) [NeZero d] :
    Function.Bijective (primitiveLift d) := by
  constructor
  · intro a b hab
    obtain ⟨ka, ψa⟩ := a
    obtain ⟨kb, ψb⟩ := b
    have hcond := congrArg DirichletCharacter.conductor hab
    have hka :
        (DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors ka.2) ψa.1).conductor = ka.1 := by
      rw [DirichletCharacter.conductor_changeLevel]
      exact ψa.2
    have hkb :
        (DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors kb.2) ψb.1).conductor = kb.1 := by
      rw [DirichletCharacter.conductor_changeLevel]
      exact ψb.2
    have hkval : ka.1 = kb.1 := by
      have hcond' :
          (DirichletCharacter.changeLevel
            (Nat.dvd_of_mem_divisors ka.2) ψa.1).conductor =
          (DirichletCharacter.changeLevel
            (Nat.dvd_of_mem_divisors kb.2) ψb.1).conductor := by
        simpa only [primitiveLift] using hcond
      exact hka.symm.trans (hcond'.trans hkb)
    have hk : ka = kb := Subtype.ext hkval
    subst kb
    have hψ : ψa.1 = ψb.1 :=
      DirichletCharacter.changeLevel_injective
        (Nat.dvd_of_mem_divisors ka.2) hab
    have hψsub : ψa = ψb := Subtype.ext hψ
    subst ψb
    rfl
  · intro χ
    let k : ↥d.divisors :=
      ⟨χ.conductor, Nat.mem_divisors.mpr
        ⟨χ.conductor_dvd_level, NeZero.ne d⟩⟩
    let ψ : {ξ : DirichletCharacter ℂ k.1 // ξ.IsPrimitive} :=
      ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩
    refine ⟨⟨k, ψ⟩, ?_⟩
    exact χ.changeLevel_primitiveCharacter

private noncomputable def primitiveData
    (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) :
    Σ k : ↥d.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive} :=
  ⟨⟨χ.conductor, Nat.mem_divisors.mpr
      ⟨χ.conductor_dvd_level, NeZero.ne d⟩⟩,
    ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩⟩

/-- Equivalence implementing the conductor partition of all characters
modulo `d`. -/
private noncomputable def primitiveLiftEquiv
    (d : ℕ) [NeZero d] :
    (Σ k : ↥d.divisors,
      {χ : DirichletCharacter ℂ k.1 // χ.IsPrimitive}) ≃
        DirichletCharacter ℂ d :=
  { toFun := primitiveLift d
    invFun := primitiveData d
    left_inv := fun z => (primitiveLift_bijective d).1 <| by
      exact (primitiveLift d z).changeLevel_primitiveCharacter
    right_inv := fun χ => χ.changeLevel_primitiveCharacter }

/-- Reindex a sum over all characters by conductor and primitive character. -/
private theorem sum_characters_eq_sum_primitiveLifts
    (d : ℕ) [NeZero d] (F : DirichletCharacter ℂ d → ℂ) :
    (∑ χ : DirichletCharacter ℂ d, F χ) =
      ∑ z : Σ k : ↥d.divisors,
        {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
          F (primitiveLift d z) :=
  ((primitiveLiftEquiv d).sum_comp F).symm

/-- A primitive character agrees pointwise with its associated primitive
character (whose level is definitionally its conductor). -/
private theorem primitiveCharacter_eq_self_apply
    {k : ℕ} [NeZero k]
    (ψ : DirichletCharacter ℂ k) (hψ : ψ.IsPrimitive) (a : ℕ) :
    ψ.primitiveCharacter a = ψ a := by
  have hlevel : ψ.conductor = k := hψ
  have hchange := ψ.changeLevel_primitiveCharacter
  by_cases ha : IsCoprime (a : ℤ) (k : ℤ)
  · have hcl :=
      DirichletCharacter.changeLevel_eq_cast_of_dvd'
        ψ.primitiveCharacter ψ.conductor_dvd_level ha
    have happ := congrArg
      (fun ξ : DirichletCharacter ℂ k => ξ (a : ℤ)) hchange
    simpa only [Int.cast_natCast] using hcl.symm.trans happ
  · have hψ0 : ψ (a : ℤ) = 0 :=
      (DirichletCharacter.apply_eq_zero_iff ψ (a : ℤ)).2 ha
    have haprim : ¬IsCoprime (a : ℤ) (ψ.conductor : ℤ) := by
      simpa only [hlevel] using ha
    have hprim0 : ψ.primitiveCharacter (a : ℤ) = 0 :=
      (DirichletCharacter.apply_eq_zero_iff
        ψ.primitiveCharacter (a : ℤ)).2 haprim
    have hψ0' : ψ a = 0 := by
      simpa only [Int.cast_natCast] using hψ0
    have hprim0' : ψ.primitiveCharacter a = 0 := by
      simpa only [Int.cast_natCast] using hprim0
    rw [hψ0', hprim0']

/-- The primitive character attached to a lifted character is the primitive
character from which it was lifted. -/
private theorem primitiveLift_primitiveCharacter_apply
    (d : ℕ) [NeZero d]
    (z : Σ k : ↥d.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive})
    (a : ℕ) :
    (primitiveLift d z).primitiveCharacter a = z.2.1 a := by
  obtain ⟨k, ψ⟩ := z
  letI : NeZero k.1 := ⟨by
    exact (Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors k.2)
      (Nat.pos_of_ne_zero (NeZero.ne d))).ne'⟩
  change
    (DirichletCharacter.changeLevel
      (Nat.dvd_of_mem_divisors k.2) ψ.1).primitiveCharacter a =
        ψ.1 a
  have hchange :=
    DirichletCharacter.primitiveCharacter_changeLevel_apply
      (Nat.dvd_of_mem_divisors k.2) ψ.1 (a : ℤ)
  have hself :=
    primitiveCharacter_eq_self_apply ψ.1 ψ.2 a
  have hchangeNat :
      (DirichletCharacter.changeLevel
        (Nat.dvd_of_mem_divisors k.2) ψ.1).primitiveCharacter a =
        ψ.1.primitiveCharacter a := by
    simpa only [Int.cast_natCast] using hchange
  exact hchangeNat.trans hself

/-- Version of Lemma 4 that also covers `m = 1`; in that case the trivial
cardinality bound is exactly the required `gcd(0,k)=k` bound. -/
theorem primitive_char_sum_bound_all
    (k : ℕ) (hk : Squarefree k) (hodd : Odd k) (m : ℕ) :
    ‖∑' χ : DirichletCharacter ℂ k,
        if χ.IsPrimitive then χ m else 0‖ ≤
      (Nat.gcd (m - 1) k : ℝ) := by
  letI : NeZero k := ⟨hodd.pos.ne'⟩
  by_cases hm : m = 1
  · subst m
    rw [show 1 - 1 = 0 by omega, Nat.gcd_zero_left]
    rw [tsum_fintype]
    calc
      ‖∑ χ : DirichletCharacter ℂ k,
          if χ.IsPrimitive then χ (1 : ℕ) else 0‖ ≤
          ∑ χ : DirichletCharacter ℂ k,
            ‖if χ.IsPrimitive then χ (1 : ℕ) else 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro χ hχ
        by_cases hp : χ.IsPrimitive <;> simp [hp]
      _ = (Fintype.card (DirichletCharacter ℂ k) : ℝ) := by simp
      _ = (Nat.totient k : ℝ) := by
        rw [Fintype.card_eq_nat_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      _ ≤ (k : ℝ) := by exact_mod_cast Nat.totient_le k
  · exact primitive_char_sum_bound k hk hodd m hm

/-- The least nonnegative residue of `m x⁻¹ (mod k)`, with the inverse
represented by the unit supplied by `(x,k)=1`. -/
noncomputable def primitiveTwistResidue
    (k x m : ℕ) (hxk : x.Coprime k) : ℕ :=
  let u : (ZMod k)ˣ :=
    (ZMod.isUnit_iff_coprime x k).2 hxk |>.unit
  ((m : ZMod k) * (↑(u⁻¹) : ZMod k)).val

/-- Lemma 4 with the factor `conj(ψ(x))` absorbed by evaluating at the
residue `m x⁻¹ (mod k)`. -/
theorem primitive_twisted_sum_bound
    {k x m : ℕ} (hk : Squarefree k) (hodd : Odd k)
    (hxk : x.Coprime k) :
    ‖∑' ψ : DirichletCharacter ℂ k,
        if ψ.IsPrimitive then
          starRingEnd ℂ (ψ x) * ψ m
        else 0‖ ≤
      (Nat.gcd (primitiveTwistResidue k x m hxk - 1) k : ℝ) := by
  letI : NeZero k := ⟨hodd.pos.ne'⟩
  let hxunit : IsUnit (x : ZMod k) :=
    (ZMod.isUnit_iff_coprime x k).2 hxk
  let u : (ZMod k)ˣ := hxunit.unit
  let a : ℕ := ((m : ZMod k) * (↑(u⁻¹) : ZMod k)).val
  have hu : (u : ZMod k) = (x : ZMod k) := hxunit.unit_spec
  have hterm :
      ∀ ψ : DirichletCharacter ℂ k,
        starRingEnd ℂ (ψ x) * ψ m = ψ a := by
    intro ψ
    have hstar := congrArg
      (fun ξ : DirichletCharacter ℂ k => ξ (u : ZMod k))
      (MulChar.star_eq_inv ψ)
    have hstar' :
        starRingEnd ℂ (ψ (u : ZMod k)) =
          (ψ (u : ZMod k))⁻¹ := by
      simpa [MulChar.inv_apply_eq_inv] using hstar
    dsimp only [a]
    rw [ZMod.natCast_zmod_val, map_mul]
    have hinv :
        ψ (↑(u⁻¹) : ZMod k) = (ψ (u : ZMod k))⁻¹ := by
      simp
    rw [hinv, ← hstar', hu]
    ring
  simp_rw [hterm]
  simpa only [primitiveTwistResidue, hxunit, u, a] using
    primitive_char_sum_bound_all k hk hodd a

/-- Replace a sum over the subtype of primitive characters by the usual
finite `tsum` with an `IsPrimitive` indicator. -/
private theorem sum_primitive_subtype_eq_tsum
    (k : ℕ) (F : DirichletCharacter ℂ k → ℂ) :
    (∑ ψ : {ψ : DirichletCharacter ℂ k // ψ.IsPrimitive}, F ψ.1) =
      ∑' ψ : DirichletCharacter ℂ k,
        if ψ.IsPrimitive then F ψ else 0 := by
  rw [tsum_fintype]
  symm
  calc
    (∑ ψ : DirichletCharacter ℂ k,
        if ψ.IsPrimitive then F ψ else 0) =
        ∑ ψ ∈ (Finset.univ.filter
          (fun ψ : DirichletCharacter ℂ k => ψ.IsPrimitive)), F ψ := by
      rw [Finset.sum_filter]
    _ = ∑ ψ : {ψ : DirichletCharacter ℂ k // ψ.IsPrimitive},
        F ψ.1 := by
      exact Finset.sum_subtype _ (by simp) F

/-- Reindex the sum of primitive associates of all nontrivial characters
modulo `d` by their conductors.  The conductor-one fiber is exactly the
trivial character and therefore disappears. -/
theorem nontrivial_primitiveAssociateSum_eq
    {d x m : ℕ} (hd : 0 < d) :
    nontrivialCharSum d (fun χ =>
      starRingEnd ℂ (χ.primitiveCharacter x) *
        χ.primitiveCharacter m) =
      ∑ k : ↥d.divisors,
        ∑ ψ : {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
          if k.1 = 1 then 0
          else starRingEnd ℂ (ψ.1 x) * ψ.1 m := by
  letI : NeZero d := ⟨hd.ne'⟩
  unfold nontrivialCharSum
  rw [dif_neg hd.ne']
  rw [sum_characters_eq_sum_primitiveLifts]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  letI : NeZero k.1 := ⟨by
    exact (Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors k.2) hd).ne'⟩
  apply Finset.sum_congr rfl
  intro ψ hψ
  have hliftone :
      primitiveLift d ⟨k, ψ⟩ = 1 ↔ k.1 = 1 := by
    change
      DirichletCharacter.changeLevel
        (Nat.dvd_of_mem_divisors k.2) ψ.1 = 1 ↔ k.1 = 1
    rw [DirichletCharacter.changeLevel_eq_one_iff]
    constructor
    · intro hψone
      have hcond :
          ψ.1.conductor = 1 :=
        DirichletCharacter.eq_one_iff_conductor_eq_one.mp hψone
      exact ψ.2.symm.trans hcond
    · intro hkone
      apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
      exact ψ.2.trans hkone
  by_cases hkone : k.1 = 1
  · rw [if_pos (hliftone.mpr hkone), if_pos hkone]
  · rw [if_neg (hliftone.not.mpr hkone), if_neg hkone]
    change
      starRingEnd ℂ ((primitiveLift d ⟨k, ψ⟩).primitiveCharacter x) *
          (primitiveLift d ⟨k, ψ⟩).primitiveCharacter m =
        starRingEnd ℂ (ψ.1 x) * ψ.1 m
    rw [primitiveLift_primitiveCharacter_apply,
      primitiveLift_primitiveCharacter_apply]

/-- Lemma 4 applied after the conductor reindexing. -/
theorem nontrivial_primitiveAssociateSum_norm_le
    {d x m : ℕ} (hd : 0 < d) (hdsq : Squarefree d)
    (hodd : Odd d) (hxd : x.Coprime d) :
    ‖nontrivialCharSum d (fun χ =>
      starRingEnd ℂ (χ.primitiveCharacter x) *
        χ.primitiveCharacter m)‖ ≤
      ∑ k : ↥d.divisors,
        let hxk : x.Coprime k.1 :=
          Nat.Coprime.of_dvd_right
            (Nat.dvd_of_mem_divisors k.2) hxd
        if k.1 = 1 then 0
        else
          (Nat.gcd
            (primitiveTwistResidue k.1 x m hxk - 1) k.1 : ℝ) := by
  rw [nontrivial_primitiveAssociateSum_eq hd]
  calc
    ‖∑ k : ↥d.divisors,
        ∑ ψ : {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
          if k.1 = 1 then 0
          else starRingEnd ℂ (ψ.1 x) * ψ.1 m‖ ≤
        ∑ k : ↥d.divisors,
          ‖∑ ψ : {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
            if k.1 = 1 then 0
            else starRingEnd ℂ (ψ.1 x) * ψ.1 m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k : ↥d.divisors,
        let hxk : x.Coprime k.1 :=
          Nat.Coprime.of_dvd_right
            (Nat.dvd_of_mem_divisors k.2) hxd
        if k.1 = 1 then 0
        else
          (Nat.gcd
            (primitiveTwistResidue k.1 x m hxk - 1) k.1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      let hkd : k.1 ∣ d := Nat.dvd_of_mem_divisors k.2
      let hxk : x.Coprime k.1 :=
        Nat.Coprime.of_dvd_right hkd hxd
      by_cases hkone : k.1 = 1
      · simp [hkone]
      · simp only [hkone, ↓reduceIte]
        rw [sum_primitive_subtype_eq_tsum k
          (fun ψ => starRingEnd ℂ (ψ x) * ψ m)]
        exact primitive_twisted_sum_bound
          (hdsq.squarefree_of_dvd hkd)
          (hodd.of_dvd_nat hkd) hxk

/-- Reverse the finite character, pair, and bad-index sums in `M₅`. -/
theorem primitiveBadCharacterContribution_eq_sum
    {x d : ℕ} (hd : 0 < d) :
    primitiveBadCharacterContribution x d =
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) d),
        ∑ n ∈ (smoothedMIndices x q).filter
            (fun n => ¬n.Coprime d),
          (smoothedMKernel x q n : ℂ) *
            nontrivialCharSum d (fun χ =>
              starRingEnd ℂ (χ.primitiveCharacter x) *
                χ.primitiveCharacter (q.1 * q.2 * n)) := by
  unfold primitiveBadCharacterContribution
  have hfun :
      (fun χ : DirichletCharacter ℂ d =>
        starRingEnd ℂ (χ.primitiveCharacter x) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ (smoothedMIndices x q).filter
                (fun n => ¬n.Coprime d),
              (smoothedMKernel x q n : ℂ) *
                χ.primitiveCharacter (q.1 * q.2 * n)) =
        fun χ =>
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ (smoothedMIndices x q).filter
                (fun n => ¬n.Coprime d),
              (smoothedMKernel x q n : ℂ) *
                (starRingEnd ℂ (χ.primitiveCharacter x) *
                  χ.primitiveCharacter (q.1 * q.2 * n)) := by
    funext χ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hfun]
  rw [nontrivialCharSum_sum_comm hd.ne'
    ((chenPairs x).filter
      (fun q => Nat.Coprime (q.1 * q.2) d))
    (fun χ q =>
      ∑ n ∈ (smoothedMIndices x q).filter
            (fun n => ¬n.Coprime d),
        (smoothedMKernel x q n : ℂ) *
          (starRingEnd ℂ (χ.primitiveCharacter x) *
            χ.primitiveCharacter (q.1 * q.2 * n)))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [nontrivialCharSum_sum_comm hd.ne'
    ((smoothedMIndices x q).filter (fun n => ¬n.Coprime d))
    (fun χ n =>
      (smoothedMKernel x q n : ℂ) *
        (starRingEnd ℂ (χ.primitiveCharacter x) *
          χ.primitiveCharacter (q.1 * q.2 * n)))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [nontrivialCharSum_const_mul hd.ne']

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

/-- The signed nonprincipal term is bounded by the positive quantity `M₄`. -/
theorem abs_mFourSigned_le_mFour
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) :
    |mFourSigned x ε| ≤ mFour x ε := by
  unfold mFourSigned mFour
  calc
    |∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d / (Nat.totient d : ℝ) *
          (imprimitiveCharacterContribution x d).re| ≤
        ∑ d ∈ sieveModuli x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
            |(imprimitiveCharacterContribution x d).re| := by
      apply abs_sum_sieveLcmCoeff_div_totient_le
        (D := sieveModuli x ε)
        (F := fun d => (imprimitiveCharacterContribution x d).re)
        hx hx1 hε0
      intro d hd
      exact ⟨(Finset.mem_filter.mp hd).2.1,
        (Finset.mem_filter.mp hd).2.2.1⟩
    _ ≤ ∑ d ∈ sieveModuli x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
          ‖imprimitiveCharacterContribution x d‖ := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm _) (by positivity)

/-- Formula (7) without the smoothing error from formula (5). -/
theorem smoothedSieveExpansion_le
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) :
    smoothedSieveExpansion x ε ≤
      mOne x ε + |mThree x ε| + mFour x ε := by
  rw [smoothedSieveExpansion_eq]
  have hthree : -mThree x ε ≤ |mThree x ε| := neg_le_abs _
  have hfour :
      mFourSigned x ε ≤ mFour x ε :=
    (le_abs_self _).trans
      (abs_mFourSigned_le_mFour hx hx1 hε0)
  linarith

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

/-- Explicit finite bound for the bad-coprimality remainder `M₃`.  It is
obtained by collecting the sieve coefficients by their lcm, reversing the
finite sums, and charging every non-coprime modulus to a prime factor of
`p₁p₂n`. -/
theorem mThreeMajorant_le_explicit {x : ℕ} {ε : ℝ} (hx1 : 2 ≤ x) (hε : 0 ≤ ε)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    mThreeMajorant x ε ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
          (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
              (harmonic x : ℝ) ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ)) := by
  let C₀ : ℝ := (6 : ℝ) ^ (46656 : ℝ)
  let D := sieveModuli x ε
  let T := smoothedMTriples x
  let W : ((ℕ × ℕ) × ℕ) → ℝ :=
    fun z => ArithmeticFunction.vonMangoldt z.2
  let decay : ℕ → ℝ := fun d => (d : ℝ) ^ (-(5 : ℝ) / 6)
  let P : ((ℕ × ℕ) × ℕ) → ℝ := fun z =>
    ∑ p ∈ (smoothedMArgument z).primeFactors, (p : ℝ)⁻¹
  have hH0 : (0 : ℝ) ≤ (harmonic x : ℝ) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    positivity
  have hfirst :
      mThreeMajorant x ε ≤
        C₀ * ∑ d ∈ D, decay d *
          ∑ z ∈ smoothedMBadTriples x d, W z := by
    unfold mThreeMajorant
    change (∑ d ∈ D,
      (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
        |smoothedMBadMass x d|) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hcoeff := sieveCoefficient_le_decay_uniform d
    have hmass := abs_smoothedMBadMass_le
      (d := d) hxlarge
    have hcoeff0 :
        0 ≤ |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ) := by
      positivity
    have hdec0 : 0 ≤ C₀ * decay d := by
      dsimp only [C₀, decay]
      positivity
    calc
      (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
          |smoothedMBadMass x d| ≤
          (C₀ * decay d) *
            ∑ z ∈ smoothedMBadTriples x d, W z :=
        mul_le_mul hcoeff hmass (abs_nonneg _) hdec0
      _ = C₀ * (decay d *
          ∑ z ∈ smoothedMBadTriples x d, W z) := by ring
  have hswap :
      (∑ d ∈ D, decay d *
          ∑ z ∈ smoothedMBadTriples x d, W z) =
        ∑ z ∈ T, W z *
          ∑ d ∈ D.filter
              (fun d => ¬(smoothedMArgument z).Coprime d),
            decay d := by
    simp only [smoothedMBadTriples, Finset.sum_filter]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hbad : ¬(smoothedMArgument z).Coprime d
    · simp [hbad]
      ring
    · simp [hbad]
  have hinner :
      ∀ z ∈ T,
        W z * ∑ d ∈ D.filter
            (fun d => ¬(smoothedMArgument z).Coprime d), decay d ≤
          W z * ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (harmonic x : ℝ) * P z) := by
    intro z hz
    by_cases hn0 : z.2 = 0
    · simp [W, hn0]
    · have hzprod := (Finset.mem_filter.mp hz).1
      have hqmem : z.1 ∈ chenPairs x :=
        (Finset.mem_product.mp hzprod).1
      have hq' := hqmem
      simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hq'
      rcases hq'.2 with ⟨hp₁, hp₂, _⟩
      have harg :
          smoothedMArgument z ≠ 0 := by
        exact mul_ne_zero
          (mul_ne_zero hp₁.ne_zero hp₂.ne_zero) hn0
      have hmod :=
        sum_sieveModuli_decay_not_coprime_le
          (x := x) (a := smoothedMArgument z)
          (show 1 ≤ x by omega) harg hε
      exact mul_le_mul_of_nonneg_left hmod
        ArithmeticFunction.vonMangoldt_nonneg
  have htoP :
      ∑ d ∈ D, decay d *
          ∑ z ∈ smoothedMBadTriples x d, W z ≤
        (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
          ∑ z ∈ T, W z * P z := by
    rw [hswap]
    calc
      (∑ z ∈ T, W z *
          ∑ d ∈ D.filter
              (fun d => ¬(smoothedMArgument z).Coprime d),
            decay d) ≤
          ∑ z ∈ T, W z *
            ((x : ℝ) ^ ((1 : ℝ) / 12) *
              (harmonic x : ℝ) * P z) := by
        apply Finset.sum_le_sum
        intro z hz
        exact hinner z hz
      _ = (x : ℝ) ^ ((1 : ℝ) / 12) *
          (harmonic x : ℝ) * ∑ z ∈ T, W z * P z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
  have hprimeFactors :
      ∑ z ∈ T, W z * P z ≤
        ∑ q ∈ chenPairs x, ∑ n ∈ smoothedMIndices x q,
          ArithmeticFunction.vonMangoldt n *
            ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹ +
              (n.minFac : ℝ)⁻¹) := by
    change (∑ z ∈ smoothedMTriples x,
      ArithmeticFunction.vonMangoldt z.2 *
        (∑ p ∈ (z.1.1 * z.1.2 * z.2).primeFactors,
          (p : ℝ)⁻¹)) ≤ _
    rw [sum_smoothedMTriples_eq_nested x
      (fun q n => ArithmeticFunction.vonMangoldt n *
        (∑ p ∈ (q.1 * q.2 * n).primeFactors, (p : ℝ)⁻¹))]
    apply Finset.sum_le_sum
    intro q hq
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    rcases hq'.2 with ⟨hp₁, hp₂, _⟩
    apply Finset.sum_le_sum
    intro n hn
    exact vonMangoldt_mul_sum_inv_primeFactors_le hp₁ hp₂
  have hnested :
      (∑ q ∈ chenPairs x, ∑ n ∈ smoothedMIndices x q,
          ArithmeticFunction.vonMangoldt n *
            ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹ +
              (n.minFac : ℝ)⁻¹)) ≤
        6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
            (harmonic x : ℝ) ^ 2 +
          ((chenPairs x).card : ℝ) *
            ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ)) := by
    calc
      (∑ q ∈ chenPairs x, ∑ n ∈ smoothedMIndices x q,
          ArithmeticFunction.vonMangoldt n *
            ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹ +
              (n.minFac : ℝ)⁻¹)) =
          ∑ q ∈ chenPairs x,
            (((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) *
                ∑ n ∈ smoothedMIndices x q,
                  ArithmeticFunction.vonMangoldt n +
              ∑ n ∈ smoothedMIndices x q,
                ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro q hq
        calc
          (∑ n ∈ smoothedMIndices x q,
              ArithmeticFunction.vonMangoldt n *
                ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹ +
                  (n.minFac : ℝ)⁻¹)) =
              ∑ n ∈ smoothedMIndices x q,
                (((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) *
                    ArithmeticFunction.vonMangoldt n +
                  ArithmeticFunction.vonMangoldt n *
                    (n.minFac : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = (((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) *
                ∑ n ∈ smoothedMIndices x q,
                  ArithmeticFunction.vonMangoldt n +
              ∑ n ∈ smoothedMIndices x q,
                ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ q ∈ chenPairs x,
          ((((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
              Real.log x) *
                ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) +
            ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ))) := by
        apply Finset.sum_le_sum
        intro q hq
        have hΛ := sum_smoothedMIndices_vonMangoldt_le hx1 q
        have hpp :=
          sum_smoothedMIndices_vonMangoldt_div_minFac_le hx1 q
        apply add_le_add
        · calc
            ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) *
                ∑ n ∈ smoothedMIndices x q,
                  ArithmeticFunction.vonMangoldt n ≤
                ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) *
                  (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
                    Real.log x) :=
              mul_le_mul_of_nonneg_left hΛ
                (add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
                  (inv_nonneg.mpr (Nat.cast_nonneg _)))
            _ = (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
                    Real.log x) *
                  ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹) := by ring
        · exact hpp
      _ = Real.log x *
            ∑ q ∈ chenPairs x,
              (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
                ((q.1 : ℝ)⁻¹ + (q.2 : ℝ)⁻¹)) +
          ((chenPairs x).card : ℝ) *
            ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul]
        rw [Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro q hq
          ring
      _ ≤ Real.log x *
            (6 * (x : ℝ) ^ ((9 : ℝ) / 10) *
              (harmonic x : ℝ) ^ 2) +
          ((chenPairs x).card : ℝ) *
            ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (sum_pair_badPrimeFactor_weight_le x (by omega))
            (Real.log_nonneg (by
              exact_mod_cast (show 1 ≤ x by omega))))
          le_rfl
      _ = 6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
            (harmonic x : ℝ) ^ 2 +
          ((chenPairs x).card : ℝ) *
            ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ)) := by ring
  have hcard := chenPairs_card_cast_le x (show 1 ≤ x by omega)
  have htotal :
      ∑ z ∈ T, W z * P z ≤
          6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
              (harmonic x : ℝ) ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ) := by
    calc
      (∑ z ∈ T, W z * P z) ≤ _ := hprimeFactors.trans hnested
      _ ≤ 6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
              (harmonic x : ℝ) ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ) := by
        apply add_le_add le_rfl
        have hfactor0 :
            0 ≤ (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
              Real.log x * (harmonic x : ℝ) := by
          positivity
        calc
          ((chenPairs x).card : ℝ) *
              ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ)) ≤
              (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
                ((⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                  Real.log x * (harmonic x : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard hfactor0
          _ = 9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ) := by ring
  change mThreeMajorant x ε ≤ C₀ * _ * _ * _
  calc
    mThreeMajorant x ε ≤
        C₀ * ∑ d ∈ D, decay d *
          ∑ z ∈ smoothedMBadTriples x d, W z := hfirst
    _ ≤ C₀ * ((x : ℝ) ^ ((1 : ℝ) / 12) *
          (harmonic x : ℝ) * ∑ z ∈ T, W z * P z) := by
      gcongr
    _ ≤ C₀ * ((x : ℝ) ^ ((1 : ℝ) / 12) *
          (harmonic x : ℝ) *
            (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
                (harmonic x : ℝ) ^ 2 +
              9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
                (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                  Real.log x * (harmonic x : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left htotal (by
          positivity)
      · dsimp only [C₀]
        positivity
    _ = C₀ * (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
          (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
              (harmonic x : ℝ) ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ)) := by ring


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

/-- The fourth power of the logarithm is eventually absorbed by `x^(1/100)`. -/
theorem eventually_log_pow_four_le_rpow :
    ∀ᶠ n : ℕ in atTop,
      (Real.log n) ^ 4 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
  have hδ : (0 : ℝ) < 1 / 100 := by norm_num
  have hreal :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x ^ (4 : ℝ)‖ ≤
          ‖x ^ ((1 : ℝ) / 100)‖ :=
    (isLittleO_log_rpow_rpow_atTop (4 : ℝ) hδ).eventuallyLE
  have hnat :
      ∀ᶠ n : ℕ in atTop,
        ‖Real.log (n : ℝ) ^ (4 : ℝ)‖ ≤
          ‖(n : ℝ) ^ ((1 : ℝ) / 100)‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_gt_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn1)
  have hn' :
      (Real.log n) ^ 4 ≤
        |(n : ℝ) ^ ((1 : ℝ) / 100)| := by
    simpa [Real.rpow_natCast, abs_of_nonneg hlogpos.le]
      using hn
  rw [abs_of_nonneg
    (Real.rpow_nonneg hnpos.le ((1 : ℝ) / 100))] at hn'
  exact hn'

/-- The bad-coprimality remainder `M₃` has the power saving required in
equations (7)–(8). -/
theorem eventually_mThreeMajorant_le_rpow {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop,
      mThreeMajorant x ε ≤
        ((6 : ℝ) ^ (46656 : ℝ) *
          (48 + 36 * ((Real.log 2)⁻¹ + 1))) *
            (x : ℝ) ^ (1 - ε / 3) := by
  have hlogOneReal :
      ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  have hxlargeEventually :
      ∀ᶠ x : ℕ in atTop, Real.exp 3 ≤ (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 3))
  filter_upwards [eventually_log_pow_four_le_rpow, hlogOne,
    hxlargeEventually, eventually_ge_atTop 2] with
      x hlogFour hlogOne hxlarge hx2
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
  let L : ℝ := Real.log x
  let H : ℝ := harmonic x
  let K : ℝ := (Real.log 2)⁻¹ + 1
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
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
  have hHthree : L * H ^ 3 ≤ 8 * L ^ 4 := by
    calc
      L * H ^ 3 ≤ L * (2 * L) ^ 3 := by gcongr
      _ = 8 * L ^ 4 := by ring
  have hHtwo :
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ^ 2 ≤
        4 * K * L ^ 4 := by
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ^ 2 ≤
          (K * L) * L * (2 * L) ^ 2 := by gcongr
      _ = 4 * K * L ^ 4 := by ring
  have hpowFirst :
      (x : ℝ) ^ ((1 : ℝ) / 12) *
          (x : ℝ) ^ ((9 : ℝ) / 10) =
        (x : ℝ) ^ ((59 : ℝ) / 60) := by
    rw [← Real.rpow_add hxpos]
    congr 2
    norm_num
  have hpowSecond :
      (x : ℝ) ^ ((1 : ℝ) / 12) *
          (x : ℝ) ^ ((5 : ℝ) / 6) =
        (x : ℝ) ^ ((11 : ℝ) / 12) := by
    rw [← Real.rpow_add hxpos]
    congr 2
    norm_num
  have hpowMono :
      (x : ℝ) ^ ((11 : ℝ) / 12) ≤
        (x : ℝ) ^ ((59 : ℝ) / 60) :=
    Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  have hcollapse :
      (x : ℝ) ^ ((1 : ℝ) / 12) * H *
          (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * L * H ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈L / Real.log 2⌉₊ : ℝ) * L * H) ≤
        (48 + 36 * K) * (x : ℝ) ^ ((59 : ℝ) / 60) *
          L ^ 4 := by
    calc
      (x : ℝ) ^ ((1 : ℝ) / 12) * H *
          (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * L * H ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈L / Real.log 2⌉₊ : ℝ) * L * H) =
          6 * ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (x : ℝ) ^ ((9 : ℝ) / 10)) * (L * H ^ 3) +
          9 * ((x : ℝ) ^ ((1 : ℝ) / 12) *
            (x : ℝ) ^ ((5 : ℝ) / 6)) *
              ((⌈L / Real.log 2⌉₊ : ℝ) * L * H ^ 2) := by ring
      _ = 6 * (x : ℝ) ^ ((59 : ℝ) / 60) * (L * H ^ 3) +
          9 * (x : ℝ) ^ ((11 : ℝ) / 12) *
            ((⌈L / Real.log 2⌉₊ : ℝ) * L * H ^ 2) := by
        rw [hpowFirst, hpowSecond]
      _ ≤ 6 * (x : ℝ) ^ ((59 : ℝ) / 60) * (8 * L ^ 4) +
          9 * (x : ℝ) ^ ((59 : ℝ) / 60) *
            (4 * K * L ^ 4) := by
        gcongr
      _ = (48 + 36 * K) * (x : ℝ) ^ ((59 : ℝ) / 60) *
          L ^ 4 := by ring
  have hexplicit := mThreeMajorant_le_explicit
    (x := x) (ε := ε) hx2 hε0.le hxlarge
  have hfixed :
      mThreeMajorant x ε ≤
        ((6 : ℝ) ^ (46656 : ℝ) * (48 + 36 * K)) *
          (x : ℝ) ^ ((149 : ℝ) / 150) := by
    calc
      mThreeMajorant x ε ≤
          (6 : ℝ) ^ (46656 : ℝ) *
            ((x : ℝ) ^ ((1 : ℝ) / 12) * H *
              (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * L * H ^ 2 +
                9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
                  (⌈L / Real.log 2⌉₊ : ℝ) * L * H)) := by
        simpa only [L, H, mul_assoc] using hexplicit
      _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
          ((48 + 36 * K) * (x : ℝ) ^ ((59 : ℝ) / 60) *
            L ^ 4) := by gcongr
      _ ≤ (6 : ℝ) ^ (46656 : ℝ) *
          ((48 + 36 * K) * (x : ℝ) ^ ((59 : ℝ) / 60) *
            (x : ℝ) ^ ((1 : ℝ) / 100)) := by
        dsimp only [L] at hlogFour ⊢
        gcongr
      _ = ((6 : ℝ) ^ (46656 : ℝ) * (48 + 36 * K)) *
          ((x : ℝ) ^ ((59 : ℝ) / 60) *
            (x : ℝ) ^ ((1 : ℝ) / 100)) := by ring
      _ = ((6 : ℝ) ^ (46656 : ℝ) * (48 + 36 * K)) *
          (x : ℝ) ^ ((149 : ℝ) / 150) := by
        rw [← Real.rpow_add hxpos]
        congr 2
        norm_num
  calc
    mThreeMajorant x ε ≤
        ((6 : ℝ) ^ (46656 : ℝ) * (48 + 36 * K)) *
          (x : ℝ) ^ ((149 : ℝ) / 150) := hfixed
    _ ≤ ((6 : ℝ) ^ (46656 : ℝ) * (48 + 36 * K)) *
          (x : ℝ) ^ (1 - ε / 3) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
      · positivity
    _ = ((6 : ℝ) ^ (46656 : ℝ) *
          (48 + 36 * ((Real.log 2)⁻¹ + 1))) *
            (x : ℝ) ^ (1 - ε / 3) := by rfl


/-- Absolute-value form of the `M₃` power saving, with a positive uniform
constant. -/
theorem abs_mThree_power_bound
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      Even x →
        |mThree x ε| ≤ C * (x : ℝ) ^ (1 - ε / 3) := by
  refine ⟨(6 : ℝ) ^ (46656 : ℝ) *
      (48 + 36 * ((Real.log 2)⁻¹ + 1)), by positivity, ?_⟩
  filter_upwards [eventually_mThreeMajorant_le_rpow hε0 hε1,
    eventually_ge_atTop 1] with x hx hx1
  intro hxEven
  exact (abs_mThree_le_majorant hxEven hx1 hε0.le).trans hx

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
