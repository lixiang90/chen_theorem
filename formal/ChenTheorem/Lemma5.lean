/-
Preparatory definitions and elementary reductions for Lemma 5 of Chen's paper.

This file deliberately stays on the finite-sum side of the argument.  The
vertical-integral representation of `mTwo` belongs to Lemma 6.
-/
import ChenTheorem.SieveLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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

/-! ### The elementary `Ω → M` reduction -/

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

end Chen
