import ChenTheorem.Main.ShiftedSieveLemmas
import ChenTheorem.Lemma5.Smoothing

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-!
# Fixed-shift Lemma 5: Selberg-weight core

This file begins the genuinely shifted part of the nine-lemma chain.  It
establishes the support and pointwise bound for the sieve weights whose scale
is `x` but whose excluded residue is the fixed even number `h`.
-/

@[simp]
theorem shiftedSieveWeight_one (h x : ℕ) (ε : ℝ) :
    shiftedSieveWeight h x ε 1 = 1 := by
  simp [shiftedSieveWeight]

theorem shiftedSieveWeight_eq_zero_of_ne_one_of_cutoff
    {h x d : ℕ} {ε : ℝ} (hd1 : d ≠ 1)
    (hd : (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) < d) :
    shiftedSieveWeight h x ε d = 0 := by
  rw [shiftedSieveWeight, if_neg hd1, if_neg (not_le.mpr hd)]

theorem shiftedSieveWeight_eq_zero_of_not_squarefree
    {h x d : ℕ} {ε : ℝ} (hd1 : d ≠ 1) (hd : ¬Squarefree d) :
    shiftedSieveWeight h x ε d = 0 := by
  rw [shiftedSieveWeight]
  simp only [hd1, ↓reduceIte]
  split_ifs
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
  · rfl

theorem shiftedSieveWeight_support
    {h x d : ℕ} {ε : ℝ} (hd : shiftedSieveWeight h x ε d ≠ 0) :
    d = 1 ∨ (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · exact Or.inr <| by
      by_contra hcut
      exact hd (shiftedSieveWeight_eq_zero_of_ne_one_of_cutoff
        hd1 (lt_of_not_ge hcut))

theorem shiftedSieveWeight_support_squarefree
    {h x d : ℕ} {ε : ℝ} (hd : shiftedSieveWeight h x ε d ≠ 0) :
    Squarefree d := by
  by_cases hd1 : d = 1
  · simp [hd1]
  · by_contra hsq
    exact hd (shiftedSieveWeight_eq_zero_of_not_squarefree hd1 hsq)

private theorem shiftedSieveSummand_nonneg_of_coprime_even
    {h n : ℕ} (hh : Even h) (hn : 1 ≤ n) (hnh : n.Coprime h) :
    0 ≤ ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
  have hn2 : n.Coprime 2 :=
    Nat.Coprime.of_dvd_right hh.two_dvd hnh
  have hodd : Odd n := hn2.odd_of_right
  exact div_nonneg (sq_nonneg _)
    (le_of_lt (fW_pos_of_odd (by omega) hodd))

private theorem shiftedSieveProduct_mul_injective
    {h x d : ℕ} {ε : ℝ} :
    Set.InjOn (fun z : ℕ × ℕ => z.1 * z.2)
      (↑(d.divisors ×ˢ shiftedSieveNumeratorIndices h x ε d) :
        Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  have ha' := Finset.mem_product.mp ha
  have hb' := Finset.mem_product.mp hb
  have had : a.1 ∣ d := Nat.dvd_of_mem_divisors ha'.1
  have hbd : b.1 ∣ d := Nat.dvd_of_mem_divisors hb'.1
  have hakhd : a.2.Coprime (h * d) := by
    have hak := ha'.2
    simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
      Finset.mem_range] at hak
    exact hak.2.2.2
  have hbkhd : b.2.Coprime (h * d) := by
    have hbk := hb'.2
    simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
      Finset.mem_range] at hbk
    exact hbk.2.2.2
  have hakd : a.2.Coprime d :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_left d h) hakhd
  have hbkd : b.2.Coprime d :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_left d h) hbkhd
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

private theorem shiftedSieveProduct_image_subset_norm
    {h x d : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hd0 : d ≠ 0) (hdh : d.Coprime h) :
    (d.divisors ×ˢ shiftedSieveNumeratorIndices h x ε d).image
        (fun z : ℕ × ℕ => z.1 * z.2) ⊆
      shiftedSieveNormIndices h x ε := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
  have ha' := Finset.mem_product.mp ha
  have htd : a.1 ∣ d := Nat.dvd_of_mem_divisors ha'.1
  have htpos : 0 < a.1 :=
    Nat.pos_of_dvd_of_pos htd (Nat.pos_of_ne_zero hd0)
  have hk := ha'.2
  simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
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
    have hdposR : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero hd0
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
  have hth : a.1.Coprime h :=
    Nat.Coprime.of_dvd_left htd hdh
  have hkh : a.2.Coprime h :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_right h d) hk.2.2.2
  simp only [shiftedSieveNormIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.mul_pos htpos (by omega), hprodR,
    hth.mul_left hkh⟩

private theorem shiftedSieveSummand_mul_eq
    {h x d t k : ℕ} {ε : ℝ} (hd : Squarefree d)
    (ht : t ∈ d.divisors)
    (hk : k ∈ shiftedSieveNumeratorIndices h x ε d) :
    ((ArithmeticFunction.moebius (t * k) : ℤ) : ℝ) ^ 2 / fW (t * k) =
      (fW t)⁻¹ *
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k) := by
  have htd : t ∣ d := Nat.dvd_of_mem_divisors ht
  have ht0 : t ≠ 0 := by
    exact ne_of_gt (Nat.pos_of_dvd_of_pos htd
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp ht).2))
  have hk' := hk
  simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range] at hk'
  have hk0 : k ≠ 0 := by omega
  have hkd : k.Coprime d :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_left d h) hk'.2.2.2
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

/-- Shifted normalization contains the divisor-indexed copies of the
numerator sum used to define `shiftedSieveWeight`. -/
theorem totient_div_mul_shiftedSieveNumerator_le_shiftedSieveNorm
    {h x d : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hdh : d.Coprime h) :
    (Nat.totient d : ℝ) / fW d * shiftedSieveNumerator h x ε d ≤
      shiftedSieveNorm h x ε := by
  have hdodd : Odd d :=
    (Nat.Coprime.of_dvd_right hh.two_dvd hdh).odd_of_right
  let P := d.divisors ×ˢ shiftedSieveNumeratorIndices h x ε d
  let imageP := P.image (fun z : ℕ × ℕ => z.1 * z.2)
  calc
    (Nat.totient d : ℝ) / fW d * shiftedSieveNumerator h x ε d =
        (∑ t ∈ d.divisors, (fW t)⁻¹) *
          (∑ k ∈ shiftedSieveNumeratorIndices h x ε d,
            ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k) := by
      rw [sum_divisors_inv_fW_eq_totient_div hd hdodd]
      rfl
    _ = ∑ t ∈ d.divisors,
          ∑ k ∈ shiftedSieveNumeratorIndices h x ε d,
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
      exact (shiftedSieveSummand_mul_eq hd ht hk).symm
    _ = ∑ n ∈ imageP,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
      dsimp only [imageP, P]
      exact (Finset.sum_image
        (f := fun n : ℕ =>
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n)
        (g := fun z : ℕ × ℕ => z.1 * z.2)
        shiftedSieveProduct_mul_injective).symm
    _ ≤ ∑ n ∈ shiftedSieveNormIndices h x ε,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (shiftedSieveProduct_image_subset_norm hx1 hε0 hd.ne_zero hdh)
      intro n hn _
      have hn' := hn
      simp only [shiftedSieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      exact shiftedSieveSummand_nonneg_of_coprime_even
        hh hn'.2.1 hn'.2.2.2
    _ = shiftedSieveNorm h x ε := rfl

theorem shiftedSieveNorm_nonneg
    {h x : ℕ} {ε : ℝ} (hh : Even h) :
    0 ≤ shiftedSieveNorm h x ε := by
  unfold shiftedSieveNorm
  apply Finset.sum_nonneg
  intro n hn
  have hn' := hn
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hn'
  exact shiftedSieveSummand_nonneg_of_coprime_even
    hh hn'.2.1 hn'.2.2.2

theorem shiftedSieveNumerator_nonneg
    {h x d : ℕ} {ε : ℝ} (hh : Even h) :
    0 ≤ shiftedSieveNumerator h x ε d := by
  unfold shiftedSieveNumerator
  apply Finset.sum_nonneg
  intro k hk
  have hk' := hk
  simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range] at hk'
  have hkh : k.Coprime h :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_right h d) hk'.2.2.2
  exact shiftedSieveSummand_nonneg_of_coprime_even hh hk'.2.1 hkh

/-- The shifted Selberg weights retain Chen's pointwise bound
`|λ_d| ≤ 1`. -/
theorem abs_shiftedSieveWeight_le_one
    {h x d : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hdh : d.Coprime h) :
    |shiftedSieveWeight h x ε d| ≤ 1 := by
  by_cases hd1 : d = 1
  · simp [hd1]
  by_cases hcut :
      (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)
  · by_cases hdsq : Squarefree d
    · have hdodd : Odd d :=
        (Nat.Coprime.of_dvd_right hh.two_dvd hdh).odd_of_right
      have hfd : 0 < fW d :=
        fW_pos_of_odd (Nat.pos_of_ne_zero hdsq.ne_zero) hdodd
      have hA : 0 ≤ (Nat.totient d : ℝ) / fW d :=
        div_nonneg (by positivity) hfd.le
      have hN : 0 ≤ shiftedSieveNumerator h x ε d :=
        shiftedSieveNumerator_nonneg hh
      have hS0 : 0 ≤ shiftedSieveNorm h x ε :=
        shiftedSieveNorm_nonneg hh
      by_cases hS : shiftedSieveNorm h x ε = 0
      · simp [shiftedSieveWeight, hd1, hS]
      · have hSpos : 0 < shiftedSieveNorm h x ε :=
          lt_of_le_of_ne hS0 (Ne.symm hS)
        have hnorm :=
          totient_div_mul_shiftedSieveNumerator_le_shiftedSieveNorm
            hh hx1 hε0 hdsq hdh
        have hB :
            0 ≤ (Nat.totient d : ℝ) / fW d *
              (shiftedSieveNumerator h x ε d /
                shiftedSieveNorm h x ε) :=
          mul_nonneg hA (div_nonneg hN hSpos.le)
        have hB1 :
            (Nat.totient d : ℝ) / fW d *
                (shiftedSieveNumerator h x ε d /
                  shiftedSieveNorm h x ε) ≤ 1 := by
          have hdiv :
              ((Nat.totient d : ℝ) / fW d *
                  shiftedSieveNumerator h x ε d) /
                    shiftedSieveNorm h x ε ≤ 1 :=
            (div_le_one hSpos).2 hnorm
          simpa [div_eq_mul_inv, mul_assoc] using hdiv
        have hmu :
            |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
          rw [← Int.cast_abs,
            ArithmeticFunction.abs_moebius_eq_one_of_squarefree hdsq]
          norm_num
        rw [shiftedSieveWeight, if_neg hd1, if_pos hcut]
        have hform :
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                (Nat.totient d : ℝ) / fW d *
                  (shiftedSieveNumerator h x ε d /
                    shiftedSieveNorm h x ε) =
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                ((Nat.totient d : ℝ) / fW d *
                  (shiftedSieveNumerator h x ε d /
                    shiftedSieveNorm h x ε)) := by
          ring
        rw [hform, abs_mul, hmu, one_mul, abs_of_nonneg hB]
        exact hB1
    · simp [shiftedSieveWeight, hd1,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
  · rw [shiftedSieveWeight, if_neg hd1,
      if_neg (by simpa only [one_div] using hcut)]
    simp

/-! ### Uniform lcm-coefficient bounds -/

theorem sum_abs_shiftedSieveWeight_lcm_le
    {h x d : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hdh : d.Coprime h) :
    ∑ q ∈ (d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
      |shiftedSieveWeight h x ε q.1 *
        shiftedSieveWeight h x ε q.2| ≤
        3 ^ distinctPrimeFactors d := by
  calc
    ∑ q ∈ (d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
      |shiftedSieveWeight h x ε q.1 *
        shiftedSieveWeight h x ε q.2| ≤
        ∑ _q ∈ (d.divisors ×ˢ d.divisors).filter
          (fun q : ℕ × ℕ => q.1.lcm q.2 = d), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqprod := (Finset.mem_filter.mp hq).1
      have hqdiv := Finset.mem_product.mp hqprod
      have hq1h : q.1.Coprime h :=
        Nat.Coprime.of_dvd_left
          (Nat.dvd_of_mem_divisors hqdiv.1) hdh
      have hq2h : q.2.Coprime h :=
        Nat.Coprime.of_dvd_left
          (Nat.dvd_of_mem_divisors hqdiv.2) hdh
      rw [abs_mul]
      have hq1 := abs_shiftedSieveWeight_le_one hh hx1 hε0 hq1h
      have hq2 := abs_shiftedSieveWeight_le_one hh hx1 hε0 hq2h
      nlinarith [abs_nonneg (shiftedSieveWeight h x ε q.1),
        abs_nonneg (shiftedSieveWeight h x ε q.2)]
    _ = (((d.divisors ×ˢ d.divisors).filter
          (fun q : ℕ × ℕ => q.1.lcm q.2 = d)).card : ℝ) := by
      simp
    _ = 3 ^ distinctPrimeFactors d := by
      exact_mod_cast card_lcm_divisor_pairs hd

theorem abs_shiftedSieveLcmCoeff_le
    {h x d : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hd : Squarefree d) (hdh : d.Coprime h) :
    |shiftedSieveLcmCoeff h x ε d| ≤
      3 ^ distinctPrimeFactors d := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (sum_abs_shiftedSieveWeight_lcm_le hh hx1 hε0 hd hdh)

private theorem shifted_squarefree_lcm {a b : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (a.lcm b) := by
  rw [Nat.squarefree_iff_factorization_le_one
    (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
  exact sup_le (ha.natFactorization_le_one p)
    (hb.natFactorization_le_one p)

theorem shiftedSieveLcmCoeff_eq_zero_of_not_squarefree
    {h x d : ℕ} {ε : ℝ} (hd : ¬Squarefree d) :
    shiftedSieveLcmCoeff h x ε d = 0 := by
  unfold shiftedSieveLcmCoeff
  apply Finset.sum_eq_zero
  intro q hq
  have hlcm := (Finset.mem_filter.mp hq).2
  by_cases hq1 : shiftedSieveWeight h x ε q.1 = 0
  · simp [hq1]
  by_cases hq2 : shiftedSieveWeight h x ε q.2 = 0
  · simp [hq2]
  have hsq1 := shiftedSieveWeight_support_squarefree hq1
  have hsq2 := shiftedSieveWeight_support_squarefree hq2
  exact (hd (hlcm ▸ shifted_squarefree_lcm hsq1 hsq2)).elim

theorem abs_shiftedSieveLcmCoeff_le_moebius
    {h x d : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hdh : d.Coprime h) :
    |shiftedSieveLcmCoeff h x ε d| ≤
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        3 ^ distinctPrimeFactors d := by
  by_cases hd : Squarefree d
  · have hmu :
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs,
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd]
      norm_num
    rw [hmu, one_mul]
    exact abs_shiftedSieveLcmCoeff_le hh hx1 hε0 hd hdh
  · rw [shiftedSieveLcmCoeff_eq_zero_of_not_squarefree hd,
      abs_zero,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num

theorem abs_sum_shiftedSieveLcmCoeff_div_totient_le
    {h x : ℕ} {ε : ℝ} (D : Finset ℕ) (F : ℕ → ℝ)
    (hh : Even h) (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d.Coprime h) :
    |∑ d ∈ D,
        shiftedSieveLcmCoeff h x ε d /
          (Nat.totient d : ℝ) * F d| ≤
      ∑ d ∈ D,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) * |F d| := by
  calc
    |∑ d ∈ D,
        shiftedSieveLcmCoeff h x ε d /
          (Nat.totient d : ℝ) * F d| ≤
        ∑ d ∈ D,
          |shiftedSieveLcmCoeff h x ε d /
            (Nat.totient d : ℝ) * F d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d /
              (Nat.totient d : ℝ)) * |F d| := by
      apply Finset.sum_le_sum
      intro d hd
      have hddata := hD d hd
      have hcoeff :=
        abs_shiftedSieveLcmCoeff_le_moebius
          hh hx1 hε0 hddata.2
      have hφ : 0 ≤ (Nat.totient d : ℝ) := by positivity
      rw [abs_mul, abs_div, abs_of_nonneg hφ]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hcoeff hφ) (abs_nonneg _)

theorem abs_shiftedMThree_le_majorant
    {h x : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) :
    |shiftedMThree h x ε| ≤ shiftedMThreeMajorant h x ε := by
  unfold shiftedMThree shiftedMThreeMajorant
  apply abs_sum_shiftedSieveLcmCoeff_div_totient_le
      (D := shiftedSieveModuli h x ε) (F := smoothedMBadMass x)
      hh hx1 hε0
  intro d hd
  exact ⟨(Finset.mem_filter.mp hd).2.1,
    (Finset.mem_filter.mp hd).2.2.1⟩

theorem sum_shiftedSieveModuli_decay_of_dvd
    {h x p : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hp : 0 < p)
    (hε : 0 ≤ ε) :
    ∑ d ∈ (shiftedSieveModuli h x ε).filter (p ∣ ·),
        (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
      (x : ℝ) ^ ((1 : ℝ) / 12) * (p : ℝ)⁻¹ *
        (harmonic x : ℝ) := by
  let S := (shiftedSieveModuli h x ε).filter (p ∣ ·)
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

theorem sum_shiftedSieveModuli_decay_not_coprime_le
    {h x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (ha : a ≠ 0)
    (hε : 0 ≤ ε) :
    ∑ d ∈ (shiftedSieveModuli h x ε).filter
        (fun d => ¬a.Coprime d),
        (d : ℝ) ^ (-(5 : ℝ) / 6) ≤
      (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
        ∑ p ∈ a.primeFactors, (p : ℝ)⁻¹ := by
  let D := shiftedSieveModuli h x ε
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
    exact sum_shiftedSieveModuli_decay_of_dvd hx1
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

/-- Explicit finite bound for the shifted bad-coprimality remainder `M₃`.
The proof is uniform in the fixed shift: after reversing the finite sums, the
only modulus input is the preceding decay estimate for `shiftedSieveModuli`. -/
theorem shiftedMThreeMajorant_le_explicit {h x : ℕ} {ε : ℝ}
    (hx1 : 2 ≤ x) (hε : 0 ≤ ε)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    shiftedMThreeMajorant h x ε ≤
      (6 : ℝ) ^ (46656 : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
          (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
              (harmonic x : ℝ) ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ)) := by
  let C₀ : ℝ := (6 : ℝ) ^ (46656 : ℝ)
  let D := shiftedSieveModuli h x ε
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
      shiftedMThreeMajorant h x ε ≤
        C₀ * ∑ d ∈ D, decay d *
          ∑ z ∈ smoothedMBadTriples x d, W z := by
    unfold shiftedMThreeMajorant
    change (∑ d ∈ D,
      (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
        |smoothedMBadMass x d|) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hcoeff := sieveCoefficient_le_decay_uniform d
    have hmass := abs_smoothedMBadMass_le (d := d) hxlarge
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
      have harg : smoothedMArgument z ≠ 0 := by
        exact mul_ne_zero
          (mul_ne_zero hp₁.ne_zero hp₂.ne_zero) hn0
      have hmod :=
        sum_shiftedSieveModuli_decay_not_coprime_le
          (h := h) (x := x) (a := smoothedMArgument z)
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
          exact mul_nonneg
            (mul_nonneg (by positivity)
              (Real.log_nonneg (by
                exact_mod_cast (show 1 ≤ x by omega)))) hH0
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
  change shiftedMThreeMajorant h x ε ≤ C₀ * _ * _ * _
  calc
    shiftedMThreeMajorant h x ε ≤
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
      · exact mul_le_mul_of_nonneg_left htotal
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) hH0)
      · dsimp only [C₀]
        positivity
    _ = C₀ * (x : ℝ) ^ ((1 : ℝ) / 12) * (harmonic x : ℝ) *
          (6 * (x : ℝ) ^ ((9 : ℝ) / 10) * Real.log x *
              (harmonic x : ℝ) ^ 2 +
            9 * (x : ℝ) ^ ((5 : ℝ) / 6) *
              (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
                Real.log x * (harmonic x : ℝ)) := by ring

theorem eventually_shiftedMThreeMajorant_le_rpow (h : ℕ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop,
      shiftedMThreeMajorant h x ε ≤
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
  have hexplicit := shiftedMThreeMajorant_le_explicit
    (h := h) (x := x) (ε := ε) hx2 hε0.le hxlarge
  have hfixed :
      shiftedMThreeMajorant h x ε ≤
        ((6 : ℝ) ^ (46656 : ℝ) * (48 + 36 * K)) *
          (x : ℝ) ^ ((149 : ℝ) / 150) := by
    calc
      shiftedMThreeMajorant h x ε ≤
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
    shiftedMThreeMajorant h x ε ≤
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

/-- Absolute-value form of the shifted `M₃` power saving. -/
theorem abs_shiftedMThree_power_bound
    {h : ℕ} (hh : Even h) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      |shiftedMThree h x ε| ≤ C * (x : ℝ) ^ (1 - ε / 3) := by
  refine ⟨(6 : ℝ) ^ (46656 : ℝ) *
      (48 + 36 * ((Real.log 2)⁻¹ + 1)), by positivity, ?_⟩
  filter_upwards [eventually_shiftedMThreeMajorant_le_rpow h hε0 hε1,
    eventually_ge_atTop 1] with x hx hx1
  exact (abs_shiftedMThree_le_majorant hh hx1 hε0.le).trans hx

/-! ### The elementary shifted `Ω → M` small-tail reduction -/

theorem shiftedOmegaSmallThirdPrimes_card_le
    (h x : ℕ) (ε : ℝ) (q : ℕ × ℕ) :
    (shiftedOmegaSmallThirdPrimes h x ε q).card ≤
      ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊ := by
  calc
    (shiftedOmegaSmallThirdPrimes h x ε q).card ≤
        (Finset.range
          ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_range]
      apply Nat.lt_ceil.mpr
      exact (Finset.mem_filter.mp hp).2
    _ = ⌈((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ (1 - ε)⌉₊ := by
      simp

theorem shiftedSieveMSmallTail_le_majorant
    (h x : ℕ) (ε : ℝ) :
    shiftedSieveMSmallTail h x ε ≤
      shiftedSieveMSmallMajorant x ε := by
  unfold shiftedSieveMSmallTail shiftedSieveMSmallMajorant
  apply Finset.sum_le_sum
  intro q _
  exact shiftedOmegaSmallThirdPrimes_card_le h x ε q

theorem shiftedSieveMSmallMajorant_eq
    (x : ℕ) (ε : ℝ) :
    shiftedSieveMSmallMajorant x ε = sieveMSmallMajorant x ε := rfl

theorem eventually_shiftedSieveMSmallTail_le_rpow
    (h : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ x : ℕ in atTop,
      (shiftedSieveMSmallTail h x ε : ℝ) ≤
        2 * (x : ℝ) ^ (1 - ε / 12) := by
  have hδ : 0 < ε / 12 := by positivity
  filter_upwards [eventually_harmonic_sq_le_rpow hδ,
    eventually_gt_atTop 0] with x hH hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have htailNat := shiftedSieveMSmallTail_le_majorant h x ε
  have htail :
      (shiftedSieveMSmallTail h x ε : ℝ) ≤
        (shiftedSieveMSmallMajorant x ε : ℝ) := by
    exact_mod_cast htailNat
  have hmajorant :
      (shiftedSieveMSmallMajorant x ε : ℝ) ≤
        2 * (x : ℝ) ^ (1 - ε / 12) := by
    rw [shiftedSieveMSmallMajorant_eq]
    calc
      (sieveMSmallMajorant x ε : ℝ) ≤
          2 * (x : ℝ) ^ (1 - ε / 6) * (harmonic x : ℝ) ^ 2 :=
        sieveMSmallMajorant_le_harmonic x hε0.le hε1
      _ ≤ 2 * (x : ℝ) ^ (1 - ε / 6) *
          (x : ℝ) ^ (ε / 12) := by
        exact mul_le_mul_of_nonneg_left hH (by positivity)
      _ = 2 * (x : ℝ) ^ (1 - ε / 12) := by
        rw [mul_assoc, ← Real.rpow_add hxpos]
        congr 2
        ring_nf
  exact htail.trans hmajorant

/-- The shifted small-third-prime tail is negligible on the logarithmic
scale required by Lemma 5. -/
theorem shiftedSieveMSmallTail_le
    (h : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (shiftedSieveMSmallTail h x ε : ℝ) ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_shiftedSieveMSmallTail_le_rpow h hε
      (hε'.trans (by norm_num)),
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := ε / 12) (r := (2.01 : ℝ)) (by positivity)] with
      x htail hpower
  exact htail.trans (by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 2)))

/-! ### Shifted character orthogonality and equation (6) -/

theorem shiftedSmoothedM_equation_six
    {h x d : ℕ} (hd : 0 < d) (hhd : h.Coprime d) :
    ∑ z ∈ smoothedMTriples x,
        (smoothedMKernel x z.1 z.2 : ℂ) *
          ((if h ≡ smoothedMArgument z [MOD d] then 1 else 0 : ℝ) : ℂ) =
      ((∑ z ∈ smoothedMGoodTriples x d,
          (smoothedMKernel x z.1 z.2 : ℂ)) +
        nontrivialCharSum d (fun χ =>
          χ (h : ZMod d)⁻¹ *
            ∑ z ∈ smoothedMTriples x,
              (smoothedMKernel x z.1 z.2 : ℂ) *
                χ (smoothedMArgument z : ZMod d))) /
        (Nat.totient d : ℂ) := by
  rw [weighted_residueSum_eq_filter_coprime hhd
    (smoothedMTriples x) smoothedMArgument
    (fun z => (smoothedMKernel x z.1 z.2 : ℂ))]
  rw [show (smoothedMTriples x).filter
      (fun z => (smoothedMArgument z).Coprime d) =
        smoothedMGoodTriples x d by rfl]
  rw [weighted_mappedResidueSum_eq_principal_add_nontrivial
    hd hhd (smoothedMGoodTriples x d) smoothedMArgument
    (fun z => smoothedMKernel x z.1 z.2)]
  · congr 3
    funext χ
    congr 1
    exact weighted_characterSum_filter_coprime χ
      (smoothedMTriples x) smoothedMArgument
      (fun z => (smoothedMKernel x z.1 z.2 : ℂ))
  · intro z hz
    exact (Finset.mem_filter.mp hz).2

theorem nontrivialCharSum_eq_shiftedImprimitiveContribution
    {h x d : ℕ} (hd : 0 < d) (hhd : h.Coprime d) :
    nontrivialCharSum d (fun χ =>
      χ (h : ZMod d)⁻¹ *
        ∑ z ∈ smoothedMTriples x,
          (smoothedMKernel x z.1 z.2 : ℂ) *
            χ (smoothedMArgument z : ZMod d)) =
      shiftedImprimitiveCharacterContribution h x d := by
  unfold shiftedImprimitiveCharacterContribution
  simp only [nontrivialCharSum, dif_neg hd.ne']
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hχone : χ = 1
  · simp [hχone]
  simp only [hχone, ↓reduceIte]
  congr 1
  · have hhunit : IsUnit (h : ZMod d) :=
      (ZMod.isUnit_iff_coprime h d).2 hhd
    obtain ⟨u, hu⟩ := hhunit
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

theorem shiftedSmoothedResidueMass_eq
    {h x d : ℕ} (hd : 0 < d) (hhd : h.Coprime d) :
    ∑ z ∈ smoothedMTriples x,
        smoothedMKernel x z.1 z.2 *
          (if h ≡ smoothedMArgument z [MOD d] then 1 else 0) =
      (smoothedMGoodMass x d +
          (shiftedImprimitiveCharacterContribution h x d).re) /
        (Nat.totient d : ℝ) := by
  have h6 := shiftedSmoothedM_equation_six (x := x) hd hhd
  rw [nontrivialCharSum_eq_shiftedImprimitiveContribution hd hhd] at h6
  have hre := congrArg Complex.re h6
  have hφ : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  simpa [smoothedMGoodMass, div_eq_mul_inv, hφ] using hre

/-- Shifted equations (6)--(7), before absolute values. -/
theorem shiftedSmoothedSieveExpansion_eq
    (h x : ℕ) (ε : ℝ) :
    shiftedSmoothedSieveExpansion h x ε =
      shiftedMOne h x ε - shiftedMThree h x ε +
        shiftedMFourSigned h x ε := by
  unfold shiftedSmoothedSieveExpansion shiftedMOne shiftedMThree
    shiftedMFourSigned
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hddata := (Finset.mem_filter.mp hd).2
  have hdpos : 0 < d := by omega
  have hres := shiftedSmoothedResidueMass_eq
    (x := x) hdpos hddata.2.1.symm
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

theorem abs_shiftedMFourSigned_le_shiftedMFour
    {h x : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) :
    |shiftedMFourSigned h x ε| ≤ shiftedMFour h x ε := by
  unfold shiftedMFourSigned shiftedMFour
  calc
    |∑ d ∈ shiftedSieveModuli h x ε,
        shiftedSieveLcmCoeff h x ε d / (Nat.totient d : ℝ) *
          (shiftedImprimitiveCharacterContribution h x d).re| ≤
        ∑ d ∈ shiftedSieveModuli h x ε,
          (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
              3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
            |(shiftedImprimitiveCharacterContribution h x d).re| := by
      apply abs_sum_shiftedSieveLcmCoeff_div_totient_le
        (D := shiftedSieveModuli h x ε)
        (F := fun d =>
          (shiftedImprimitiveCharacterContribution h x d).re)
        hh hx1 hε0
      intro d hd
      exact ⟨(Finset.mem_filter.mp hd).2.1,
        (Finset.mem_filter.mp hd).2.2.1⟩
    _ ≤ ∑ d ∈ shiftedSieveModuli h x ε,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            3 ^ distinctPrimeFactors d / (Nat.totient d : ℝ)) *
          ‖shiftedImprimitiveCharacterContribution h x d‖ := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm _) (by positivity)

/-- Shifted formula (7), before splitting `M₄` into `M₂ + M₅`. -/
theorem shiftedSmoothedSieveExpansion_le
    {h x : ℕ} {ε : ℝ} (hh : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) :
    shiftedSmoothedSieveExpansion h x ε ≤
      shiftedMOne h x ε + |shiftedMThree h x ε| +
        shiftedMFour h x ε := by
  rw [shiftedSmoothedSieveExpansion_eq]
  have hthree : -shiftedMThree h x ε ≤
      |shiftedMThree h x ε| := neg_le_abs _
  have hfour : shiftedMFourSigned h x ε ≤
      shiftedMFour h x ε :=
    (le_abs_self _).trans
      (abs_shiftedMFourSigned_le_shiftedMFour hh hx1 hε0)
  linarith

theorem shiftedMFour_le_shiftedMTwo_add_shiftedMFive
    (h x : ℕ) (ε : ℝ) :
    shiftedMFour h x ε ≤
      shiftedMTwo h x ε + shiftedMFive h x ε := by
  unfold shiftedMFour shiftedMTwo shiftedMFive
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  let A : ℝ :=
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ distinctPrimeFactors d / (Nat.totient d : ℝ)
  let F : ℂ := shiftedImprimitiveCharacterContribution h x d
  let G : ℂ := shiftedPrimitiveCharacterContribution h x d
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have htriangle : ‖F‖ ≤ ‖G‖ + ‖F - G‖ := by
    have hnorm := norm_add_le G (F - G)
    simpa [add_sub_cancel_left] using hnorm
  change A * ‖F‖ ≤ A * ‖G‖ + A * ‖F - G‖
  calc
    A * ‖F‖ ≤ A * (‖G‖ + ‖F - G‖) :=
      mul_le_mul_of_nonneg_left htriangle hA
    _ = A * ‖G‖ + A * ‖F - G‖ := by ring

/-! ### Shifted square Selberg sieve -/

theorem shiftedSieveDivisorSum_eq_sum_universe
    (h x : ℕ) (ε : ℝ) (a : ℕ) :
    shiftedSieveDivisorSum h x ε a =
      ∑ d ∈ shiftedSieveDivisorUniverse h x,
        if d ∣ a then shiftedSieveWeight h x ε d else 0 := by
  unfold shiftedSieveDivisorSum
  rw [Finset.sum_filter]

theorem shiftedLcm_mem_sieveModuli_of_weight_mul_ne_zero
    {h x d₁ d₂ : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hd₁ : d₁ ∈ shiftedSieveDivisorUniverse h x)
    (hd₂ : d₂ ∈ shiftedSieveDivisorUniverse h x)
    (hweight :
      shiftedSieveWeight h x ε d₁ *
        shiftedSieveWeight h x ε d₂ ≠ 0) :
    d₁.lcm d₂ ∈ shiftedSieveModuli h x ε := by
  have hd₁data := (Finset.mem_filter.mp hd₁).2
  have hd₂data := (Finset.mem_filter.mp hd₂).2
  have hd₁pos : 0 < d₁ := by omega
  have hd₂pos : 0 < d₂ := by omega
  have hweight₁ : shiftedSieveWeight h x ε d₁ ≠ 0 := by
    intro hz
    exact hweight (by rw [hz, zero_mul])
  have hweight₂ : shiftedSieveWeight h x ε d₂ ≠ 0 := by
    intro hz
    exact hweight (by rw [hz, mul_zero])
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hexp0 : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
  have hRone :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) :=
    Real.one_le_rpow hxone hexp0
  have hd₁cut :
      (d₁ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases shiftedSieveWeight_support hweight₁ with heq | hcut
    · simpa only [heq, Nat.cast_one] using hRone
    · exact hcut
  have hd₂cut :
      (d₂ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rcases shiftedSieveWeight_support hweight₂ with heq | hcut
    · simpa only [heq, Nat.cast_one] using hRone
    · exact hcut
  have hlcmpos : 0 < d₁.lcm d₂ := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hz' := Nat.lcm_eq_zero_iff.mp hz
    omega
  have hlcmcop : (d₁.lcm d₂).Coprime h :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul d₁ d₂)
      (hd₁data.2.mul_left hd₂data.2)
  have hlcmle : d₁.lcm d₂ ≤ d₁ * d₂ :=
    Nat.lcm_le_mul hd₁pos hd₂pos
  have hprod :
      ((d₁ * d₂ : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    norm_num only [Nat.cast_mul]
    exact mul_le_mul hd₁cut hd₂cut (by positivity) (by positivity)
  have hpow :
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) =
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hlcmcut :
      (d₁.lcm d₂ : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    calc
      (d₁.lcm d₂ : ℝ) ≤ (d₁ * d₂ : ℕ) := by
        exact_mod_cast hlcmle
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) *
          (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := hprod
      _ = (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hpow
  have hexp_le : (1 : ℝ) / 2 - ε ≤ 1 := by linarith
  have hlcmx : d₁.lcm d₂ ≤ x := by
    have hpowx :
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ x := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hxone hexp_le
    exact_mod_cast hlcmcut.trans hpowx
  simp only [shiftedSieveModuli, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by exact ⟨by omega, hlcmcop, hlcmcut⟩⟩

/-- On an `x^(1/4)`-rough positive shifted difference, only `λ₁` survives. -/
theorem shiftedSieveDivisorSum_eq_one_of_rough
    {h x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (ha : chenRough x a) :
    shiftedSieveDivisorSum h x ε a = 1 := by
  unfold shiftedSieveDivisorSum
  let S : Finset ℕ :=
    (shiftedSieveDivisorUniverse h x).filter (fun d => d ∣ a)
  have h1S : 1 ∈ S := by
    simp only [S, shiftedSieveDivisorUniverse, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨⟨by omega, by simp⟩, by simp⟩
  calc
    ∑ d ∈ (shiftedSieveDivisorUniverse h x).filter (fun d => d ∣ a),
        shiftedSieveWeight h x ε d =
      ∑ d ∈ S, shiftedSieveWeight h x ε d := by rfl
    _ = shiftedSieveWeight h x ε 1 := by
      apply Finset.sum_eq_single 1
      · intro d hdS hd1
        by_contra hweight
        have hddata := (Finset.mem_filter.mp hdS).1
        have hduniv := (Finset.mem_filter.mp hddata).2
        have hda := (Finset.mem_filter.mp hdS).2
        have hdpos : 0 < d := by omega
        obtain ⟨p, hp, hpd⟩ :=
          Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have hp_le_d : p ≤ d := Nat.le_of_dvd hdpos hpd
        have hdcut :=
          (shiftedSieveWeight_support hweight).resolve_left hd1
        have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx1
        have hexp :
            (1 : ℝ) / 4 - ε / 2 ≤ (1 : ℝ) / 4 := by
          linarith
        have hdquarter :
            (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
          hdcut.trans
            (Real.rpow_le_rpow_of_exponent_le hxone hexp)
        have hpquarter :
            (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
          (show (p : ℝ) ≤ d by exact_mod_cast hp_le_d).trans
            hdquarter
        exact ha p hp hpquarter (dvd_trans hpd hda)
      · intro hnot
        exact (hnot h1S).elim
    _ = 1 := shiftedSieveWeight_one h x ε

theorem shiftedSieveDivisorSum_sq_eq_lcm_sum
    {h x a : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    (shiftedSieveDivisorSum h x ε a) ^ 2 =
      ∑ d ∈ shiftedSieveModuli h x ε,
        shiftedSieveLcmCoeff h x ε d *
          (if d ∣ a then 1 else 0) := by
  let U : Finset ℕ := shiftedSieveDivisorUniverse h x
  let P : Finset (ℕ × ℕ) := U ×ˢ U
  let f : ℕ × ℕ → ℝ := fun q =>
    (if q.1 ∣ a then shiftedSieveWeight h x ε q.1 else 0) *
      (if q.2 ∣ a then shiftedSieveWeight h x ε q.2 else 0)
  have hsquare :
      (shiftedSieveDivisorSum h x ε a) ^ 2 =
        ∑ q ∈ P, f q := by
    rw [shiftedSieveDivisorSum_eq_sum_universe, pow_two,
      Finset.sum_mul_sum]
    simp only [P, U, f, Finset.sum_product]
  have hsupport :
      ∑ q ∈ P, f q =
        ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ shiftedSieveModuli h x ε),
            f q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hlcm :
        q.1.lcm q.2 ∈ shiftedSieveModuli h x ε
    · simp [hlcm]
    · rw [if_neg hlcm]
      by_contra hf
      have hqdata := Finset.mem_product.mp hq
      have hweight :
          shiftedSieveWeight h x ε q.1 *
            shiftedSieveWeight h x ε q.2 ≠ 0 := by
        apply mul_ne_zero
        · intro hw
          apply hf
          dsimp only [f]
          simp [hw]
        · intro hw
          apply hf
          dsimp only [f]
          simp [hw]
      exact hlcm
        (shiftedLcm_mem_sieveModuli_of_weight_mul_ne_zero
          hx1 hε0 hεhalf
          (by simpa only [U] using hqdata.1)
          (by simpa only [U] using hqdata.2) hweight)
  have hfiber :
      ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ shiftedSieveModuli h x ε),
            f q =
        ∑ d ∈ shiftedSieveModuli h x ε,
          ∑ q ∈ P.filter (fun q => q.1.lcm q.2 = d),
            f q := by
    symm
    exact Finset.sum_fiberwise_eq_sum_filter P
      (shiftedSieveModuli h x ε) (fun q => q.1.lcm q.2) f
  calc
    (shiftedSieveDivisorSum h x ε a) ^ 2 =
        ∑ q ∈ P, f q := hsquare
    _ = ∑ q ∈ P.filter
          (fun q => q.1.lcm q.2 ∈ shiftedSieveModuli h x ε),
            f q := hsupport
    _ = ∑ d ∈ shiftedSieveModuli h x ε,
          ∑ q ∈ P.filter (fun q => q.1.lcm q.2 = d),
            f q := hfiber
    _ = ∑ d ∈ shiftedSieveModuli h x ε,
        shiftedSieveLcmCoeff h x ε d *
          (if d ∣ a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hddata := (Finset.mem_filter.mp hd).2
      have hdpos : 0 < d := by omega
      have hdle : d ≤ x := by
        have hdrange := (Finset.mem_filter.mp hd).1
        have hdlt := Finset.mem_range.mp hdrange
        omega
      have hfin :
          P.filter (fun q => q.1.lcm q.2 = d) =
            (d.divisors ×ˢ d.divisors).filter
              (fun q => q.1.lcm q.2 = d) := by
        ext q
        simp only [P, U, shiftedSieveDivisorUniverse,
          Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        constructor
        · intro hq
          rcases hq with
            ⟨⟨⟨hq₁range, hq₁pos, hq₁cop⟩,
              ⟨hq₂range, hq₂pos, hq₂cop⟩⟩, hlcm⟩
          have hq₁d : q.1 ∣ d := by
            rw [← hlcm]
            exact Nat.dvd_lcm_left q.1 q.2
          have hq₂d : q.2 ∣ d := by
            rw [← hlcm]
            exact Nat.dvd_lcm_right q.1 q.2
          exact ⟨⟨Nat.mem_divisors.mpr ⟨hq₁d, hdpos.ne'⟩,
            Nat.mem_divisors.mpr ⟨hq₂d, hdpos.ne'⟩⟩, hlcm⟩
        · intro hq
          rcases hq with ⟨⟨hq₁mem, hq₂mem⟩, hlcm⟩
          have hq₁d := Nat.dvd_of_mem_divisors hq₁mem
          have hq₂d := Nat.dvd_of_mem_divisors hq₂mem
          have hq₁pos : 1 ≤ q.1 :=
            Nat.pos_of_dvd_of_pos hq₁d hdpos
          have hq₂pos : 1 ≤ q.2 :=
            Nat.pos_of_dvd_of_pos hq₂d hdpos
          have hq₁cop := Nat.Coprime.of_dvd_left hq₁d hddata.2.1
          have hq₂cop := Nat.Coprime.of_dvd_left hq₂d hddata.2.1
          have hq₁le : q.1 ≤ d := Nat.le_of_dvd hdpos hq₁d
          have hq₂le : q.2 ≤ d := Nat.le_of_dvd hdpos hq₂d
          exact
            ⟨⟨⟨by omega, hq₁pos, hq₁cop⟩,
              ⟨by omega, hq₂pos, hq₂cop⟩⟩, hlcm⟩
      rw [hfin, shiftedSieveLcmCoeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hlcm := (Finset.mem_filter.mp hq).2
      have hqdiv := Finset.mem_product.mp
        (Finset.mem_filter.mp hq).1
      have hq₁d := Nat.dvd_of_mem_divisors hqdiv.1
      have hq₂d := Nat.dvd_of_mem_divisors hqdiv.2
      by_cases hda : d ∣ a
      · have hq₁a : q.1 ∣ a := dvd_trans hq₁d hda
        have hq₂a : q.2 ∣ a := dvd_trans hq₂d hda
        simp [f, hda, hq₁a, hq₂a]
      · have hnotboth : ¬(q.1 ∣ a ∧ q.2 ∣ a) := by
          intro hboth
          apply hda
          rw [← hlcm]
          exact Nat.lcm_dvd hboth.1 hboth.2
        rcases not_and_or.mp hnotboth with hq₁a | hq₂a
        · simp [f, hda, hq₁a]
        · simp [f, hda, hq₂a]

theorem shifted_modEq_iff_dvd_dist (d a b : ℕ) :
    a ≡ b [MOD d] ↔ d ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact Nat.modEq_iff_dvd' hab
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact Nat.ModEq.comm.trans (Nat.modEq_iff_dvd' hba)

theorem shiftedSmoothedRoughM_eq_kernel_sum (h x : ℕ) :
    shiftedSmoothedRoughM h x =
      ∑ q ∈ chenPairs x,
        ∑ n ∈ shiftedSieveMIndices h x q,
          smoothedMKernel x q n := rfl

theorem shiftedSmoothedRoughM_le_squareSieveExpansion
    {h x : ℕ} {ε : ℝ} (hx : 1 < x) (hε0 : 0 ≤ ε) :
    shiftedSmoothedRoughM h x ≤
      shiftedSquareSieveExpansion h x ε := by
  rw [shiftedSmoothedRoughM_eq_kernel_sum]
  unfold shiftedSquareSieveExpansion
  apply Finset.sum_le_sum
  intro q hq
  have hsubset :
      shiftedSieveMIndices h x q ⊆ smoothedMIndices x q := by
    intro n hn
    have hn' := hn
    simp only [shiftedSieveMIndices, Finset.mem_filter,
      Finset.mem_range] at hn'
    simp only [smoothedMIndices, Finset.mem_filter, Finset.mem_range]
    exact ⟨hn'.1, hn'.2.1⟩
  calc
    ∑ n ∈ shiftedSieveMIndices h x q, smoothedMKernel x q n =
        ∑ n ∈ shiftedSieveMIndices h x q,
          smoothedMKernel x q n *
            (shiftedSieveDivisorSum h x ε
              (Nat.dist h (q.1 * q.2 * n))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := hn
      simp only [shiftedSieveMIndices, Finset.mem_filter,
        Finset.mem_range, shiftedRough] at hn'
      have hdist :
          Nat.dist h (q.1 * q.2 * n) = q.1 * q.2 * n - h :=
        Nat.dist_eq_sub_of_le hn'.2.2.1.le
      rw [hdist, shiftedSieveDivisorSum_eq_one_of_rough
        (show 1 ≤ x by omega) hε0 hn'.2.2.2]
      ring
    _ ≤ ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            (shiftedSieveDivisorSum h x ε
              (Nat.dist h (q.1 * q.2 * n))) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn _hnrough
      exact mul_nonneg (smoothedMKernel_nonneg hx hq) (sq_nonneg _)

theorem shiftedSquareSieveExpansion_eq_smoothedSieveExpansion
    {h x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    shiftedSquareSieveExpansion h x ε =
      shiftedSmoothedSieveExpansion h x ε := by
  unfold shiftedSquareSieveExpansion shiftedSmoothedSieveExpansion
  calc
    ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            (shiftedSieveDivisorSum h x ε
              (Nat.dist h (q.1 * q.2 * n))) ^ 2 =
      ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q,
          smoothedMKernel x q n *
            ∑ d ∈ shiftedSieveModuli h x ε,
              shiftedSieveLcmCoeff h x ε d *
                (if h ≡ q.1 * q.2 * n [MOD d]
                  then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro n hn
      have hsquare :=
        shiftedSieveDivisorSum_sq_eq_lcm_sum
          (h := h) (x := x) (a := Nat.dist h (q.1 * q.2 * n))
          (ε := ε) hx1 hε0 hεhalf
      rw [hsquare]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hiff := shifted_modEq_iff_dvd_dist d h (q.1 * q.2 * n)
      by_cases hmod : h ≡ q.1 * q.2 * n [MOD d]
      · have hdvd := hiff.mp hmod
        simp [hmod, hdvd]
      · have hndvd : ¬d ∣ Nat.dist h (q.1 * q.2 * n) := by
          intro hdvd
          exact hmod (hiff.mpr hdvd)
        simp [hmod, hndvd]
    _ = ∑ d ∈ shiftedSieveModuli h x ε,
        shiftedSieveLcmCoeff h x ε d *
          ∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              smoothedMKernel x q n *
                (if h ≡ q.1 * q.2 * n [MOD d]
                  then 1 else 0) := by
      calc
        (∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              smoothedMKernel x q n *
                ∑ d ∈ shiftedSieveModuli h x ε,
                  shiftedSieveLcmCoeff h x ε d *
                    (if h ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) =
          ∑ q ∈ chenPairs x,
            ∑ n ∈ smoothedMIndices x q,
              ∑ d ∈ shiftedSieveModuli h x ε,
                smoothedMKernel x q n *
                  (shiftedSieveLcmCoeff h x ε d *
                    (if h ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro q hq
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
        _ = ∑ q ∈ chenPairs x,
            ∑ d ∈ shiftedSieveModuli h x ε,
              ∑ n ∈ smoothedMIndices x q,
                smoothedMKernel x q n *
                  (shiftedSieveLcmCoeff h x ε d *
                    (if h ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.sum_comm]
        _ = ∑ d ∈ shiftedSieveModuli h x ε,
            ∑ q ∈ chenPairs x,
              ∑ n ∈ smoothedMIndices x q,
                smoothedMKernel x q n *
                  (shiftedSieveLcmCoeff h x ε d *
                    (if h ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0)) := by
            rw [Finset.sum_comm]
        _ = ∑ d ∈ shiftedSieveModuli h x ε,
            shiftedSieveLcmCoeff h x ε d *
              ∑ q ∈ chenPairs x,
                ∑ n ∈ smoothedMIndices x q,
                  smoothedMKernel x q n *
                    (if h ≡ q.1 * q.2 * n [MOD d]
                      then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
    _ = ∑ d ∈ shiftedSieveModuli h x ε,
        shiftedSieveLcmCoeff h x ε d *
          ∑ z ∈ smoothedMTriples x,
            smoothedMKernel x z.1 z.2 *
              (if h ≡ smoothedMArgument z [MOD d]
                then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      exact (sum_smoothedMTriples_eq_nested x
        (fun q n =>
          smoothedMKernel x q n *
            (if h ≡ q.1 * q.2 * n [MOD d]
              then 1 else 0))).symm

theorem shiftedSmoothedRoughM_le_smoothedSieveExpansion
    {h x : ℕ} {ε : ℝ} (hx : 1 < x)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    shiftedSmoothedRoughM h x ≤
      shiftedSmoothedSieveExpansion h x ε := by
  calc
    shiftedSmoothedRoughM h x ≤
        shiftedSquareSieveExpansion h x ε :=
      shiftedSmoothedRoughM_le_squareSieveExpansion hx hε0
    _ = shiftedSmoothedSieveExpansion h x ε :=
      shiftedSquareSieveExpansion_eq_smoothedSieveExpansion
        (show 1 ≤ x by omega) hε0 hεhalf

/-! ### Fixed-shift smoothing loss -/

/-- Inserting `chenPhi` gives the same exact decomposition as in the
unshifted argument; only the rough index set changes. -/
theorem shiftedSieveM_eq_smoothedRoughM_add_smoothingError
    (h x : ℕ) :
    shiftedSieveM h x = shiftedSmoothedRoughM h x +
      shiftedSieveMSmoothingError h x := by
  unfold shiftedSieveM shiftedSmoothedRoughM
    shiftedSieveMSmoothingError smoothedMKernel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [mul_assoc]
  rw [← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem shiftedSieveMSmoothingError_nonneg
    {h x : ℕ} (hx : 1 < x) :
    0 ≤ shiftedSieveMSmoothingError h x := by
  unfold shiftedSieveMSmoothingError
  apply Finset.sum_nonneg
  intro q hq
  have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
    one_lt_pairQuotient hq
  have hlog : 0 < Real.log
      ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
    Real.log_pos hY
  apply mul_nonneg (inv_nonneg.mpr hlog.le)
  apply Finset.sum_nonneg
  intro n hn
  have hy : 0 ≤
      (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (sub_nonneg.mpr (chenPhi_le_one x
      (by exact_mod_cast hx) hy))

theorem shiftedSmoothingBoundaryMass_eq_small_add_large
    (h x : ℕ) :
    shiftedSmoothingBoundaryMass h x =
      shiftedSmoothingBoundarySmallBaseMass h x +
        shiftedSmoothingBoundaryLargeBaseMass h x := by
  unfold shiftedSmoothingBoundaryMass
    shiftedSmoothingBoundarySmallBaseMass
    shiftedSmoothingBoundaryLargeBaseMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add]
  congr 1
  simpa only using (Finset.sum_filter_add_sum_filter_not
    (s := shiftedSmoothingBoundaryIndices h x q)
    (p := fun n =>
      (n.minFac : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100))
    (f := fun n => ArithmeticFunction.vonMangoldt n)).symm

/-- Lemma 1 splits the shifted smoothing error into its uniform interior
loss and the thin transition boundary. -/
theorem shiftedSieveMSmoothingError_le_interior_add_boundary
    {h x : ℕ} (hx1 : 1 < x)
    (hxlog : (10 : ℝ) ^ 4 ≤ Real.log x) :
    shiftedSieveMSmoothingError h x ≤
      (x : ℝ) ^ (-(0.1 : ℝ)) * shiftedSieveM h x +
        shiftedSmoothingBoundaryMass h x := by
  unfold shiftedSieveMSmoothingError shiftedSieveM
    shiftedSmoothingBoundaryMass
  calc
    ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n *
              (1 - chenPhi x
                ((x : ℝ) / ((q.1 : ℝ) * q.2 * n))) ≤
      ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ((x : ℝ) ^ (-(0.1 : ℝ)) *
              ∑ n ∈ shiftedSieveMIndices h x q,
                ArithmeticFunction.vonMangoldt n +
            ∑ n ∈ shiftedSmoothingBoundaryIndices h x q,
              ArithmeticFunction.vonMangoldt n) := by
      apply Finset.sum_le_sum
      intro q hq
      have hY : 1 < (x : ℝ) / ((q.1 : ℝ) * q.2) :=
        one_lt_pairQuotient hq
      have hlogY : 0 < Real.log
          ((x : ℝ) / ((q.1 : ℝ) * q.2)) :=
        Real.log_pos hY
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlogY.le)
      rw [Finset.mul_sum]
      rw [show
          (∑ n ∈ shiftedSmoothingBoundaryIndices h x q,
              ArithmeticFunction.vonMangoldt n) =
            ∑ n ∈ shiftedSieveMIndices h x q,
              if (x : ℝ) / ((q.1 : ℝ) * q.2 * n) <
                  Real.exp
                    (2 * (Real.log x) ^ (-(0.1 : ℝ)))
              then ArithmeticFunction.vonMangoldt n
              else 0 by
        unfold shiftedSmoothingBoundaryIndices
        rw [Finset.sum_filter]]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro n hn
      let y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2 * n)
      have hy0 : 0 ≤ y := by
        dsimp only [y]
        positivity
      have hphi0 : 0 ≤ chenPhi x y :=
        chenPhi_nonneg x (by exact_mod_cast hx1) hy0
      by_cases hboundary :
          y < Real.exp
            (2 * (Real.log x) ^ (-(0.1 : ℝ)))
      · rw [if_pos hboundary]
        change ArithmeticFunction.vonMangoldt n *
            (1 - chenPhi x y) ≤
          (x : ℝ) ^ (-(0.1 : ℝ)) *
              ArithmeticFunction.vonMangoldt n +
            ArithmeticFunction.vonMangoldt n
        have hloss : 1 - chenPhi x y ≤ 1 := by linarith
        calc
          ArithmeticFunction.vonMangoldt n *
              (1 - chenPhi x y) ≤
            ArithmeticFunction.vonMangoldt n * 1 :=
              mul_le_mul_of_nonneg_left hloss
                ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ (x : ℝ) ^ (-(0.1 : ℝ)) *
                ArithmeticFunction.vonMangoldt n +
              ArithmeticFunction.vonMangoldt n := by
            have hnonneg :
                0 ≤ (x : ℝ) ^ (-(0.1 : ℝ)) *
                  ArithmeticFunction.vonMangoldt n :=
              mul_nonneg (Real.rpow_nonneg (by positivity) _)
                ArithmeticFunction.vonMangoldt_nonneg
            linarith
      · rw [if_neg hboundary]
        change ArithmeticFunction.vonMangoldt n *
            (1 - chenPhi x y) ≤
          (x : ℝ) ^ (-(0.1 : ℝ)) *
              ArithmeticFunction.vonMangoldt n + 0
        have hylarge :
            Real.exp
                (2 * (Real.log x) ^ (-(0.1 : ℝ))) ≤ y :=
          le_of_not_gt hboundary
        have hphi :=
          chenPhi_ge (x := (x : ℝ)) (y := y)
            (by exact_mod_cast hx1) hxlog hylarge
        have hloss :
            1 - chenPhi x y ≤
              (x : ℝ) ^ (-(0.1 : ℝ)) := by
          linarith
        simpa only [add_zero, mul_comm] using
          mul_le_mul_of_nonneg_left hloss
            ArithmeticFunction.vonMangoldt_nonneg
    _ = (x : ℝ) ^ (-(0.1 : ℝ)) *
          ∑ q ∈ chenPairs x,
            (Real.log
              ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
              ∑ n ∈ shiftedSieveMIndices h x q,
                ArithmeticFunction.vonMangoldt n +
        ∑ q ∈ chenPairs x,
          (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
            ∑ n ∈ shiftedSmoothingBoundaryIndices h x q,
              ArithmeticFunction.vonMangoldt n := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- The crude estimate for `M` is residue-independent: the shifted rough
indices are still a subset of the same unsifted interval. -/
theorem shiftedSieveM_le_crude
    {h x : ℕ} (hx2 : 2 ≤ x)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    shiftedSieveM h x ≤
      ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
        18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
          Real.log x := by
  unfold shiftedSieveM
  have hxpos : (0 : ℝ) < x := (Real.exp_pos 3).trans_le hxlarge
  have hxone : (1 : ℝ) ≤ x := by
    have h : (1 : ℝ) < Real.exp 3 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (h.trans_le hxlarge).le
  have hlogx : (3 : ℝ) ≤ Real.log x := by
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (Real.exp_pos 3))
        (Set.mem_Ioi.mpr hxpos) hxlarge
  have hpair :
      ∀ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n ≤
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x) := by
    intro q hq
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
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
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤
            Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
      rw [hlogpow] at hmono
      nlinarith
    have hinvnonneg : 0 ≤ (Real.log Y)⁻¹ := by positivity
    have hinvle : (Real.log Y)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hlogY
    have hsubset :
        shiftedSieveMIndices h x q ⊆ smoothedMIndices x q := by
      intro n hn
      have hn' := hn
      simp only [shiftedSieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      simp only [smoothedMIndices, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨hn'.1, hn'.2.1⟩
    have hrough :
        ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n ≤
          ∑ n ∈ smoothedMIndices x q,
            ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hmass :
        ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n ≤
          (Y + 2) * Real.log x :=
      hrough.trans (by
        simpa only [Y] using
          sum_smoothedMIndices_vonMangoldt_le hx2 q)
    have hmass0 :
        0 ≤ ∑ n ∈ shiftedSieveMIndices h x q,
          ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_nonneg
      intro n hn
      exact ArithmeticFunction.vonMangoldt_nonneg
    calc
      (Real.log
          ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n =
        (Real.log Y)⁻¹ *
          ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n := by rfl
      _ ≤ 1 * ((Y + 2) * Real.log x) :=
        mul_le_mul hinvle hmass hmass0 (by norm_num)
      _ = ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x := by simp only [Y, one_mul]
  calc
    ∑ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ shiftedSieveMIndices h x q,
            ArithmeticFunction.vonMangoldt n ≤
      ∑ q ∈ chenPairs x,
        (((x : ℝ) / ((q.1 : ℝ) * q.2) + 2) *
          Real.log x) := by
      apply Finset.sum_le_sum
      exact hpair
    _ = (∑ q ∈ chenPairs x,
          ((x : ℝ) / ((q.1 : ℝ) * q.2) + 2)) *
        Real.log x := by rw [Finset.sum_mul]
    _ ≤ ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
          2 * ((chenPairs x).card : ℝ)) *
        Real.log x := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hYsum :
          ∑ q ∈ chenPairs x,
              (x : ℝ) / ((q.1 : ℝ) * q.2) ≤
            (x : ℝ) * (harmonic x : ℝ) ^ 2 := by
        simpa only [sub_zero, zero_div, Real.rpow_one] using
        (sum_pairQuotient_rpow_le_harmonic
          x (ε := 0) (by norm_num))
      calc
        (∑ q ∈ chenPairs x,
            (x : ℝ) / ((q.1 : ℝ) * q.2)) +
              ((chenPairs x).card : ℝ) * 2 =
            2 * ((chenPairs x).card : ℝ) +
              ∑ q ∈ chenPairs x,
                (x : ℝ) / ((q.1 : ℝ) * q.2) := by ring
        _ ≤ 2 * ((chenPairs x).card : ℝ) +
              (x : ℝ) * (harmonic x : ℝ) ^ 2 :=
          add_le_add_right hYsum _
        _ = (x : ℝ) * (harmonic x : ℝ) ^ 2 +
              2 * ((chenPairs x).card : ℝ) := by ring
    _ ≤ ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
          18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
        Real.log x := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard := chenPairs_card_cast_le x
        (show 1 ≤ x by omega)
      have hcard' :
          2 * ((chenPairs x).card : ℝ) ≤
            18 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
        nlinarith
      simpa [add_comm] using
        add_le_add_left hcard'
          ((x : ℝ) * (harmonic x : ℝ) ^ 2)

/-- The small-base part of the shifted transition interval has the same
power-saving majorant as in the original argument. -/
theorem shiftedSmoothingBoundarySmallBaseMass_le_explicit
    {h x : ℕ} (hx2 : 2 ≤ x)
    (hxlarge : Real.exp 3 ≤ (x : ℝ)) :
    shiftedSmoothingBoundarySmallBaseMass h x ≤
      9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
        (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) := by
  unfold shiftedSmoothingBoundarySmallBaseMass
  have hxpos : (0 : ℝ) < x := (Real.exp_pos 3).trans_le hxlarge
  have hxone : (1 : ℝ) ≤ x := by
    have h : (1 : ℝ) < Real.exp 3 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (h.trans_le hxlarge).le
  have hlogx : (3 : ℝ) ≤ Real.log x := by
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (Real.exp_pos 3))
        (Set.mem_Ioi.mpr hxpos) hxlarge
  let B : ℝ :=
    (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
      Real.log x * (harmonic x : ℝ)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hH : 0 ≤ (harmonic x : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      positivity
    exact mul_nonneg
      (mul_nonneg (by positivity) (by linarith)) hH
  have hpair :
      ∀ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter
              (fun n => (n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
    intro q hq
    let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
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
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤
            Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
      rw [hlogpow] at hmono
      nlinarith
    have hinv0 : 0 ≤ (Real.log Y)⁻¹ := by positivity
    have hinvle : (Real.log Y)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hlogY
    let S : Finset ℕ :=
      (shiftedSmoothingBoundaryIndices h x q).filter
        (fun n => (n.minFac : ℝ) ≤
          (x : ℝ) ^ ((1 : ℝ) / 100))
    have hSsubset : S ⊆ smoothedMIndices x q := by
      intro n hn
      have hnBoundary := (Finset.mem_filter.mp hn).1
      have hnSieve := (Finset.mem_filter.mp hnBoundary).1
      have hn' := hnSieve
      simp only [shiftedSieveMIndices, Finset.mem_filter,
        Finset.mem_range] at hn'
      simp only [smoothedMIndices, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨hn'.1, hn'.2.1⟩
    have hsum :
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            ∑ n ∈ smoothedMIndices x q,
              ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹ := by
      calc
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
            ∑ n ∈ S,
              (x : ℝ) ^ ((1 : ℝ) / 100) *
                (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro n hn
          exact vonMangoldt_le_rpow_mul_div_minFac
            (Finset.mem_filter.mp hn).2
        _ ≤ ∑ n ∈ smoothedMIndices x q,
              (x : ℝ) ^ ((1 : ℝ) / 100) *
                (ArithmeticFunction.vonMangoldt n *
                  (n.minFac : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsubset
          intro n hn _
          exact mul_nonneg
            (Real.rpow_nonneg hxpos.le _)
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (inv_nonneg.mpr (by positivity)))
        _ = (x : ℝ) ^ ((1 : ℝ) / 100) *
            ∑ n ∈ smoothedMIndices x q,
              ArithmeticFunction.vonMangoldt n *
                (n.minFac : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    have hsumB :
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B :=
      hsum.trans (mul_le_mul_of_nonneg_left
        (by simpa only [B] using
          (sum_smoothedMIndices_vonMangoldt_div_minFac_le
            hx2 q))
        (Real.rpow_nonneg hxpos.le _))
    have hsum0 :
        0 ≤ ∑ n ∈ S,
          ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_nonneg
      intro n hn
      exact ArithmeticFunction.vonMangoldt_nonneg
    have hmul :
        (Real.log Y)⁻¹ *
            ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
      calc
        (Real.log Y)⁻¹ *
            ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
          1 * ∑ n ∈ S,
            ArithmeticFunction.vonMangoldt n :=
          mul_le_mul_of_nonneg_right hinvle hsum0
        _ ≤ 1 * ((x : ℝ) ^ ((1 : ℝ) / 100) * B) :=
          mul_le_mul_of_nonneg_left hsumB (by norm_num)
        _ = (x : ℝ) ^ ((1 : ℝ) / 100) * B := one_mul _
    simpa only [Y, S] using hmul
  calc
    ∑ q ∈ chenPairs x,
        (Real.log
            ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (shiftedSmoothingBoundaryIndices h x q).filter
              (fun n => (n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
      ∑ q ∈ chenPairs x,
        (x : ℝ) ^ ((1 : ℝ) / 100) * B := by
      apply Finset.sum_le_sum
      exact hpair
    _ = ((chenPairs x).card : ℝ) *
        ((x : ℝ) ^ ((1 : ℝ) / 100) * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
        ((x : ℝ) ^ ((1 : ℝ) / 100) * B) := by
      exact mul_le_mul_of_nonneg_right
        (chenPairs_card_cast_le x (show 1 ≤ x by omega))
        (mul_nonneg (Real.rpow_nonneg hxpos.le _) hB0)
    _ = 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
        (⌈Real.log x / Real.log 2⌉₊ : ℝ) *
          Real.log x * (harmonic x : ℝ) := by
      have hexp :
          (253 : ℝ) / 300 =
            (5 : ℝ) / 6 + (1 : ℝ) / 100 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      dsimp only [B]
      ring

theorem eventually_shiftedSmoothingBoundarySmallBaseMass_le (h : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      shiftedSmoothingBoundarySmallBaseMass h x ≤
        (18 * ((Real.log 2)⁻¹ + 1)) *
          (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
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
  filter_upwards [eventually_log_pow_five_le_rpow, hlogOne,
    hxlargeEventually, eventually_ge_atTop 2,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 10) (r := (2.01 : ℝ))
        (by norm_num)] with
      x hlogFive hlogOne hxlarge hx2 hpower
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
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
  have hlogs :
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ≤
        2 * K * L ^ 5 := by
    calc
      (⌈L / Real.log 2⌉₊ : ℝ) * L * H ≤
          (K * L) * L * (2 * L) := by gcongr
      _ = 2 * K * L ^ 3 := by ring
      _ ≤ 2 * K * L ^ 5 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (show 1 ≤ L by
            simpa only [L] using hlogOne) (by norm_num))
          (mul_nonneg (by norm_num) hK0)
  have hexplicit :=
    shiftedSmoothingBoundarySmallBaseMass_le_explicit
      (h := h) hx2 hxlarge
  calc
    shiftedSmoothingBoundarySmallBaseMass h x ≤
        9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          ((⌈L / Real.log 2⌉₊ : ℝ) * L * H) := by
      simpa only [L, H, mul_assoc] using hexplicit
    _ ≤ 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          (2 * K * L ^ 5) := by
      gcongr
    _ ≤ 9 * (x : ℝ) ^ ((253 : ℝ) / 300) *
          (2 * K * (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      dsimp only [L] at hlogFive ⊢
      gcongr
    _ = (18 * K) * (x : ℝ) ^ ((64 : ℝ) / 75) := by
      have hexp :
          (64 : ℝ) / 75 =
            (253 : ℝ) / 300 + (1 : ℝ) / 100 := by
        norm_num
      rw [hexp, Real.rpow_add hxpos]
      ring
    _ ≤ (18 * K) * (x : ℝ) ^ (1 - (1 : ℝ) / 10) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
      · exact mul_nonneg (by norm_num) hK0
    _ ≤ (18 * K) *
        ((x : ℝ) / (Real.log x) ^ (2.01 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hpower
        (mul_nonneg (by norm_num) hK0)
    _ = (18 * ((Real.log 2)⁻¹ + 1)) *
        (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [K]
      ring

theorem eventually_shiftedSmoothingInterior_le (h : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (-(0.1 : ℝ)) * shiftedSieveM h x ≤
        19 * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
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
  have hδ01 : (0 : ℝ) < 1 / 100 := by norm_num
  have hδ08 : (0 : ℝ) < 8 / 100 := by norm_num
  filter_upwards [eventually_harmonic_sq_le_rpow hδ01,
    eventually_log_pow_four_le_rpow, hlogOne,
    hxlargeEventually, eventually_ge_atTop 2,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (8 : ℝ) / 100) (r := (2.01 : ℝ)) hδ08] with
      x hH hlogFour hlogOne hxlarge hx2 hpower
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := zero_lt_one.trans_le hxone
  have hpow01one :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.one_le_rpow hxone (by norm_num)
  have hlog :
      Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
    calc
      Real.log x ≤ (Real.log x) ^ 4 := by
        nlinarith [sq_nonneg (Real.log x),
          sq_nonneg ((Real.log x) ^ 2 - Real.log x)]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := hlogFour
  have h56 :
      (x : ℝ) ^ ((5 : ℝ) / 6) ≤ (x : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)).trans_eq
      (Real.rpow_one x)
  have hM := shiftedSieveM_le_crude (h := h) hx2 hxlarge
  have hxx :
      (x : ℝ) ≤ (x : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 100) :=
    le_mul_of_one_le_right hxpos.le hpow01one
  have hinside :
      (x : ℝ) * (harmonic x : ℝ) ^ 2 +
          18 * (x : ℝ) ^ ((5 : ℝ) / 6) ≤
        (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 100) +
          18 * ((x : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100)) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hH hxpos.le)
      (mul_le_mul_of_nonneg_left (h56.trans hxx) (by norm_num))
  have hM' :
      shiftedSieveM h x ≤
        19 * (x : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            (x : ℝ) ^ ((1 : ℝ) / 100) := by
    calc
      shiftedSieveM h x ≤
          ((x : ℝ) * (harmonic x : ℝ) ^ 2 +
            18 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x := hM
      _ ≤ ((x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 100) +
            18 * ((x : ℝ) *
              (x : ℝ) ^ ((1 : ℝ) / 100))) *
              (x : ℝ) ^ ((1 : ℝ) / 100) := by
        exact mul_le_mul hinside hlog
          (by linarith) (by positivity)
      _ = 19 * (x : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 100) *
            (x : ℝ) ^ ((1 : ℝ) / 100) := by ring
  calc
    (x : ℝ) ^ (-(0.1 : ℝ)) * shiftedSieveM h x ≤
        (x : ℝ) ^ (-(0.1 : ℝ)) *
          (19 * (x : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100) *
              (x : ℝ) ^ ((1 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hM'
        (Real.rpow_nonneg hxpos.le _)
    _ = 19 * ((x : ℝ) ^ (-(0.1 : ℝ)) *
          (x : ℝ) ^ (1 : ℝ) *
            (x : ℝ) ^ ((1 : ℝ) / 100) *
              (x : ℝ) ^ ((1 : ℝ) / 100)) := by
      rw [Real.rpow_one]
      ring
    _ = 19 * (x : ℝ) ^ ((92 : ℝ) / 100) := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos,
        ← Real.rpow_add hxpos]
      congr 2
      norm_num
    _ ≤ 19 * ((x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [show (92 : ℝ) / 100 =
          1 - (8 : ℝ) / 100 by norm_num] using hpower
    _ = 19 * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by ring

end Chen
