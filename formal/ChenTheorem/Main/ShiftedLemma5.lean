import ChenTheorem.Main.ShiftedSieveLemmas
import ChenTheorem.Lemma5.Core

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

end Chen
