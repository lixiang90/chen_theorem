import ChenTheorem.MainEstimates
import ChenTheorem.Main.ShiftedLemma6Large

open Filter Real
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-! # Fixed-shift analogue of Lemma 7

The fixed shift changes only the Selberg coefficient: the smoothed prime mass
is the same scale-dependent quantity as in the unshifted proof.  This file
first combines shifted Lemmas 5 and 6, then develops the normalization needed
to bound `shiftedMOne`.
-/

/-- Shifted Lemmas 5 and 6 combined: the primitive-character remainder is
absorbed into the `x/(log x)^2.01` error. -/
theorem shiftedSieveOmega_le_mOne
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      Even x →
      (shiftedSieveOmega h x : ℝ) ≤
        shiftedMOne h x ε / (1 - ε) +
          C * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) := by
  obtain ⟨C₅, hC₅, hlemma5⟩ :=
    shiftedSieveOmega_le_mOne_add_mTwo h hh0 hhEven ε hε hε'
  obtain ⟨C₆, hC₆, hlemma6⟩ := shiftedMTwo_le h ε hε hε'
  have hε1 : ε < 1 := hε'.trans (by norm_num)
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  let C : ℝ := C₅ + C₆ / (1 - ε)
  refine ⟨C, by dsimp only [C]; exact add_pos hC₅ (div_pos hC₆ hden), ?_⟩
  filter_upwards [hlemma5, hlemma6] with x h5 h6
  intro hxEven
  have h6' :
      shiftedMTwo h x ε / (1 - ε) ≤
        (C₆ * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ)) /
          (1 - ε) :=
    (div_le_div_iff_of_pos_right hden).2 (h6 hxEven)
  calc
    (shiftedSieveOmega h x : ℝ) ≤
        (shiftedMOne h x ε + shiftedMTwo h x ε) / (1 - ε) +
          C₅ * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) := h5
    _ = shiftedMOne h x ε / (1 - ε) +
          shiftedMTwo h x ε / (1 - ε) +
            C₅ * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) := by ring
    _ ≤ shiftedMOne h x ε / (1 - ε) +
          (C₆ * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ)) /
            (1 - ε) +
              C₅ * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) := by
      gcongr
    _ = shiftedMOne h x ε / (1 - ε) +
          C * (x : ℝ) / Real.log (x : ℝ) ^ (2.01 : ℝ) := by
      dsimp only [C]
      field_simp
      ring

/-- The fixed-shift Selberg coefficient occurring in `shiftedMOne`. -/
noncomputable def shiftedSieveMainCoefficient
    (h x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ shiftedSieveModuli h x ε,
    shiftedSieveLcmCoeff h x ε d / (Nat.totient d : ℝ)

/-- The principal term factors into the fixed-shift Selberg coefficient and
the same smoothed prime mass used in the original Lemma 7. -/
theorem shiftedMOne_eq_sieveMainCoefficient_mul_smoothedPrimeMass
    (h x : ℕ) (ε : ℝ) :
    shiftedMOne h x ε =
      shiftedSieveMainCoefficient h x ε * smoothedPrimeMass x := by
  simp only [shiftedMOne, shiftedSieveMainCoefficient, smoothedPrimeMass,
    Finset.sum_mul]

/-- The shifted normalizing sum contains its `k = 1` term. -/
theorem one_le_shiftedSieveNorm
    {h x : ℕ} {ε : ℝ} (hhEven : Even h) (hx1 : 1 ≤ x)
    (_hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    1 ≤ shiftedSieveNorm h x ε := by
  have hexp : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
  have hmem : 1 ∈ shiftedSieveNormIndices h x ε := by
    simp only [shiftedSieveNormIndices, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by norm_num, ?_, Nat.coprime_one_left h⟩
    simpa using Real.one_le_rpow (by exact_mod_cast hx1) hexp
  rw [shiftedSieveNorm]
  have hnonneg :
      ∀ k ∈ shiftedSieveNormIndices h x ε,
        0 ≤ ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k := by
    intro k hk
    have hk' := hk
    simp only [shiftedSieveNormIndices, Finset.mem_filter,
      Finset.mem_range] at hk'
    have hk2 : k.Coprime 2 :=
      Nat.Coprime.of_dvd_right hhEven.two_dvd hk'.2.2.2
    have hkodd : Odd k := hk2.odd_of_right
    exact div_nonneg (sq_nonneg _)
      (fW_pos_of_odd (by omega) hkodd).le
  have hone :
      ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) ^ 2 / fW 1 = 1 := by
    norm_num [fW]
  calc
    1 = ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) ^ 2 / fW 1 := hone.symm
    _ ≤ ∑ k ∈ shiftedSieveNormIndices h x ε,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k :=
      Finset.single_le_sum hnonneg hmem

@[simp]
theorem shiftedSieveNumerator_one (h x : ℕ) (ε : ℝ) :
    shiftedSieveNumerator h x ε 1 = shiftedSieveNorm h x ε := by
  have hindices :
      shiftedSieveNumeratorIndices h x ε 1 =
        shiftedSieveNormIndices h x ε := by
    ext k
    simp [shiftedSieveNumeratorIndices, shiftedSieveNormIndices]
  rw [shiftedSieveNumerator, shiftedSieveNorm, hindices]

/-- On its support, the separately specified value `λ₁ = 1` agrees with the
uniform fixed-shift Selberg formula. -/
theorem shiftedSieveWeight_eq_uniform
    {h x d : ℕ} {ε : ℝ} (hhEven : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hd : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)) :
    shiftedSieveWeight h x ε d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (Nat.totient d : ℝ) / fW d *
          (shiftedSieveNumerator h x ε d /
            shiftedSieveNorm h x ε) := by
  by_cases hd1 : d = 1
  · subst d
    have hS : shiftedSieveNorm h x ε ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le
        (one_le_shiftedSieveNorm hhEven hx1 hε0 hε))
    simp [shiftedSieveNumerator_one, hS, shiftedSieveWeight]
  · rw [shiftedSieveWeight, if_neg hd1, if_pos hd]

/-- The lcm of two shifted weight-support indices lies in the collected
modulus range. -/
theorem lcm_mem_shiftedSieveModuli_of_mem_shiftedSieveNormIndices
    {h x d₁ d₂ : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hd₁ : d₁ ∈ shiftedSieveNormIndices h x ε)
    (hd₂ : d₂ ∈ shiftedSieveNormIndices h x ε) :
    d₁.lcm d₂ ∈ shiftedSieveModuli h x ε := by
  have h₁ := hd₁
  have h₂ := hd₂
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at h₁ h₂
  let R : ℝ := (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)
  have hxR : (0 : ℝ) < x := by positivity
  have hlcmR : ((d₁.lcm d₂ : ℕ) : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
    calc
      ((d₁.lcm d₂ : ℕ) : ℝ) ≤ (d₁ * d₂ : ℕ) := by
        exact_mod_cast Nat.lcm_le_mul (by omega : 0 < d₁) (by omega : 0 < d₂)
      _ = (d₁ : ℝ) * d₂ := by norm_num
      _ ≤ R * R := mul_le_mul h₁.2.2.1 h₂.2.2.1
        (by positivity) (by positivity)
      _ = (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
        dsimp only [R]
        rw [← Real.rpow_add hxR]
        congr 1
        ring
  have hexp_le : (1 : ℝ) / 2 - ε ≤ 1 := by linarith
  have hpow_le_x : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hx1) hexp_le
  have hlcmx : d₁.lcm d₂ ≤ x := by
    exact_mod_cast hlcmR.trans hpow_le_x
  have hlcmPos : 1 ≤ d₁.lcm d₂ :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.lcm_ne_zero (by omega) (by omega))
  have hlcmCoprime : (d₁.lcm d₂).Coprime h :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul d₁ d₂)
      (h₁.2.2.2.mul_left h₂.2.2.2)
  simp only [shiftedSieveModuli, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hlcmPos, hlcmCoprime, hlcmR⟩

theorem shiftedSieveWeight_eq_zero_of_divisor_not_mem_normIndices
    {h x d q : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (_hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hd : d ∈ shiftedSieveModuli h x ε)
    (hq : q ∈ d.divisors)
    (hqnot : q ∉ shiftedSieveNormIndices h x ε) :
    shiftedSieveWeight h x ε q = 0 := by
  have hd' := hd
  simp only [shiftedSieveModuli, Finset.mem_filter, Finset.mem_range] at hd'
  have hqd : q ∣ d := Nat.dvd_of_mem_divisors hq
  have hqpos : 1 ≤ q := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hq0
      subst q
      have : d = 0 := by simpa using hqd
      omega)
  have hqle : q ≤ x :=
    (Nat.le_of_dvd (by omega) hqd).trans (by omega)
  have hqcoprime : q.Coprime h :=
    Nat.Coprime.of_dvd_left hqd hd'.2.2.1
  have hcut : (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) < q := by
    by_contra hcut
    apply hqnot
    simp only [shiftedSieveNormIndices, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨by omega, hqpos, le_of_not_gt hcut, hqcoprime⟩
  have hq1 : q ≠ 1 := by
    intro hqeq
    subst q
    have hexp : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
    have hone : (1 : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
      simpa using Real.one_le_rpow (by exact_mod_cast hx1) hexp
    linarith
  exact shiftedSieveWeight_eq_zero_of_ne_one_of_cutoff hq1 hcut

/-- A fixed shifted lcm fiber may be restricted to the actual support of the
Selberg weights. -/
theorem shiftedSieveLcmCoeff_eq_sum_normIndices_fiber
    {h x d : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hd : d ∈ shiftedSieveModuli h x ε) :
    shiftedSieveLcmCoeff h x ε d =
      ∑ q ∈ (shiftedSieveNormIndices h x ε ×ˢ
          shiftedSieveNormIndices h x ε).filter
          (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
        shiftedSieveWeight h x ε q.1 *
          shiftedSieveWeight h x ε q.2 := by
  unfold shiftedSieveLcmCoeff
  let A := (d.divisors ×ˢ d.divisors).filter
    (fun q : ℕ × ℕ => q.1.lcm q.2 = d)
  let B := (shiftedSieveNormIndices h x ε ×ˢ
      shiftedSieveNormIndices h x ε).filter
    (fun q : ℕ × ℕ => q.1.lcm q.2 = d)
  have hBA : B ⊆ A := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hprod := Finset.mem_product.mp hq'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hq'.2⟩
    · exact Nat.mem_divisors.mpr
        ⟨hq'.2 ▸ Nat.dvd_lcm_left q.1 q.2, by
          have hd' := hd
          simp only [shiftedSieveModuli, Finset.mem_filter,
            Finset.mem_range] at hd'
          omega⟩
    · exact Nat.mem_divisors.mpr
        ⟨hq'.2 ▸ Nat.dvd_lcm_right q.1 q.2, by
          have hd' := hd
          simp only [shiftedSieveModuli, Finset.mem_filter,
            Finset.mem_range] at hd'
          omega⟩
  change (∑ q ∈ A,
      shiftedSieveWeight h x ε q.1 * shiftedSieveWeight h x ε q.2) =
    ∑ q ∈ B,
      shiftedSieveWeight h x ε q.1 * shiftedSieveWeight h x ε q.2
  symm
  apply Finset.sum_subset hBA
  intro q hqA hqB
  have hqA' := Finset.mem_filter.mp hqA
  have hqdiv := Finset.mem_product.mp hqA'.1
  by_cases hq₁ : q.1 ∈ shiftedSieveNormIndices h x ε
  · have hq₂ : q.2 ∉ shiftedSieveNormIndices h x ε := by
      intro hmem
      apply hqB
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hq₁, hmem⟩, hqA'.2⟩
    rw [shiftedSieveWeight_eq_zero_of_divisor_not_mem_normIndices
      hx1 hε0 hε hd hqdiv.2 hq₂, mul_zero]
  · rw [shiftedSieveWeight_eq_zero_of_divisor_not_mem_normIndices
      hx1 hε0 hε hd hqdiv.1 hq₁, zero_mul]

/-- Uncollecting the shifted lcm fibers gives the quadratic form on the left
of equation (22). -/
theorem shiftedSieveMainCoefficient_eq_double_sum
    {h x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) :
    shiftedSieveMainCoefficient h x ε =
      ∑ q ∈ shiftedSieveNormIndices h x ε ×ˢ
          shiftedSieveNormIndices h x ε,
        shiftedSieveWeight h x ε q.1 * shiftedSieveWeight h x ε q.2 /
          (Nat.totient (q.1.lcm q.2) : ℝ) := by
  let S := shiftedSieveNormIndices h x ε ×ˢ
    shiftedSieveNormIndices h x ε
  let g : ℕ × ℕ → ℕ := fun q => q.1.lcm q.2
  let F : ℕ × ℕ → ℝ := fun q =>
    shiftedSieveWeight h x ε q.1 * shiftedSieveWeight h x ε q.2 /
      (Nat.totient (g q) : ℝ)
  have hmaps : ∀ q ∈ S, g q ∈ shiftedSieveModuli h x ε := by
    intro q hq
    have hq' := Finset.mem_product.mp hq
    exact lcm_mem_shiftedSieveModuli_of_mem_shiftedSieveNormIndices
      hx1 hε0 hq'.1 hq'.2
  rw [shiftedSieveMainCoefficient]
  calc
    (∑ d ∈ shiftedSieveModuli h x ε,
        shiftedSieveLcmCoeff h x ε d / (Nat.totient d : ℝ)) =
      ∑ d ∈ shiftedSieveModuli h x ε,
        ∑ q ∈ S with g q = d,
          shiftedSieveWeight h x ε q.1 * shiftedSieveWeight h x ε q.2 /
            (Nat.totient d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [shiftedSieveLcmCoeff_eq_sum_normIndices_fiber
        hx1 hε0 hε hd, Finset.sum_div]
    _ = ∑ d ∈ shiftedSieveModuli h x ε,
        ∑ q ∈ S with g q = d, F q := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro q hq
      have hgq : g q = d := (Finset.mem_filter.mp hq).2
      simp only [F, hgq]
    _ = ∑ q ∈ S, F q := Finset.sum_fiberwise_of_maps_to hmaps F
    _ = ∑ q ∈ shiftedSieveNormIndices h x ε ×ˢ
          shiftedSieveNormIndices h x ε,
        shiftedSieveWeight h x ε q.1 * shiftedSieveWeight h x ε q.2 /
          (Nat.totient (q.1.lcm q.2) : ℝ) := rfl

theorem mem_shiftedSieveNormIndices_of_dvd
    {h x d k : ℕ} {ε : ℝ}
    (hd : d ∈ shiftedSieveNormIndices h x ε) (hkd : k ∣ d) :
    k ∈ shiftedSieveNormIndices h x ε := by
  have hd' := hd
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hd'
  have hkpos : 1 ≤ k :=
    Nat.one_le_iff_ne_zero.mpr (by
      intro hk0
      subst k
      have : d = 0 := by simpa using hkd
      omega)
  have hkle : k ≤ d := Nat.le_of_dvd (by omega) hkd
  have hkleR : (k : ℝ) ≤ d := by exact_mod_cast hkle
  simp only [shiftedSieveNormIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hkpos, hkleR.trans hd'.2.2.1,
    Nat.Coprime.of_dvd_left hkd hd'.2.2.2⟩

/-- Pointwise divisor expansion of the shifted quadratic kernel. -/
theorem shiftedSieveWeight_mul_div_totient_lcm_eq
    {h x a b : ℕ} {ε : ℝ} (hhEven : Even h)
    (ha : a ∈ shiftedSieveNormIndices h x ε)
    (hb : b ∈ shiftedSieveNormIndices h x ε) :
    shiftedSieveWeight h x ε a * shiftedSieveWeight h x ε b /
        (Nat.totient (a.lcm b) : ℝ) =
      ∑ k ∈ (a.gcd b).divisors,
        fW k *
          (shiftedSieveWeight h x ε a / (Nat.totient a : ℝ)) *
          (shiftedSieveWeight h x ε b / (Nat.totient b : ℝ)) := by
  by_cases hasq : Squarefree a
  swap
  · have ha1 : a ≠ 1 := fun haeq => hasq (haeq ▸ squarefree_one)
    rw [shiftedSieveWeight_eq_zero_of_not_squarefree ha1 hasq]
    simp
  by_cases hbsq : Squarefree b
  swap
  · have hb1 : b ≠ 1 := fun hbeq => hbsq (hbeq ▸ squarefree_one)
    rw [shiftedSieveWeight_eq_zero_of_not_squarefree hb1 hbsq]
    simp
  have ha' := ha
  have hb' := hb
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at ha' hb'
  have haodd : Odd a :=
    (Nat.Coprime.of_dvd_right hhEven.two_dvd ha'.2.2.2).odd_of_right
  have hbodd : Odd b :=
    (Nat.Coprime.of_dvd_right hhEven.two_dvd hb'.2.2.2).odd_of_right
  rw [div_eq_mul_inv, inv_totient_lcm_eq hasq hbsq haodd hbodd]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Diagonal form of the shifted finite quadratic expression in (22). -/
theorem shiftedSieveMainCoefficient_eq_diagonal
    {h x : ℕ} {ε : ℝ} (hhEven : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    shiftedSieveMainCoefficient h x ε =
      ∑ k ∈ shiftedSieveNormIndices h x ε,
        fW k *
          (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
            shiftedSieveWeight h x ε d / (Nat.totient d : ℝ)) ^ 2 := by
  let S := shiftedSieveNormIndices h x ε
  let u : ℕ → ℝ := fun d =>
    shiftedSieveWeight h x ε d / (Nat.totient d : ℝ)
  rw [shiftedSieveMainCoefficient_eq_double_sum hx1 hε0 hε]
  rw [Finset.sum_product]
  have hexpand :
      (∑ a ∈ S, ∑ b ∈ S,
          shiftedSieveWeight h x ε a * shiftedSieveWeight h x ε b /
            (Nat.totient (a.lcm b) : ℝ)) =
        ∑ a ∈ S, ∑ b ∈ S,
          ∑ k ∈ (a.gcd b).divisors,
            fW k *
              (shiftedSieveWeight h x ε a / (Nat.totient a : ℝ)) *
              (shiftedSieveWeight h x ε b / (Nat.totient b : ℝ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact shiftedSieveWeight_mul_div_totient_lcm_eq hhEven ha hb
  rw [hexpand]
  have hdivset : ∀ a ∈ S, ∀ b ∈ S,
      (a.gcd b).divisors = S.filter (fun k => k ∣ a ∧ k ∣ b) := by
    intro a ha b hb
    ext k
    constructor
    · intro hk
      have hkg : k ∣ a.gcd b := Nat.dvd_of_mem_divisors hk
      have hka : k ∣ a := hkg.trans (Nat.gcd_dvd_left a b)
      have hkb : k ∣ b := hkg.trans (Nat.gcd_dvd_right a b)
      exact Finset.mem_filter.mpr
        ⟨mem_shiftedSieveNormIndices_of_dvd ha hka, hka, hkb⟩
    · intro hk
      have hk' := Finset.mem_filter.mp hk
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd hk'.2.1 hk'.2.2, by
          have ha' := ha
          simp only [S, shiftedSieveNormIndices, Finset.mem_filter,
            Finset.mem_range] at ha'
          exact Nat.gcd_ne_zero_left (by omega)⟩
  have hreindex :
      (∑ a ∈ S, ∑ b ∈ S,
          ∑ k ∈ (a.gcd b).divisors, fW k * u a * u b) =
        ∑ a ∈ S, ∑ b ∈ S,
          ∑ k ∈ S.filter (fun k => k ∣ a ∧ k ∣ b),
            fW k * u a * u b := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hdivset a ha b hb]
  rw [hreindex]
  change (∑ a ∈ S, ∑ b ∈ S,
      ∑ k ∈ S.filter (fun k => k ∣ a ∧ k ∣ b),
        fW k * u a * u b) = _
  have hfilter :
      (∑ a ∈ S, ∑ b ∈ S,
          ∑ k ∈ S.filter (fun k => k ∣ a ∧ k ∣ b),
            fW k * u a * u b) =
        ∑ a ∈ S, ∑ b ∈ S, ∑ k ∈ S,
          if k ∣ a ∧ k ∣ b then fW k * u a * u b else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_filter]
  rw [hfilter]
  calc
    (∑ a ∈ S, ∑ b ∈ S, ∑ k ∈ S,
        if k ∣ a ∧ k ∣ b then fW k * u a * u b else 0) =
      ∑ k ∈ S, ∑ a ∈ S, ∑ b ∈ S,
        if k ∣ a ∧ k ∣ b then fW k * u a * u b else 0 := by
      trans ∑ a ∈ S, ∑ k ∈ S, ∑ b ∈ S,
        if k ∣ a ∧ k ∣ b then fW k * u a * u b else 0
      · apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
      · rw [Finset.sum_comm]
    _ = ∑ k ∈ S, fW k * (∑ d ∈ S.filter (k ∣ ·), u d) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [sq, Finset.sum_mul, Finset.mul_sum,
        Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hka : k ∣ a
      · simp only [hka, true_and, if_true]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hkb : k ∣ b
        · simp [hkb]
          ring
        · simp [hkb]
      · simp [hka]
    _ = ∑ k ∈ shiftedSieveNormIndices h x ε,
        fW k *
          (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
            shiftedSieveWeight h x ε d / (Nat.totient d : ℝ)) ^ 2 := rfl

/-- Uniform formula for the transformed shifted weight `λ_d / φ(d)`. -/
theorem shiftedSieveWeight_div_totient_eq
    {h x d : ℕ} {ε : ℝ} (hhEven : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hd : d ∈ shiftedSieveNormIndices h x ε) :
    shiftedSieveWeight h x ε d / (Nat.totient d : ℝ) =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
        (shiftedSieveNumerator h x ε d / shiftedSieveNorm h x ε) := by
  have hd' := hd
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hd'
  have hdodd : Odd d :=
    (Nat.Coprime.of_dvd_right hhEven.two_dvd hd'.2.2.2).odd_of_right
  have hφ : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  rw [shiftedSieveWeight_eq_uniform hhEven hx1 hε0 hε hd'.2.2.1]
  field_simp

theorem mul_mem_shiftedSieveNormIndices_of_mem_numerator
    {h x d n : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hd : d ∈ shiftedSieveNormIndices h x ε)
    (hn : n ∈ shiftedSieveNumeratorIndices h x ε d) :
    d * n ∈ shiftedSieveNormIndices h x ε := by
  have hd' := hd
  have hn' := hn
  simp only [shiftedSieveNormIndices, shiftedSieveNumeratorIndices,
    Finset.mem_filter, Finset.mem_range] at hd' hn'
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hprodR : ((d * n : ℕ) : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rw [Nat.cast_mul, mul_comm]
    exact (le_div_iff₀ hdR).mp hn'.2.2.1
  have hexp : (1 : ℝ) / 4 - ε / 2 ≤ 1 := by linarith
  have hRleX : (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hx1) hexp
  have hprodX : d * n ≤ x := by exact_mod_cast hprodR.trans hRleX
  have hnh : n.Coprime h :=
    Nat.Coprime.of_dvd_right (dvd_mul_right h d) hn'.2.2.2
  simp only [shiftedSieveNormIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.mul_pos hd'.2.1 hn'.2.1, hprodR,
    hd'.2.2.2.mul_left hnh⟩

theorem div_mem_shiftedSieveNumeratorIndices_of_squarefree
    {h x r d : ℕ} {ε : ℝ} (hrsq : Squarefree r)
    (hr : r ∈ shiftedSieveNormIndices h x ε) (hdr : d ∣ r) :
    r / d ∈ shiftedSieveNumeratorIndices h x ε d := by
  have hr' := hr
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hr'
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdr (by omega)
  have hnpos : 0 < r / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdr) hdpos
  have hnle : r / d ≤ r := Nat.div_le_self r d
  have hmul : r / d * d = r := Nat.div_mul_cancel hdr
  have hbound : ((r / d : ℕ) : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) / d := by
    have hdR : (0 : ℝ) < d := by positivity
    apply (le_div_iff₀ hdR).2
    rw [← Nat.cast_mul, hmul]
    exact hr'.2.2.1
  have hdh : d.Coprime h :=
    Nat.Coprime.of_dvd_left hdr hr'.2.2.2
  have hnh : (r / d).Coprime h :=
    Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hdr) hr'.2.2.2
  have hnd : (r / d).Coprime d := by
    have hgd : r.gcd d = d := Nat.gcd_eq_right_iff_dvd.mpr hdr
    simpa [hgd] using
      (Nat.coprime_div_gcd_of_squarefree hrsq hdpos.ne')
  simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨by omega, hnpos, hbound, hnh.mul_right hnd⟩

theorem shiftedSieveNumerator_eq_sum_squarefree
    (h x d : ℕ) (ε : ℝ) :
    shiftedSieveNumerator h x ε d =
      ∑ n ∈ (shiftedSieveNumeratorIndices h x ε d).filter Squarefree,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
  rw [shiftedSieveNumerator]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnfilter
  have hnonsq : ¬Squarefree n := by
    intro hsq
    exact hnfilter (Finset.mem_filter.mpr ⟨hn, hsq⟩)
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnonsq]
  norm_num

theorem sum_shiftedSieveWeightTransform_eq_sum_squarefree
    {h x k : ℕ} {ε : ℝ} :
    (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          shiftedSieveNumerator h x ε d) =
      ∑ d ∈ (shiftedSieveNormIndices h x ε).filter
          (fun d => k ∣ d ∧ Squarefree d),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          shiftedSieveNumerator h x ε d := by
  let A := (shiftedSieveNormIndices h x ε).filter (k ∣ ·)
  let B := (shiftedSieveNormIndices h x ε).filter
    (fun d => k ∣ d ∧ Squarefree d)
  have hBA : B ⊆ A := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hd'.1, hd'.2.1⟩
  change (∑ d ∈ A, _) = ∑ d ∈ B, _
  symm
  apply Finset.sum_subset hBA
  intro d hdA hdB
  have hnot : ¬Squarefree d := by
    intro hsq
    apply hdB
    have hdA' := Finset.mem_filter.mp hdA
    exact Finset.mem_filter.mpr ⟨hdA'.1, hdA'.2, hsq⟩
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
  norm_num

noncomputable def shiftedSieveTransformSource
    (h x k : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  (shiftedSieveNormIndices h x ε ×ˢ Finset.range (x + 1)).filter fun z =>
    k ∣ z.1 ∧ Squarefree z.1 ∧
      z.2 ∈ shiftedSieveNumeratorIndices h x ε z.1 ∧ Squarefree z.2

noncomputable def shiftedSieveTransformTarget
    (h x k : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  (shiftedSieveNormIndices h x ε ×ˢ Finset.range (x + 1)).filter fun z =>
    k ∣ z.1 ∧ Squarefree z.1 ∧ z.2 ∈ z.1.divisors ∧ k ∣ z.2

/-- Reindex the shifted numerator convolution by `r = d n`. -/
theorem sum_shiftedSieveTransformSource_eq_target
    {h x k : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε) :
    (∑ z ∈ shiftedSieveTransformSource h x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 / fW z.2)) =
      ∑ z ∈ shiftedSieveTransformTarget h x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          ((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ) := by
  refine Finset.sum_bij (fun z _ => (z.1 * z.2, z.1)) ?_ ?_ ?_ ?_
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hprod := Finset.mem_product.mp hz'.1
    have hmulS := mul_mem_shiftedSieveNormIndices_of_mem_numerator
      hx1 hε0 hprod.1 hz'.2.2.2.1
    have hnhd : z.2.Coprime (h * z.1) := by
      have hn := hz'.2.2.2.1
      simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
        Finset.mem_range] at hn
      exact hn.2.2.2
    have hcop : z.1.Coprime z.2 :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left z.1 h) hnhd).symm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hmulS, ?_⟩,
      dvd_mul_of_dvd_left hz'.2.1 z.2,
      Nat.squarefree_mul_iff.mpr ⟨hcop, hz'.2.2.1, hz'.2.2.2.2⟩,
      ?_, hz'.2.1⟩
    · have hzS := hprod.1
      simp only [shiftedSieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hzS
      exact Finset.mem_range.mpr (by omega)
    · exact Nat.mem_divisors.mpr
        ⟨dvd_mul_right z.1 z.2,
          Nat.mul_ne_zero hz'.2.2.1.ne_zero hz'.2.2.2.2.ne_zero⟩
  · intro a ha b hb hab
    have hfirst : a.1 = b.1 := congrArg Prod.snd hab
    apply Prod.ext
    · exact hfirst
    · have ha' := Finset.mem_filter.mp ha
      have hapos : 0 < a.1 := ha'.2.2.1.ne_zero.bot_lt
      exact Nat.eq_of_mul_eq_mul_left hapos
        (by simpa [hfirst] using congrArg Prod.fst hab)
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyprod := Finset.mem_product.mp hy'.1
    have hydvd : y.2 ∣ y.1 := Nat.dvd_of_mem_divisors hy'.2.2.2.1
    let z : ℕ × ℕ := (y.2, y.1 / y.2)
    refine ⟨z, ?_, ?_⟩
    · have hdS := mem_shiftedSieveNormIndices_of_dvd hyprod.1 hydvd
      have hnN := div_mem_shiftedSieveNumeratorIndices_of_squarefree
        hy'.2.2.1 hyprod.1 hydvd
      have hnrange : y.1 / y.2 < x + 1 := by
        have hyS := hyprod.1
        simp only [shiftedSieveNormIndices, Finset.mem_filter,
          Finset.mem_range] at hyS
        exact (Nat.div_le_self y.1 y.2).trans_lt hyS.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
          ⟨hdS, Finset.mem_range.mpr hnrange⟩,
        hy'.2.2.2.2,
        hy'.2.2.1.squarefree_of_dvd hydvd,
        hnN,
        hy'.2.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hydvd)⟩
    · dsimp only [z]
      apply Prod.ext
      · exact Nat.mul_div_cancel' hydvd
      · rfl
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hn := hz'.2.2.2.1
    simp only [shiftedSieveNumeratorIndices, Finset.mem_filter,
      Finset.mem_range] at hn
    have hcop : z.1.Coprime z.2 :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left z.1 h) hn.2.2.2).symm
    have hd0 : z.1 ≠ 0 := hz'.2.2.1.ne_zero
    have hn0 : z.2 ≠ 0 := hz'.2.2.2.2.ne_zero
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        hcop.gcd_eq_one,
      fW_mul_of_coprime hd0 hn0 hcop,
      Nat.mul_div_cancel_left z.2 (by omega : 0 < z.1)]
    push_cast
    ring

theorem sum_shiftedSieveWeightTransform_eq_source
    {h x k : ℕ} {ε : ℝ} :
    (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          shiftedSieveNumerator h x ε d) =
      ∑ z ∈ shiftedSieveTransformSource h x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 / fW z.2) := by
  rw [sum_shiftedSieveWeightTransform_eq_sum_squarefree]
  unfold shiftedSieveTransformSource
  simp only [Finset.sum_filter, Finset.sum_product]
  simp_rw [shiftedSieveNumerator_eq_sum_squarefree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hkd : k ∣ d
  swap
  · simp [hkd]
  by_cases hdsq : Squarefree d
  swap
  · simp [hkd, hdsq]
  simp only [hkd, hdsq, and_self, true_and, if_true]
  rw [shiftedSieveNumeratorIndices, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  by_cases hnmem :
      1 ≤ n ∧
        (n : ℝ) ≤ (x : ℝ) ^ ((4 : ℝ)⁻¹ - ε / 2) / d ∧
        n.Coprime (h * d)
  swap
  · simp [hnmem, hnle]
  by_cases hnsq : Squarefree n <;> simp [hnmem, hnsq, hnle]

theorem sum_shiftedSieveTransformTarget_eq_nested
    {h x k : ℕ} {ε : ℝ} :
    (∑ z ∈ shiftedSieveTransformTarget h x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          ((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ)) =
      ∑ r ∈ (shiftedSieveNormIndices h x ε).filter
          (fun r => k ∣ r ∧ Squarefree r),
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
          ∑ d ∈ r.divisors.filter (k ∣ ·),
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) := by
  rw [shiftedSieveTransformTarget, Finset.sum_filter, Finset.sum_product,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hkr : k ∣ r
  swap
  · simp [hkr]
  by_cases hrsq : Squarefree r
  swap
  · simp [hkr, hrsq]
  simp only [hkr, hrsq, and_self, true_and, if_true]
  rw [Finset.mul_sum, Finset.sum_filter]
  let D := r.divisors.filter (k ∣ ·)
  have hD : D ⊆ Finset.range (x + 1) := by
    intro d hd
    have hdr : d ∣ r :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hr' := hr
    simp only [shiftedSieveNormIndices, Finset.mem_filter,
      Finset.mem_range] at hr'
    exact Finset.mem_range.mpr
      ((Nat.le_of_dvd (by omega) hdr).trans_lt (by omega))
  change (∑ d ∈ Finset.range (x + 1),
      if d ∈ r.divisors ∧ k ∣ d then
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
          ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)
      else 0) =
    ∑ d ∈ r.divisors,
      if k ∣ d then
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
          ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)
      else 0
  calc
    _ = ∑ d ∈ D,
        (if d ∈ r.divisors ∧ k ∣ d then
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)
        else 0) := by
      symm
      apply Finset.sum_subset hD
      intro d hdR hdD
      by_cases hddiv : d ∈ r.divisors
      · have hnotk : ¬k ∣ d := by
          intro hkd
          exact hdD (Finset.mem_filter.mpr ⟨hddiv, hkd⟩)
        simp [hnotk]
      · simp [hddiv]
    _ = ∑ d ∈ D,
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
          ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      simp [hd'.1, hd'.2]
    _ = _ := by rw [Finset.sum_filter]

theorem sum_shiftedSieveTransformTarget_eq_moebius_div
    {h x k : ℕ} {ε : ℝ}
    (hk : k ∈ shiftedSieveNormIndices h x ε) :
    (∑ z ∈ shiftedSieveTransformTarget h x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          ((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ)) =
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) / fW k := by
  rw [sum_shiftedSieveTransformTarget_eq_nested]
  have hk' := hk
  simp only [shiftedSieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hk'
  by_cases hksq : Squarefree k
  · have hinner : ∀ r ∈ (shiftedSieveNormIndices h x ε).filter
        (fun r => k ∣ r ∧ Squarefree r),
        (∑ d ∈ r.divisors.filter (k ∣ ·),
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)) =
          if r = k then 1 else 0 := by
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      exact_mod_cast sum_moebius_divisors_multiples (by omega) hr'.2.1
    have hrewrite :
        (∑ r ∈ (shiftedSieveNormIndices h x ε).filter
            (fun r => k ∣ r ∧ Squarefree r),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
            ∑ d ∈ r.divisors.filter (k ∣ ·),
              ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)) =
        ∑ r ∈ (shiftedSieveNormIndices h x ε).filter
            (fun r => k ∣ r ∧ Squarefree r),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
            (if r = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hinner r hr]
    rw [hrewrite]
    let T := (shiftedSieveNormIndices h x ε).filter
      (fun r => k ∣ r ∧ Squarefree r)
    have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hk, dvd_rfl, hksq⟩
    change (∑ r ∈ T,
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
          (if r = k then 1 else 0)) = _
    calc
      _ = ((ArithmeticFunction.moebius k : ℤ) : ℝ) / fW k *
          (if k = k then 1 else 0) := by
        apply Finset.sum_eq_single k
        · intro r hr hrk
          simp [if_neg hrk]
        · intro hknot
          exact (hknot hkT).elim
      _ = _ := by simp
  · have hT : (shiftedSieveNormIndices h x ε).filter
        (fun r => k ∣ r ∧ Squarefree r) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r hr hpred
      exact hksq (hpred.2.squarefree_of_dvd hpred.1)
    rw [hT]
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hksq]

theorem sum_shiftedSieveNumeratorTransform
    {h x k : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hk : k ∈ shiftedSieveNormIndices h x ε) :
    (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          shiftedSieveNumerator h x ε d) =
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) / fW k := by
  rw [sum_shiftedSieveWeightTransform_eq_source,
    sum_shiftedSieveTransformSource_eq_target hx1 hε0,
    sum_shiftedSieveTransformTarget_eq_moebius_div hk]

/-- Möbius transform immediately preceding shifted equation (22). -/
theorem sum_shiftedSieveWeight_div_totient
    {h x k : ℕ} {ε : ℝ} (hhEven : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hk : k ∈ shiftedSieveNormIndices h x ε) :
    (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
        shiftedSieveWeight h x ε d / (Nat.totient d : ℝ)) =
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) /
        (shiftedSieveNorm h x ε * fW k) := by
  calc
    (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
        shiftedSieveWeight h x ε d / (Nat.totient d : ℝ)) =
      ∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          shiftedSieveNumerator h x ε d / shiftedSieveNorm h x ε := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [shiftedSieveWeight_div_totient_eq hhEven hx1 hε0 hε
        (Finset.mem_filter.mp hd).1]
      ring
    _ = ((ArithmeticFunction.moebius k : ℤ) : ℝ) /
        (shiftedSieveNorm h x ε * fW k) := by
      rw [← Finset.sum_div,
        sum_shiftedSieveNumeratorTransform hx1 hε0 hk]
      ring

/-- Shifted equation (22): the quadratic Selberg coefficient is exactly the
reciprocal of its fixed-shift normalizing sum. -/
theorem shiftedSieveMainCoefficient_eq_inv_shiftedSieveNorm
    {h x : ℕ} {ε : ℝ} (hhEven : Even h) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    shiftedSieveMainCoefficient h x ε =
      (shiftedSieveNorm h x ε)⁻¹ := by
  rw [shiftedSieveMainCoefficient_eq_diagonal hhEven hx1 hε0 hε]
  have hrewrite :
      (∑ k ∈ shiftedSieveNormIndices h x ε,
          fW k *
            (∑ d ∈ (shiftedSieveNormIndices h x ε).filter (k ∣ ·),
              shiftedSieveWeight h x ε d / (Nat.totient d : ℝ)) ^ 2) =
        ∑ k ∈ shiftedSieveNormIndices h x ε,
          fW k *
            (((ArithmeticFunction.moebius k : ℤ) : ℝ) /
              (shiftedSieveNorm h x ε * fW k)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [sum_shiftedSieveWeight_div_totient hhEven hx1 hε0 hε hk]
  rw [hrewrite]
  have hS : shiftedSieveNorm h x ε ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le
      (one_le_shiftedSieveNorm hhEven hx1 hε0 hε))
  calc
    (∑ k ∈ shiftedSieveNormIndices h x ε,
        fW k *
          (((ArithmeticFunction.moebius k : ℤ) : ℝ) /
            (shiftedSieveNorm h x ε * fW k)) ^ 2) =
      shiftedSieveNorm h x ε ^ (-2 : ℤ) *
        ∑ k ∈ shiftedSieveNormIndices h x ε,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := hk
      simp only [shiftedSieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hk'
      have hkodd : Odd k :=
        (Nat.Coprime.of_dvd_right hhEven.two_dvd hk'.2.2.2).odd_of_right
      have hfk : fW k ≠ 0 := (fW_pos_of_odd (by omega) hkodd).ne'
      field_simp [hS, hfk]
    _ = shiftedSieveNorm h x ε ^ (-2 : ℤ) *
        shiftedSieveNorm h x ε := by rfl
    _ = (shiftedSieveNorm h x ε)⁻¹ := by field_simp [hS]

end Chen
