import ChenTheorem.Lemma6.Core

open Filter Real
open scoped Classical

namespace Chen

/-!
# Lemma 7: finite reduction

This file separates the two factors in the main term `M₁`.  Equation (22)
of the paper evaluates `sieveMainCoefficient`; the last sentence of the proof
of Lemma 7 bounds `smoothedPrimeMass`.
-/

/-- The quadratic Selberg coefficient on the left-hand side of equation (22). -/
noncomputable def sieveMainCoefficient (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    sieveLcmCoeff x ε d / (Nat.totient d : ℝ)

/-- The smoothed von Mangoldt mass common to every modulus in `M₁`. -/
noncomputable def smoothedPrimeMass (x : ℕ) : ℝ :=
  ∑ q ∈ chenPairs x,
    ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n

/-- The definition of `M₁` factors into its Selberg coefficient and its
smoothed prime mass. -/
theorem mOne_eq_sieveMainCoefficient_mul_smoothedPrimeMass
    (x : ℕ) (ε : ℝ) :
    mOne x ε = sieveMainCoefficient x ε * smoothedPrimeMass x := by
  simp only [mOne, sieveMainCoefficient, smoothedPrimeMass,
    Finset.sum_mul]

/-- The normalizing sum contains its `k = 1` term.  This elementary
positivity fact is needed before equation (22) can divide by `S`. -/
theorem one_le_sieveNorm
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    1 ≤ sieveNorm x ε := by
  have hexp : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
  have hmem : 1 ∈ sieveNormIndices x ε := by
    simp only [sieveNormIndices, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by norm_num, ?_, Nat.coprime_one_left x⟩
    simpa using Real.one_le_rpow (by exact_mod_cast hx1) hexp
  rw [sieveNorm]
  have hnonneg :
      ∀ k ∈ sieveNormIndices x ε,
        0 ≤ ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k := by
    intro k hk
    have hk' := hk
    simp only [sieveNormIndices, Finset.mem_filter,
      Finset.mem_range] at hk'
    have hk2 : k.Coprime 2 :=
      Nat.Coprime.of_dvd_right hx.two_dvd hk'.2.2.2
    have hkodd : Odd k := hk2.odd_of_right
    exact div_nonneg (sq_nonneg _)
      (fW_pos_of_odd (by omega) hkodd).le
  calc
    1 = ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) ^ 2 / fW 1 := by simp
    _ ≤ ∑ k ∈ sieveNormIndices x ε,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k := by
      exact Finset.single_le_sum (fun k hk => hnonneg k hk) hmem

@[simp]
theorem sieveNumerator_one (x : ℕ) (ε : ℝ) :
    sieveNumerator x ε 1 = sieveNorm x ε := by
  have hindices :
      sieveNumeratorIndices x ε 1 = sieveNormIndices x ε := by
    ext k
    simp [sieveNumeratorIndices, sieveNormIndices]
  rw [sieveNumerator, sieveNorm, hindices]

/-- On its support, Chen's separately specified value `λ₁ = 1` agrees
with the uniform Selberg-weight formula used in the proof of (22). -/
theorem sieveWeight_eq_uniform
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hd : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2)) :
    sieveWeight x ε d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (Nat.totient d : ℝ) / fW d *
          (sieveNumerator x ε d / sieveNorm x ε) := by
  by_cases hd1 : d = 1
  · subst d
    have hS : sieveNorm x ε ≠ 0 :=
      ne_of_gt ((show (0 : ℝ) < 1 from zero_lt_one).trans_le
        (one_le_sieveNorm hx hx1 hε0 hε))
    simp [sieveNumerator_one, hS]
  · rw [sieveWeight, if_neg hd1, if_pos hd]

/-- The lcm of two weight-support indices lies in the collected modulus
range.  This is the range calculation behind the passage to equation (22). -/
theorem lcm_mem_sieveModuli_of_mem_sieveNormIndices
    {x d₁ d₂ : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hd₁ : d₁ ∈ sieveNormIndices x ε)
    (hd₂ : d₂ ∈ sieveNormIndices x ε) :
    d₁.lcm d₂ ∈ sieveModuli x ε := by
  have h₁ := hd₁
  have h₂ := hd₂
  simp only [sieveNormIndices, Finset.mem_filter,
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
  have hpow_le_x :
      (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hx1) hexp_le
  have hlcmx : d₁.lcm d₂ ≤ x := by
    exact_mod_cast hlcmR.trans hpow_le_x
  have hlcmPos : 1 ≤ d₁.lcm d₂ := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.lcm_ne_zero (by omega) (by omega))
  have hlcmCoprime : (d₁.lcm d₂).Coprime x :=
    Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul d₁ d₂)
      (h₁.2.2.2.mul_left h₂.2.2.2)
  simp only [sieveModuli, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hlcmPos, hlcmCoprime, hlcmR⟩

theorem sieveWeight_eq_zero_of_divisor_not_mem_sieveNormIndices
    {x d q : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hd : d ∈ sieveModuli x ε)
    (hq : q ∈ d.divisors) (hqnot : q ∉ sieveNormIndices x ε) :
    sieveWeight x ε q = 0 := by
  have hd' := hd
  simp only [sieveModuli, Finset.mem_filter, Finset.mem_range] at hd'
  have hqd : q ∣ d := Nat.dvd_of_mem_divisors hq
  have hqpos : 1 ≤ q := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hq0
      subst q
      have : d = 0 := by simpa using hqd
      omega)
  have hqle : q ≤ x :=
    (Nat.le_of_dvd (by omega) hqd).trans (by omega)
  have hqcoprime : q.Coprime x :=
    Nat.Coprime.of_dvd_left hqd hd'.2.2.1
  have hcut :
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) < q := by
    by_contra h
    apply hqnot
    simp only [sieveNormIndices, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hqpos, le_of_not_gt h, hqcoprime⟩
  have hq1 : q ≠ 1 := by
    intro hqeq
    subst q
    have hexp : 0 ≤ (1 : ℝ) / 4 - ε / 2 := by linarith
    have hone :
        (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
      simpa using Real.one_le_rpow (by exact_mod_cast hx1) hexp
    linarith
  exact sieveWeight_eq_zero_of_ne_one_of_cutoff hq1 hcut

/-- For a fixed collected modulus, the divisor-pair definition of
`sieveLcmCoeff` may be restricted to the actual support of the weights. -/
theorem sieveLcmCoeff_eq_sum_sieveNormIndices_fiber
    {x d : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hd : d ∈ sieveModuli x ε) :
    sieveLcmCoeff x ε d =
      ∑ q ∈ (sieveNormIndices x ε ×ˢ sieveNormIndices x ε).filter
          (fun q : ℕ × ℕ => q.1.lcm q.2 = d),
        sieveWeight x ε q.1 * sieveWeight x ε q.2 := by
  unfold sieveLcmCoeff
  let A := (d.divisors ×ˢ d.divisors).filter
    (fun q : ℕ × ℕ => q.1.lcm q.2 = d)
  let B := (sieveNormIndices x ε ×ˢ sieveNormIndices x ε).filter
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
          simp only [sieveModuli, Finset.mem_filter,
            Finset.mem_range] at hd'
          omega⟩
    · exact Nat.mem_divisors.mpr
        ⟨hq'.2 ▸ Nat.dvd_lcm_right q.1 q.2, by
          have hd' := hd
          simp only [sieveModuli, Finset.mem_filter,
            Finset.mem_range] at hd'
          omega⟩
  change (∑ q ∈ A, sieveWeight x ε q.1 * sieveWeight x ε q.2) =
    ∑ q ∈ B, sieveWeight x ε q.1 * sieveWeight x ε q.2
  symm
  apply Finset.sum_subset hBA
  intro q hqA hqB
  have hqA' := Finset.mem_filter.mp hqA
  have hqdiv := Finset.mem_product.mp hqA'.1
  by_cases hq₁ : q.1 ∈ sieveNormIndices x ε
  · have hq₂ : q.2 ∉ sieveNormIndices x ε := by
      intro hmem
      apply hqB
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hq₁, hmem⟩, hqA'.2⟩
    rw [sieveWeight_eq_zero_of_divisor_not_mem_sieveNormIndices
      hx1 hε0 hε hd hqdiv.2 hq₂, mul_zero]
  · rw [sieveWeight_eq_zero_of_divisor_not_mem_sieveNormIndices
      hx1 hε0 hε hd hqdiv.1 hq₁, zero_mul]

/-- Uncollecting the lcm fibers turns the coefficient in `M₁` into the
quadratic form appearing on the left of equation (22). -/
theorem sieveMainCoefficient_eq_double_sum
    {x : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) :
    sieveMainCoefficient x ε =
      ∑ q ∈ sieveNormIndices x ε ×ˢ sieveNormIndices x ε,
        sieveWeight x ε q.1 * sieveWeight x ε q.2 /
          (Nat.totient (q.1.lcm q.2) : ℝ) := by
  let S := sieveNormIndices x ε ×ˢ sieveNormIndices x ε
  let g : ℕ × ℕ → ℕ := fun q => q.1.lcm q.2
  let F : ℕ × ℕ → ℝ := fun q =>
    sieveWeight x ε q.1 * sieveWeight x ε q.2 /
      (Nat.totient (g q) : ℝ)
  have hmaps : ∀ q ∈ S, g q ∈ sieveModuli x ε := by
    intro q hq
    have hq' := Finset.mem_product.mp hq
    exact lcm_mem_sieveModuli_of_mem_sieveNormIndices
      hx1 hε0 hq'.1 hq'.2
  rw [sieveMainCoefficient]
  calc
    (∑ d ∈ sieveModuli x ε,
        sieveLcmCoeff x ε d / (Nat.totient d : ℝ)) =
      ∑ d ∈ sieveModuli x ε,
        ∑ q ∈ S with g q = d,
          sieveWeight x ε q.1 * sieveWeight x ε q.2 /
            (Nat.totient d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [sieveLcmCoeff_eq_sum_sieveNormIndices_fiber
        hx1 hε0 hε hd, Finset.sum_div]
    _ = ∑ d ∈ sieveModuli x ε,
        ∑ q ∈ S with g q = d, F q := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro q hq
      have hgq : g q = d := (Finset.mem_filter.mp hq).2
      simp only [F, hgq]
    _ = ∑ q ∈ S, F q :=
      Finset.sum_fiberwise_of_maps_to hmaps F
    _ = ∑ q ∈ sieveNormIndices x ε ×ˢ sieveNormIndices x ε,
        sieveWeight x ε q.1 * sieveWeight x ε q.2 /
          (Nat.totient (q.1.lcm q.2) : ℝ) := rfl

/-- The local identity `1 + (p - 2) = p - 1`, multiplied over the
prime divisors of a squarefree odd number. -/
theorem sum_divisors_fW_eq_totient
    {d : ℕ} (hd : Squarefree d) (hodd : Odd d) :
    ∑ t ∈ d.divisors, fW t = (Nat.totient d : ℝ) := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hd,
    Nat.sum_divisors_filter_squarefree hd.ne_zero]
  simp only [Nat.factors_eq]
  simp_rw [Finset.prod_val]
  have hterm :
      ∀ u ∈ d.primeFactors.powerset,
        fW (∏ p ∈ u, p) = ∏ p ∈ u, ((p : ℝ) - 2) := by
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
      Nat.primeFactors_prod huprime]
  calc
    (∑ u ∈ d.primeFactorsList.toFinset.powerset,
        fW (∏ p ∈ u, p)) =
      ∑ u ∈ d.primeFactors.powerset,
        ∏ p ∈ u, ((p : ℝ) - 2) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ∏ p ∈ d.primeFactors, (1 + ((p : ℝ) - 2)) := by
      rw [Finset.prod_one_add]
    _ = (Nat.totient d : ℝ) := by
      rw [totient_cast_eq_prod_sub_one_of_squarefree hd]
      apply Finset.prod_congr rfl
      intro p hp
      ring

theorem totient_gcd_mul_totient_lcm_of_squarefree
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    (Nat.totient (a.gcd b) : ℝ) * Nat.totient (a.lcm b) =
      (Nat.totient a : ℝ) * Nat.totient b := by
  have hab0 : a.lcm b ≠ 0 := Nat.lcm_ne_zero ha.ne_zero hb.ne_zero
  have hg : Squarefree (a.gcd b) := ha.gcd_left b
  have hl : Squarefree (a.lcm b) := by
    rw [Nat.squarefree_iff_factorization_le_one hab0]
    intro p
    rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
    exact max_le (ha.natFactorization_le_one p)
      (hb.natFactorization_le_one p)
  have hpf : (a.lcm b).primeFactors = (a * b).primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpl, -⟩
      exact ⟨hp, hpl.trans (Nat.lcm_dvd_mul a b),
        Nat.mul_ne_zero ha.ne_zero hb.ne_zero⟩
    · rintro ⟨hp, hpab, -⟩
      have hp' : Nat.Prime p := hp
      exact ⟨hp, (hp'.dvd_mul.mp hpab).elim
        (fun hpa => hpa.trans (Nat.dvd_lcm_left a b))
        (fun hpb => hpb.trans (Nat.dvd_lcm_right a b)), hab0⟩
  rw [totient_cast_eq_prod_sub_one_of_squarefree hg,
    totient_cast_eq_prod_sub_one_of_squarefree hl,
    totient_cast_eq_prod_sub_one_of_squarefree ha,
    totient_cast_eq_prod_sub_one_of_squarefree hb, hpf,
    Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul]

/-- The divisor expansion of the lcm kernel used to diagonalize (22). -/
theorem inv_totient_lcm_eq
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (haodd : Odd a) (hbodd : Odd b) :
    ((Nat.totient (a.lcm b) : ℝ))⁻¹ =
      ((Nat.totient a : ℝ))⁻¹ *
        ((Nat.totient b : ℝ))⁻¹ *
          ∑ k ∈ (a.gcd b).divisors, fW k := by
  have hgodd : Odd (a.gcd b) :=
    haodd.of_dvd_nat (Nat.gcd_dvd_left a b)
  have hsum :
      ∑ k ∈ (a.gcd b).divisors, fW k =
        (Nat.totient (a.gcd b) : ℝ) :=
    sum_divisors_fW_eq_totient (ha.gcd_left b) hgodd
  rw [hsum]
  have haφ : (Nat.totient a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha.ne_zero)).ne'
  have hbφ : (Nat.totient b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb.ne_zero)).ne'
  have hlφ : (Nat.totient (a.lcm b) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero))).ne'
  rw [inv_eq_one_div, inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith [totient_gcd_mul_totient_lcm_of_squarefree ha hb]

theorem mem_sieveNormIndices_of_dvd
    {x d k : ℕ} {ε : ℝ} (hd : d ∈ sieveNormIndices x ε)
    (hkd : k ∣ d) : k ∈ sieveNormIndices x ε := by
  have hd' := hd
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hd'
  have hkpos : 1 ≤ k :=
    Nat.one_le_iff_ne_zero.mpr (by
      intro hk0
      subst k
      have : d = 0 := by simpa using hkd
      omega)
  have hkle : k ≤ d := Nat.le_of_dvd (by omega) hkd
  have hkleR : (k : ℝ) ≤ d := by exact_mod_cast hkle
  simp only [sieveNormIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hkpos, hkleR.trans hd'.2.2.1,
    Nat.Coprime.of_dvd_left hkd hd'.2.2.2⟩

/-- Pointwise divisor expansion of the quadratic kernel.  Nonsquarefree
indices disappear because Chen's weights vanish there. -/
theorem sieveWeight_mul_div_totient_lcm_eq
    {x a b : ℕ} {ε : ℝ} (hx : Even x)
    (ha : a ∈ sieveNormIndices x ε)
    (hb : b ∈ sieveNormIndices x ε) :
    sieveWeight x ε a * sieveWeight x ε b /
        (Nat.totient (a.lcm b) : ℝ) =
      ∑ k ∈ (a.gcd b).divisors,
        fW k *
          (sieveWeight x ε a / (Nat.totient a : ℝ)) *
          (sieveWeight x ε b / (Nat.totient b : ℝ)) := by
  by_cases hasq : Squarefree a
  swap
  · have ha1 : a ≠ 1 := fun h => hasq (h ▸ squarefree_one)
    rw [sieveWeight_eq_zero_of_not_squarefree ha1 hasq]
    simp
  by_cases hbsq : Squarefree b
  swap
  · have hb1 : b ≠ 1 := fun h => hbsq (h ▸ squarefree_one)
    rw [sieveWeight_eq_zero_of_not_squarefree hb1 hbsq]
    simp
  have ha' := ha
  have hb' := hb
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at ha' hb'
  have haodd : Odd a :=
    (Nat.Coprime.of_dvd_right hx.two_dvd ha'.2.2.2).odd_of_right
  have hbodd : Odd b :=
    (Nat.Coprime.of_dvd_right hx.two_dvd hb'.2.2.2).odd_of_right
  rw [div_eq_mul_inv, inv_totient_lcm_eq hasq hbsq haodd hbodd]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Diagonal form of the finite quadratic expression in (22). -/
theorem sieveMainCoefficient_eq_diagonal
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    sieveMainCoefficient x ε =
      ∑ k ∈ sieveNormIndices x ε,
        fW k *
          (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
            sieveWeight x ε d / (Nat.totient d : ℝ)) ^ 2 := by
  let S := sieveNormIndices x ε
  let u : ℕ → ℝ := fun d =>
    sieveWeight x ε d / (Nat.totient d : ℝ)
  rw [sieveMainCoefficient_eq_double_sum hx1 hε0 hε]
  rw [Finset.sum_product]
  have hexpand :
      (∑ a ∈ S, ∑ b ∈ S,
          sieveWeight x ε a * sieveWeight x ε b /
            (Nat.totient (a.lcm b) : ℝ)) =
        ∑ a ∈ S, ∑ b ∈ S,
          ∑ k ∈ (a.gcd b).divisors,
            fW k *
              (sieveWeight x ε a / (Nat.totient a : ℝ)) *
              (sieveWeight x ε b / (Nat.totient b : ℝ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact sieveWeight_mul_div_totient_lcm_eq hx ha hb
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
        ⟨mem_sieveNormIndices_of_dvd ha hka, hka, hkb⟩
    · intro hk
      have hk' := Finset.mem_filter.mp hk
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd hk'.2.1 hk'.2.2, by
          have ha' := ha
          simp only [S, sieveNormIndices, Finset.mem_filter,
            Finset.mem_range] at ha'
          exact Nat.gcd_ne_zero_left (by omega)⟩
  have hreindex :
      (∑ a ∈ S, ∑ b ∈ S,
          ∑ k ∈ (a.gcd b).divisors,
            fW k * u a * u b) =
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
    _ = ∑ k ∈ S,
        fW k * (∑ d ∈ S.filter (k ∣ ·), u d) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [sq, Finset.sum_mul]
      rw [Finset.mul_sum]
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hka : k ∣ a
      · simp only [hka, true_and, if_true]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hkb : k ∣ b <;> simp [hkb] <;> ring
      · simp [hka]
    _ = ∑ k ∈ sieveNormIndices x ε,
        fW k *
          (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
            sieveWeight x ε d / (Nat.totient d : ℝ)) ^ 2 := rfl

/-- Uniform formula for the transformed weight `λ_d / φ(d)` on the
finite support. -/
theorem sieveWeight_div_totient_eq
    {x d : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hd : d ∈ sieveNormIndices x ε) :
    sieveWeight x ε d / (Nat.totient d : ℝ) =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
        (sieveNumerator x ε d / sieveNorm x ε) := by
  have hd' := hd
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hd'
  have hdodd : Odd d :=
    (Nat.Coprime.of_dvd_right hx.two_dvd hd'.2.2.2).odd_of_right
  have hφ : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  rw [sieveWeight_eq_uniform hx hx1 hε0 hε hd'.2.2.1]
  field_simp

theorem mul_mem_sieveNormIndices_of_mem_numerator
    {x d n : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hd : d ∈ sieveNormIndices x ε)
    (hn : n ∈ sieveNumeratorIndices x ε d) :
    d * n ∈ sieveNormIndices x ε := by
  have hd' := hd
  have hn' := hn
  simp only [sieveNormIndices, sieveNumeratorIndices,
    Finset.mem_filter, Finset.mem_range] at hd' hn'
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by omega)
  have hprodR : ((d * n : ℕ) : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) := by
    rw [Nat.cast_mul, mul_comm]
    exact (le_div_iff₀ hdR).mp hn'.2.2.1
  have hexp : (1 : ℝ) / 4 - ε / 2 ≤ 1 := by linarith
  have hRleX :
      (x : ℝ) ^ ((1 : ℝ) / 4 - ε / 2) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hx1) hexp
  have hprodX : d * n ≤ x := by exact_mod_cast hprodR.trans hRleX
  have hnx : n.Coprime x :=
    Nat.Coprime.of_dvd_right (dvd_mul_right x d) hn'.2.2.2
  simp only [sieveNormIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.mul_pos hd'.2.1 hn'.2.1, hprodR,
    hd'.2.2.2.mul_left hnx⟩

theorem div_mem_sieveNumeratorIndices_of_squarefree
    {x r d : ℕ} {ε : ℝ} (hrsq : Squarefree r)
    (hr : r ∈ sieveNormIndices x ε) (hdr : d ∣ r) :
    r / d ∈ sieveNumeratorIndices x ε d := by
  have hr' := hr
  simp only [sieveNormIndices, Finset.mem_filter,
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
  have hdx : d.Coprime x :=
    Nat.Coprime.of_dvd_left hdr hr'.2.2.2
  have hnx : (r / d).Coprime x :=
    Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hdr) hr'.2.2.2
  have hnd : (r / d).Coprime d :=
    by
      have hgd : r.gcd d = d := Nat.gcd_eq_right_iff_dvd.mpr hdr
      simpa [hgd] using
        (Nat.coprime_div_gcd_of_squarefree hrsq hdpos.ne')
  simp only [sieveNumeratorIndices, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨by omega, hnpos, hbound,
    hnx.mul_right hnd⟩

theorem sieveNumerator_eq_sum_squarefree (x d : ℕ) (ε : ℝ) :
    sieveNumerator x ε d =
      ∑ n ∈ (sieveNumeratorIndices x ε d).filter Squarefree,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / fW n := by
  rw [sieveNumerator]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnfilter
  have hnonsq : ¬Squarefree n := by
    intro hsq
    exact hnfilter (Finset.mem_filter.mpr ⟨hn, hsq⟩)
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnonsq]
  norm_num

theorem sum_sieveWeightTransform_eq_sum_squarefree
    {x k : ℕ} {ε : ℝ} :
    (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          sieveNumerator x ε d) =
      ∑ d ∈ (sieveNormIndices x ε).filter
          (fun d => k ∣ d ∧ Squarefree d),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          sieveNumerator x ε d := by
  let A := (sieveNormIndices x ε).filter (k ∣ ·)
  let B := (sieveNormIndices x ε).filter
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

noncomputable def sieveTransformSource (x k : ℕ) (ε : ℝ) :
    Finset (ℕ × ℕ) :=
  (sieveNormIndices x ε ×ˢ Finset.range (x + 1)).filter fun z =>
    k ∣ z.1 ∧ Squarefree z.1 ∧
      z.2 ∈ sieveNumeratorIndices x ε z.1 ∧ Squarefree z.2

noncomputable def sieveTransformTarget (x k : ℕ) (ε : ℝ) :
    Finset (ℕ × ℕ) :=
  (sieveNormIndices x ε ×ˢ Finset.range (x + 1)).filter fun z =>
    k ∣ z.1 ∧ Squarefree z.1 ∧
      z.2 ∈ z.1.divisors ∧ k ∣ z.2

/-- Reindex the numerator convolution by `r = d n`. -/
theorem sum_sieveTransformSource_eq_target
    {x k : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε) :
    (∑ z ∈ sieveTransformSource x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 / fW z.2)) =
      ∑ z ∈ sieveTransformTarget x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          ((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ) := by
  refine Finset.sum_bij (fun z _ => (z.1 * z.2, z.1)) ?_ ?_ ?_ ?_
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hprod := Finset.mem_product.mp hz'.1
    have hmulS := mul_mem_sieveNormIndices_of_mem_numerator
      hx1 hε0 hprod.1 hz'.2.2.2.1
    have hnxd : z.2.Coprime (x * z.1) := by
      have hn := hz'.2.2.2.1
      simp only [sieveNumeratorIndices, Finset.mem_filter,
        Finset.mem_range] at hn
      exact hn.2.2.2
    have hcop : z.1.Coprime z.2 :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left z.1 x) hnxd).symm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hmulS, ?_⟩,
      dvd_mul_of_dvd_left hz'.2.1 z.2,
      (Nat.squarefree_mul_iff.mpr ⟨hcop, hz'.2.2.1, hz'.2.2.2.2⟩), ?_, hz'.2.1⟩
    · have hzS := hprod.1
      simp only [sieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hzS
      exact Finset.mem_range.mpr (by omega)
    · exact Nat.mem_divisors.mpr
        ⟨dvd_mul_right z.1 z.2, Nat.mul_ne_zero
          (hz'.2.2.1.ne_zero) (hz'.2.2.2.2.ne_zero)⟩
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
    · have hdS := mem_sieveNormIndices_of_dvd hyprod.1 hydvd
      have hnN := div_mem_sieveNumeratorIndices_of_squarefree
        hy'.2.2.1 hyprod.1 hydvd
      have hnrange : y.1 / y.2 < x + 1 := by
        have hyS := hyprod.1
        simp only [sieveNormIndices, Finset.mem_filter,
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
    simp only [sieveNumeratorIndices, Finset.mem_filter,
      Finset.mem_range] at hn
    have hcop : z.1.Coprime z.2 :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left z.1 x) hn.2.2.2).symm
    have hd0 : z.1 ≠ 0 := hz'.2.2.1.ne_zero
    have hn0 : z.2 ≠ 0 := hz'.2.2.2.2.ne_zero
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        hcop.gcd_eq_one,
      fW_mul_of_coprime hd0 hn0 hcop,
      Nat.mul_div_cancel_left z.2 (by omega : 0 < z.1)]
    push_cast
    ring

theorem sum_sieveWeightTransform_eq_source
    {x k : ℕ} {ε : ℝ} :
    (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          sieveNumerator x ε d) =
      ∑ z ∈ sieveTransformSource x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) ^ 2 / fW z.2) := by
  rw [sum_sieveWeightTransform_eq_sum_squarefree]
  unfold sieveTransformSource
  simp only [Finset.sum_filter, Finset.sum_product]
  simp_rw [sieveNumerator_eq_sum_squarefree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hkd : k ∣ d
  swap
  · simp [hkd]
  by_cases hdsq : Squarefree d
  swap
  · simp [hkd, hdsq]
  simp only [hkd, hdsq, and_self, true_and, if_true]
  rw [sieveNumeratorIndices, Finset.sum_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  by_cases hnmem :
      1 ≤ n ∧
        (n : ℝ) ≤ (x : ℝ) ^ ((4 : ℝ)⁻¹ - ε / 2) / d ∧
        n.Coprime (x * d)
  swap
  · simp [hnmem, hnle]
  by_cases hnsq : Squarefree n <;> simp [hnmem, hnsq, hnle]

theorem sum_moebius_divisors (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d =
      if n = 1 then 1 else 0 := by
  calc
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
        ((↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
          ArithmeticFunction.moebius) n :=
      ArithmeticFunction.coe_zeta_mul_apply.symm
    _ = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.coe_zeta_mul_moebius]
    _ = if n = 1 then 1 else 0 := rfl

theorem sum_moebius_divisors_multiples
    {k r : ℕ} (hk : 0 < k) (hkr : k ∣ r) :
    ∑ d ∈ r.divisors.filter (k ∣ ·),
        ArithmeticFunction.moebius (r / d) =
      if r = k then 1 else 0 := by
  by_cases hr0 : r = 0
  · subst r
    simp [Nat.ne_of_lt hk]
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  calc
    (∑ d ∈ r.divisors.filter (k ∣ ·),
        ArithmeticFunction.moebius (r / d)) =
      ∑ e ∈ (r / k).divisors,
        ArithmeticFunction.moebius ((r / k) / e) := by
      refine Finset.sum_bij (fun d _ => d / k) ?_ ?_ ?_ ?_
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd'.1
        exact Nat.mem_divisors.mpr ⟨by
          rw [Nat.dvd_div_iff_mul_dvd hkr]
          simpa [Nat.mul_div_cancel' hd'.2, mul_comm] using hdr,
          (Nat.div_pos (Nat.le_of_dvd hr hkr) hk).ne'⟩
      · intro d hd e he hde
        have hdk : k ∣ d := (Finset.mem_filter.mp hd).2
        have hek : k ∣ e := (Finset.mem_filter.mp he).2
        calc
          d = d / k * k := (Nat.div_mul_cancel hdk).symm
          _ = e / k * k := congrArg (· * k) hde
          _ = e := Nat.div_mul_cancel hek
      · intro e he
        have he' := Nat.mem_divisors.mp he
        refine ⟨k * e, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Nat.mem_divisors.mpr ⟨?_, hr.ne'⟩, dvd_mul_right k e⟩
          exact (Nat.dvd_div_iff_mul_dvd hkr).mp (by
            simpa [mul_comm] using he'.1)
        · simp [Nat.mul_div_cancel_left e hk]
      · intro d hd
        rw [Nat.div_div_eq_div_mul, mul_comm]
        rw [Nat.div_mul_cancel (Finset.mem_filter.mp hd).2]
    _ = ∑ e ∈ (r / k).divisors,
        ArithmeticFunction.moebius e := by
      rw [Nat.sum_div_divisors]
    _ = if r / k = 1 then 1 else 0 :=
      sum_moebius_divisors (r / k)
        (Nat.div_pos (Nat.le_of_dvd hr hkr) hk)
    _ = if r = k then 1 else 0 := by
      have hiff : r / k = 1 ↔ r = k := by
        constructor
        · intro hdiv
          calc
            r = r / k * k := (Nat.div_mul_cancel hkr).symm
            _ = 1 * k := congrArg (· * k) hdiv
            _ = k := one_mul k
        · intro hrk
          subst r
          exact Nat.div_self hk
      exact if_congr hiff rfl rfl

theorem sum_sieveTransformTarget_eq_nested
    {x k : ℕ} {ε : ℝ} :
    (∑ z ∈ sieveTransformTarget x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          ((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ)) =
      ∑ r ∈ (sieveNormIndices x ε).filter
          (fun r => k ∣ r ∧ Squarefree r),
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
          ∑ d ∈ r.divisors.filter (k ∣ ·),
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) := by
  rw [sieveTransformTarget, Finset.sum_filter, Finset.sum_product,
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
    simp only [sieveNormIndices, Finset.mem_filter,
      Finset.mem_range] at hr'
    exact Finset.mem_range.mpr (by
      exact (Nat.le_of_dvd (by omega) hdr).trans_lt (by omega))
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
    _ = _ := by
      rw [Finset.sum_filter]

theorem sum_sieveTransformTarget_eq_moebius_div
    {x k : ℕ} {ε : ℝ} (hk : k ∈ sieveNormIndices x ε) :
    (∑ z ∈ sieveTransformTarget x k ε,
        ((ArithmeticFunction.moebius z.1 : ℤ) : ℝ) / fW z.1 *
          ((ArithmeticFunction.moebius (z.1 / z.2) : ℤ) : ℝ)) =
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) / fW k := by
  rw [sum_sieveTransformTarget_eq_nested]
  have hk' := hk
  simp only [sieveNormIndices, Finset.mem_filter,
    Finset.mem_range] at hk'
  by_cases hksq : Squarefree k
  · have hinner : ∀ r ∈ (sieveNormIndices x ε).filter
        (fun r => k ∣ r ∧ Squarefree r),
        (∑ d ∈ r.divisors.filter (k ∣ ·),
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)) =
          if r = k then 1 else 0 := by
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      exact_mod_cast sum_moebius_divisors_multiples (by omega) hr'.2.1
    have hrewrite :
        (∑ r ∈ (sieveNormIndices x ε).filter
            (fun r => k ∣ r ∧ Squarefree r),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
            ∑ d ∈ r.divisors.filter (k ∣ ·),
              ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)) =
        ∑ r ∈ (sieveNormIndices x ε).filter
            (fun r => k ∣ r ∧ Squarefree r),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / fW r *
            (if r = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hinner r hr]
    rw [hrewrite]
    let T := (sieveNormIndices x ε).filter
      (fun r => k ∣ r ∧ Squarefree r)
    have hkT : k ∈ T := Finset.mem_filter.mpr
      ⟨hk, dvd_rfl, hksq⟩
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
  · have hT : (sieveNormIndices x ε).filter
        (fun r => k ∣ r ∧ Squarefree r) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r hr hpred
      exact hksq (hpred.2.squarefree_of_dvd hpred.1)
    rw [hT]
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hksq]

theorem sum_sieveNumeratorTransform
    {x k : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε0 : 0 ≤ ε)
    (hk : k ∈ sieveNormIndices x ε) :
    (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          sieveNumerator x ε d) =
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) / fW k := by
  rw [sum_sieveWeightTransform_eq_source,
    sum_sieveTransformSource_eq_target hx1 hε0,
    sum_sieveTransformTarget_eq_moebius_div hk]

/-- Möbius transform of Chen's chosen Selberg weights.  This is the
display immediately preceding equation (22). -/
theorem sum_sieveWeight_div_totient
    {x k : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hk : k ∈ sieveNormIndices x ε) :
    (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
        sieveWeight x ε d / (Nat.totient d : ℝ)) =
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) /
        (sieveNorm x ε * fW k) := by
  calc
    (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
        sieveWeight x ε d / (Nat.totient d : ℝ)) =
      ∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / fW d *
          sieveNumerator x ε d / sieveNorm x ε := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [sieveWeight_div_totient_eq hx hx1 hε0 hε
        (Finset.mem_filter.mp hd).1]
      ring
    _ = ((ArithmeticFunction.moebius k : ℤ) : ℝ) /
        (sieveNorm x ε * fW k) := by
      rw [← Finset.sum_div,
        sum_sieveNumeratorTransform hx1 hε0 hk]
      ring

/-- Equation (22): the quadratic Selberg coefficient is exactly the
reciprocal of the normalizing sum. -/
theorem sieveMainCoefficient_eq_inv_sieveNorm
    {x : ℕ} {ε : ℝ} (hx : Even x) (hx1 : 1 ≤ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    sieveMainCoefficient x ε = (sieveNorm x ε)⁻¹ := by
  rw [sieveMainCoefficient_eq_diagonal hx hx1 hε0 hε]
  have hrewrite :
      (∑ k ∈ sieveNormIndices x ε,
          fW k *
            (∑ d ∈ (sieveNormIndices x ε).filter (k ∣ ·),
              sieveWeight x ε d / (Nat.totient d : ℝ)) ^ 2) =
        ∑ k ∈ sieveNormIndices x ε,
          fW k *
            (((ArithmeticFunction.moebius k : ℤ) : ℝ) /
              (sieveNorm x ε * fW k)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [sum_sieveWeight_div_totient hx hx1 hε0 hε hk]
  rw [hrewrite]
  have hS : sieveNorm x ε ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le
      (one_le_sieveNorm hx hx1 hε0 hε))
  calc
    (∑ k ∈ sieveNormIndices x ε,
        fW k *
          (((ArithmeticFunction.moebius k : ℤ) : ℝ) /
            (sieveNorm x ε * fW k)) ^ 2) =
      (sieveNorm x ε) ^ (-2 : ℤ) *
        ∑ k ∈ sieveNormIndices x ε,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 / fW k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := hk
      simp only [sieveNormIndices, Finset.mem_filter,
        Finset.mem_range] at hk'
      have hkodd : Odd k :=
        (Nat.Coprime.of_dvd_right hx.two_dvd hk'.2.2.2).odd_of_right
      have hfk : fW k ≠ 0 :=
        (fW_pos_of_odd (by omega) hkodd).ne'
      field_simp [hS, hfk]
    _ = (sieveNorm x ε) ^ (-2 : ℤ) * sieveNorm x ε := by rfl
    _ = (sieveNorm x ε)⁻¹ := by
      field_simp [hS]

end Chen
