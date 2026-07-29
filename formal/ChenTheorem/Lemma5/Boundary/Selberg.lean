import ChenTheorem.Lemma5.Boundary.Sieve

/-!
# The Selberg-sieve stage of Chen's Lemma 5

This file develops the multiplicative local-density input needed to
diagonalize the quadratic form obtained in `Lemma5/Boundary/Sieve.lean`.
-/

open scoped Classical

namespace Chen

/-- The roots of the transition polynomial modulo a product of coprime
positive moduli are the Cartesian product of its roots modulo the two
factors. -/
theorem smoothingTransitionZModRoots_image_chineseRemainder
    {x m n : ℕ} {q : ℕ × ℕ}
    (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    letI : NeZero m := ⟨hm.ne'⟩
    letI : NeZero n := ⟨hn.ne'⟩
    letI : NeZero (m * n) := ⟨(mul_pos hm hn).ne'⟩
    (smoothingTransitionZModRoots x q (m * n)).image
        (ZMod.chineseRemainder hcop) =
      smoothingTransitionZModRoots x q m ×ˢ
        smoothingTransitionZModRoots x q n := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero (m * n) := ⟨(mul_pos hm hn).ne'⟩
  let e := ZMod.chineseRemainder hcop
  ext z
  simp only [Finset.mem_image, smoothingTransitionZModRoots,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hz := congrArg e ha
    constructor
    · have hz₁ := congrArg Prod.fst hz
      simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.fst_mul,
        Prod.fst_sub, Prod.fst_natCast, Prod.fst_zero, e] using hz₁
    · have hz₂ := congrArg Prod.snd hz
      simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.snd_mul,
        Prod.snd_sub, Prod.snd_natCast, Prod.snd_zero, e] using hz₂
  · rintro ⟨hz₁, hz₂⟩
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    apply e.injective
    rw [map_zero]
    have hmap :
        e (e.symm z *
          ((x : ZMod (m * n)) -
            (q.1 * q.2 : ℕ) * e.symm z)) =
          z * ((x : ZMod m × ZMod n) -
            (q.1 * q.2 : ℕ) * z) := by
      simp only [map_mul, map_sub, map_natCast,
        e.apply_symm_apply]
    rw [hmap]
    apply Prod.ext
    · change z.1 *
        ((x : ZMod m) - (q.1 * q.2 : ℕ) * z.1) = 0
      exact hz₁
    · change z.2 *
        ((x : ZMod n) - (q.1 * q.2 : ℕ) * z.2) = 0
      exact hz₂

/-- The number of roots of the transition polynomial is multiplicative
on positive coprime moduli. -/
theorem smoothingTransitionRootCount_mul_of_coprime
    {x m n : ℕ} {q : ℕ × ℕ}
    (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    smoothingTransitionRootCount x q (m * n) =
      smoothingTransitionRootCount x q m *
        smoothingTransitionRootCount x q n := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero (m * n) := ⟨(mul_pos hm hn).ne'⟩
  let e := ZMod.chineseRemainder hcop
  calc
    smoothingTransitionRootCount x q (m * n) =
        (smoothingTransitionZModRoots x q (m * n)).card :=
      smoothingTransitionRootCount_eq_zmodRoots_card (mul_pos hm hn)
    _ = ((smoothingTransitionZModRoots x q (m * n)).image e).card := by
      rw [Finset.card_image_of_injective _ e.injective]
    _ = (smoothingTransitionZModRoots x q m ×ˢ
          smoothingTransitionZModRoots x q n).card := by
      rw [smoothingTransitionZModRoots_image_chineseRemainder hm hn hcop]
    _ = (smoothingTransitionZModRoots x q m).card *
          (smoothingTransitionZModRoots x q n).card :=
      Finset.card_product _ _
    _ = smoothingTransitionRootCount x q m *
          smoothingTransitionRootCount x q n := by
      rw [← smoothingTransitionRootCount_eq_zmodRoots_card hm,
        ← smoothingTransitionRootCount_eq_zmodRoots_card hn]

/-- The local density of roots of the transition polynomial. -/
noncomputable def smoothingTransitionNu
    (x : ℕ) (q : ℕ × ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => (smoothingTransitionRootCount x q d : ℝ) / d, by
    simp [smoothingTransitionRootCount,
      smoothingTransitionRootResidues]⟩

@[simp]
theorem smoothingTransitionNu_apply
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) :
    smoothingTransitionNu x q d =
      (smoothingTransitionRootCount x q d : ℝ) / d :=
  rfl

/-- The local-density arithmetic function is multiplicative. -/
theorem smoothingTransitionNu_isMultiplicative
    (x : ℕ) (q : ℕ × ℕ) :
    (smoothingTransitionNu x q).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · have hroots :
    smoothingTransitionRootResidues x q 1 = {0} := by
      ext r
      simp only [smoothingTransitionRootResidues, Finset.mem_filter,
        Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, -⟩
        omega
      · intro hr
        subst r
        simp
    simp [smoothingTransitionNu, smoothingTransitionRootCount, hroots]
  · intro m n hm hn hcop
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [smoothingTransitionNu_apply, smoothingTransitionNu_apply,
      smoothingTransitionNu_apply,
      smoothingTransitionRootCount_mul_of_coprime hmpos hnpos hcop,
      Nat.cast_mul, Nat.cast_mul]
    exact (div_mul_div_comm _ _ _ _).symm

/-- At a sieving prime the local density is `1 / p` when `p ∣ x` and
`2 / p` otherwise. -/
theorem smoothingTransitionNu_prime
    {x p : ℕ} {q : ℕ × ℕ} (hp : p.Prime)
    (hpb : ¬p ∣ q.1 * q.2) :
    smoothingTransitionNu x q p =
      (if p ∣ x then 1 else 2) / (p : ℝ) := by
  rw [smoothingTransitionNu_apply,
    smoothingTransitionRootCount_prime hp hpb]
  split_ifs <;> norm_num

theorem smoothingTransitionNu_pos_of_sievePrime
    {x p : ℕ} {q : ℕ × ℕ} (hx : 1 < x)
    (hq : q ∈ chenPairs x) (hp : p.Prime)
    (hpdvd : p ∣ transitionSieveProduct x) :
    0 < smoothingTransitionNu x q p := by
  rw [smoothingTransitionNu_prime hp
    (transitionSievePrime_not_dvd_pair hx hq hp hpdvd)]
  have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.2 hp.pos
  split_ifs
  · exact div_pos (by norm_num) hpR
  · exact div_pos (by norm_num) hpR

private theorem one_or_two_div_prime_lt_one
    {x p : ℕ} (hxEven : Even x) (hp : p.Prime) :
    (if p ∣ x then (1 : ℝ) else 2) / (p : ℝ) < 1 := by
  by_cases hpx : p ∣ x
  · rw [if_pos hpx]
    have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.2 hp.pos
    rw [div_lt_one hpR]
    exact_mod_cast hp.one_lt
  · rw [if_neg hpx]
    have hpne : p ≠ 2 := by
      intro hp2
      subst p
      exact hpx (even_iff_two_dvd.mp hxEven)
    have hptwo : 2 < p := by
      exact lt_of_le_of_ne hp.two_le hpne.symm
    have hptwoR : (2 : ℝ) < (p : ℝ) :=
      Nat.cast_lt.2 hptwo
    have hpR : (0 : ℝ) < (p : ℝ) := by linarith
    rw [div_lt_one hpR]
    exact hptwoR

theorem smoothingTransitionNu_lt_one_of_sievePrime
    {x p : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hp : p.Prime)
    (hpdvd : p ∣ transitionSieveProduct x) :
    smoothingTransitionNu x q p < 1 := by
  rw [smoothingTransitionNu_prime hp
    (transitionSievePrime_not_dvd_pair hx hq hp hpdvd)]
  exact one_or_two_div_prime_lt_one hxEven hp

/-- The abstract sieve carrying the transition polynomial's prime product
and local density.  Its support fields are dummy data: below we use this
object only to invoke Mathlib's algebraic diagonalization of the main
quadratic form; the indexed counting inequality remains the one proved in
`Lemma5/Boundary/Sieve.lean`. -/
noncomputable def smoothingTransitionBoundingSieve
    (x : ℕ) (q : ℕ × ℕ) (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) : BoundingSieve where
  support := ∅
  prodPrimes := transitionSieveProduct x
  prodPrimes_squarefree := transitionSieveProduct_squarefree x
  weights := 0
  weights_nonneg := by simp
  totalMass := 0
  nu := smoothingTransitionNu x q
  nu_mult := smoothingTransitionNu_isMultiplicative x q
  nu_pos_of_prime := fun p hp hpdvd =>
    smoothingTransitionNu_pos_of_sievePrime hx hq hp hpdvd
  nu_lt_one_of_prime := fun p hp hpdvd =>
    smoothingTransitionNu_lt_one_of_sievePrime hx hxEven hq hp hpdvd

/-- Extend a level-`R` weight by zero outside the level. -/
noncomputable def smoothingTruncatedWeight
    (R : ℕ) (w : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d ≤ R then w d else 0

@[simp]
theorem smoothingTruncatedWeight_of_le
    {R d : ℕ} {w : ℕ → ℝ} (hd : d ≤ R) :
    smoothingTruncatedWeight R w d = w d := by
  simp [smoothingTruncatedWeight, hd]

@[simp]
theorem smoothingTruncatedWeight_of_not_le
    {R d : ℕ} {w : ℕ → ℝ} (hd : ¬d ≤ R) :
    smoothingTruncatedWeight R w d = 0 := by
  simp [smoothingTruncatedWeight, hd]

/-- The custom indexed main quadratic form is exactly Mathlib's
`lambdaSquared` main sum after the weights are extended by zero. -/
theorem transitionMainQuadratic_eq_mainSum_lambdaSquared
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (w : ℕ → ℝ) :
    transitionMainQuadratic x q R w =
      (smoothingTransitionBoundingSieve x q hx hxEven hq).mainSum
        (BoundingSieve.lambdaSquared
          (smoothingTruncatedWeight R w)) := by
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul]
  unfold transitionMainQuadratic truncatedSieveDivisors
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  by_cases hd₁R : d₁ ≤ R
  · simp only [hd₁R, if_true, smoothingTruncatedWeight_of_le]
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    by_cases hd₂R : d₂ ≤ R
    · simp only [hd₂R, if_true,
        smoothingTruncatedWeight_of_le]
      have hgcd :
          d₁.gcd d₂ ∣ transitionSieveProduct x :=
        (Nat.gcd_dvd_left d₁ d₂).trans
          (Nat.dvd_of_mem_divisors hd₁)
      have hnugcd :
          s.nu (d₁.gcd d₂) ≠ 0 :=
        ne_of_gt (s.nu_pos_of_dvd_prodPrimes hgcd)
      have hlcm :=
        s.nu_mult.map_lcm hnugcd
      change
        w d₁ * w d₂ * s.nu (d₁.lcm d₂) =
          s.nu d₁ * w d₁ * s.nu d₂ * w d₂ *
            (s.nu (d₁.gcd d₂))⁻¹
      rw [hlcm]
      field_simp
    · simp [hd₂R, smoothingTruncatedWeight]
  · simp [hd₁R, smoothingTruncatedWeight]

/-- The truncated Selberg mass `G(R)`.  This is the denominator in the
optimal value of the diagonal quadratic form. -/
noncomputable def truncatedSelbergMass
    (s : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ l ∈ truncatedSieveDivisors s.prodPrimes R,
    s.selbergTerms l

theorem truncatedSelbergMass_pos
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    0 < truncatedSelbergMass s R := by
  unfold truncatedSelbergMass
  apply Finset.sum_pos'
  · intro l hl
    exact (s.selbergTerms_pos
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)).le
  · refine ⟨1, one_mem_truncatedSieveDivisors
      s.prodPrimes_ne_zero hR, ?_⟩
    exact s.selbergTerms_pos (one_dvd _)

/-- Diagonal form of the indexed transition main term. -/
theorem transitionMainQuadratic_eq_diagonal
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (w : ℕ → ℝ) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    transitionMainQuadratic x q R w =
      ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            s.nu d * smoothingTruncatedWeight R w d
          else 0) ^ 2 := by
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  rw [transitionMainQuadratic_eq_mainSum_lambdaSquared hx hxEven hq]
  exact s.mainSum_lambdaSquared_eq_sum_mul_sum_sq
    (smoothingTruncatedWeight R w)

/-- There are at most `d` roots modulo `d`. -/
theorem smoothingTransitionRootCount_le
    (x : ℕ) (q : ℕ × ℕ) (d : ℕ) :
    smoothingTransitionRootCount x q d ≤ d := by
  unfold smoothingTransitionRootCount
  exact (Finset.card_filter_le _ _).trans_eq
    (Finset.card_range d)

/-- The number of retained divisors is at most `R + 1`; this deliberately
crude estimate is sufficient for the polynomial error term. -/
theorem truncatedSieveDivisors_card_le
    (P R : ℕ) :
    (truncatedSieveDivisors P R).card ≤ R + 1 := by
  have hsub :
      truncatedSieveDivisors P R ⊆ Finset.range (R + 1) := by
    intro d hd
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hd).2
  simpa using Finset.card_le_card hsub

/-- A crude but uniform error estimate for any truncated weights bounded
by one.  Its polynomial dependence on `R` lets us choose a very small
power of `x` as the Selberg level. -/
theorem transitionErrorQuadratic_le
    (x : ℕ) (q : ℕ × ℕ) (R : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R, |w d| ≤ 1) :
    transitionErrorQuadratic x q R w ≤
      ((R + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (R : ℝ) ^ 2 + 1) := by
  let D :=
    truncatedSieveDivisors (transitionSieveProduct x) R
  let B : ℝ := 3 * (R : ℝ) ^ 2 + 1
  unfold transitionErrorQuadratic
  change (∑ d₁ ∈ D, ∑ d₂ ∈ D,
      |w d₁ * w d₂| *
        (3 * smoothingTransitionRootCount x q (d₁.lcm d₂) + 1)) ≤
    ((R + 1 : ℕ) : ℝ) ^ 2 * B
  calc
    (∑ d₁ ∈ D, ∑ d₂ ∈ D,
        |w d₁ * w d₂| *
          (3 * smoothingTransitionRootCount x q (d₁.lcm d₂) + 1)) ≤
        ∑ _d₁ ∈ D, ∑ _d₂ ∈ D, B := by
      apply Finset.sum_le_sum
      intro d₁ hd₁
      apply Finset.sum_le_sum
      intro d₂ hd₂
      have hd₁R : d₁ ≤ R := (Finset.mem_filter.mp hd₁).2
      have hd₂R : d₂ ≤ R := (Finset.mem_filter.mp hd₂).2
      have hd₁pos : 0 < d₁ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₁).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hd₂pos : 0 < d₂ :=
        Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hd₂).1)
          (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
      have hlcmle : d₁.lcm d₂ ≤ d₁ * d₂ :=
        Nat.le_of_dvd (Nat.mul_pos hd₁pos hd₂pos)
          (Nat.lcm_dvd_mul d₁ d₂)
      have hroot :
          smoothingTransitionRootCount x q (d₁.lcm d₂) ≤
            R * R :=
        (smoothingTransitionRootCount_le x q _).trans
          (hlcmle.trans (Nat.mul_le_mul hd₁R hd₂R))
      have hweight : |w d₁ * w d₂| ≤ 1 := by
        rw [abs_mul]
        nlinarith [hw d₁ hd₁, hw d₂ hd₂,
          abs_nonneg (w d₁), abs_nonneg (w d₂)]
      have hfactor :
          3 * (smoothingTransitionRootCount x q
              (d₁.lcm d₂) : ℝ) + 1 ≤ B := by
        dsimp only [B]
        exact_mod_cast (show
          3 * smoothingTransitionRootCount x q (d₁.lcm d₂) + 1 ≤
            3 * R ^ 2 + 1 by
          simpa [pow_two] using
            Nat.add_le_add_right (Nat.mul_le_mul_left 3 hroot) 1)
      simpa using
        mul_le_mul hweight hfactor (by positivity) (by positivity)
    _ = (D.card : ℝ) ^ 2 * B := by
      simp [pow_two]
      ring
    _ ≤ ((R + 1 : ℕ) : ℝ) ^ 2 * B := by
      have hcard :
          (D.card : ℝ) ≤ (R + 1 : ℕ) := by
        exact_mod_cast truncatedSieveDivisors_card_le
          (transitionSieveProduct x) R
      have hcard0 : (0 : ℝ) ≤ D.card := by positivity
      have hR0 : (0 : ℝ) ≤ (R + 1 : ℕ) := by positivity
      have hsq : (D.card : ℝ) ^ 2 ≤
          ((R + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hsq (by
        dsimp only [B]
        positivity)

end Chen
