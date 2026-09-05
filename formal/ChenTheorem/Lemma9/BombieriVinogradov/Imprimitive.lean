import ChenTheorem.Lemma9.BombieriVinogradov.Induction

open scoped Classical Nat.Prime

namespace Chen.BombieriVinogradov

/-!
# The imprimitive-character error

A von-Mangoldt term on which a lifted character can differ from its primitive
source is a prime power whose base prime divides the ambient modulus.  We use
a deliberately coarse finite counting bound; its polynomial-in-`Q` size is
harmless at the Bombieri--Vinogradov level after the logarithmic loss in `Q`.
-/

/-- The uniform error used when an ambient character modulo `q` is replaced
by its primitive source. -/
noncomputable def imprimitiveLiftError (x q : ℕ) : ℝ :=
  2 * (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x

/-- Bad indices carrying nonzero von-Mangoldt weight. -/
noncomputable def imprimitiveBadPrimePowers (x q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n =>
    ¬n.Coprime q ∧ ArithmeticFunction.vonMangoldt n ≠ 0

/-- A coarse finite superset of all relevant prime powers: base at most `q`
and exponent at most `log₂ x`. -/
noncomputable def imprimitivePrimePowerCandidates (x q : ℕ) : Finset ℕ :=
  ((Finset.range (q + 1)) ×ˢ (Finset.range (Nat.log 2 x + 1))).image
    (fun pk : ℕ × ℕ => pk.1 ^ (pk.2 + 1))

theorem imprimitiveBadPrimePowers_subset_candidates
    {x q : ℕ} (hq : 0 < q) :
    imprimitiveBadPrimePowers x q ⊆
      imprimitivePrimePowerCandidates x q := by
  intro n hn
  rw [imprimitiveBadPrimePowers, Finset.mem_filter] at hn
  rcases hn with ⟨hnrange, hncop, hΛ⟩
  have hnpp : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hnpp
  have hpcop : ¬p.Coprime q := by
    intro h
    exact hncop (h.pow_left k)
  have hpdvd : p ∣ q := hp.dvd_iff_not_coprime.mpr hpcop
  have hpq : p ≤ q := Nat.le_of_dvd hq hpdvd
  have hpowtwo : 2 ^ k ≤ p ^ k :=
    Nat.pow_le_pow_left hp.two_le k
  have hpkx : p ^ k ≤ x := (Finset.mem_Icc.mp hnrange).2
  have hklog : k ≤ Nat.log 2 x :=
    Nat.le_log_of_pow_le (by omega) (hpowtwo.trans hpkx)
  rw [imprimitivePrimePowerCandidates, Finset.mem_image]
  refine ⟨(p, k - 1), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    constructor <;> omega
  · simp only
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]

theorem card_imprimitiveBadPrimePowers_le
    {x q : ℕ} (hq : 0 < q) :
    (imprimitiveBadPrimePowers x q).card ≤
      (q + 1) * (Nat.log 2 x + 1) := by
  calc
    (imprimitiveBadPrimePowers x q).card ≤
        (imprimitivePrimePowerCandidates x q).card :=
      Finset.card_le_card (imprimitiveBadPrimePowers_subset_candidates hq)
    _ ≤ ((Finset.range (q + 1)) ×ˢ
          (Finset.range (Nat.log 2 x + 1))).card := by
      rw [imprimitivePrimePowerCandidates]
      exact Finset.card_image_le
    _ = (q + 1) * (Nat.log 2 x + 1) := by simp

/-- Coarse total von-Mangoldt mass on the imprimitive support. -/
theorem sum_bad_vonMangoldt_le
    {x q : ℕ} (hx : 2 ≤ x) (hq : 0 < q) :
    (∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬n.Coprime q),
        ArithmeticFunction.vonMangoldt n) ≤
      (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x := by
  let bad := (Finset.Icc 1 x).filter (fun n => ¬n.Coprime q)
  have hrestrict :
      (∑ n ∈ bad, ArithmeticFunction.vonMangoldt n) =
        ∑ n ∈ imprimitiveBadPrimePowers x q,
          ArithmeticFunction.vonMangoldt n := by
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [imprimitiveBadPrimePowers, Finset.mem_filter] at hn
      exact Finset.mem_filter.mpr ⟨hn.1, hn.2.1⟩
    · intro n hnbad hnnot
      by_contra hΛ
      exact hnnot (by
        rw [imprimitiveBadPrimePowers, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hnbad).1,
          (Finset.mem_filter.mp hnbad).2, hΛ⟩)
  change (∑ n ∈ bad, ArithmeticFunction.vonMangoldt n) ≤ _
  rw [hrestrict]
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  calc
    (∑ n ∈ imprimitiveBadPrimePowers x q,
        ArithmeticFunction.vonMangoldt n) ≤
      ∑ _n ∈ imprimitiveBadPrimePowers x q, Real.log x := by
      apply Finset.sum_le_sum
      intro n hn
      have hnrange := (Finset.mem_filter.mp
        (show n ∈ (Finset.Icc 1 x).filter (fun n =>
          ¬n.Coprime q ∧ ArithmeticFunction.vonMangoldt n ≠ 0) from hn)).1
      have hndata := Finset.mem_Icc.mp hnrange
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hndata.2))
    _ = (imprimitiveBadPrimePowers x q).card * Real.log x := by simp
    _ ≤ (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x := by
      gcongr
      exact_mod_cast card_imprimitiveBadPrimePowers_le hq

/-- Uniform norm bound for replacing a lifted character by its primitive
source in a twisted von-Mangoldt sum. -/
theorem norm_twistedPsi_primitiveLift_sub_le
    (x q : ℕ) [NeZero q]
    (z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive})
    (hx : 2 ≤ x) :
    ‖twistedPsi x (Chen.primitiveLift q z) - twistedPsi x z.2.1‖ ≤
      2 * (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x := by
  rw [twistedPsi_primitiveLift_sub_eq_bad_sum]
  calc
    ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬n.Coprime q),
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Chen.primitiveLift q z n - z.2.1 n)‖ ≤
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬n.Coprime q),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          (Chen.primitiveLift q z n - z.2.1 n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬n.Coprime q),
        2 * ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hchars :
          ‖Chen.primitiveLift q z n - z.2.1 n‖ ≤ 2 := by
        calc
          ‖Chen.primitiveLift q z n - z.2.1 n‖ ≤
              ‖Chen.primitiveLift q z n‖ + ‖z.2.1 n‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add
            (DirichletCharacter.norm_le_one _ _)
            (DirichletCharacter.norm_le_one _ _)
          _ = 2 := by norm_num
      nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
    _ = 2 * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬n.Coprime q),
        ArithmeticFunction.vonMangoldt n := by rw [Finset.mul_sum]
    _ ≤ 2 * ((((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) *
        Real.log x) :=
      mul_le_mul_of_nonneg_left
        (sum_bad_vonMangoldt_le hx (NeZero.pos q)) (by norm_num)
    _ = 2 * (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x := by
      ring

theorem norm_adjustedTwistedPsi_primitiveLift_sub_le
    (x q : ℕ) [NeZero q]
    (z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive})
    (hx : 2 ≤ x) :
    ‖adjustedTwistedPsi x (Chen.primitiveLift q z) -
        adjustedTwistedPsi x z.2.1‖ ≤
      2 * (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x := by
  rw [adjustedTwistedPsi_primitiveLift_sub]
  exact norm_twistedPsi_primitiveLift_sub_le x q z hx

/-- Pointwise replacement of an ambient character by its primitive source,
including the explicit imprimitive error. -/
theorem norm_adjustedTwistedPsi_primitiveLift_le
    (x q : ℕ) [NeZero q]
    (z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive})
    (hx : 2 ≤ x) :
    ‖adjustedTwistedPsi x (Chen.primitiveLift q z)‖ ≤
      ‖adjustedTwistedPsi x z.2.1‖ +
        2 * (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x := by
  calc
    ‖adjustedTwistedPsi x (Chen.primitiveLift q z)‖ =
        ‖adjustedTwistedPsi x z.2.1 +
          (adjustedTwistedPsi x (Chen.primitiveLift q z) -
            adjustedTwistedPsi x z.2.1)‖ := by
      congr 1
      abel
    _ ≤ ‖adjustedTwistedPsi x z.2.1‖ +
        ‖adjustedTwistedPsi x (Chen.primitiveLift q z) -
          adjustedTwistedPsi x z.2.1‖ := norm_add_le _ _
    _ ≤ ‖adjustedTwistedPsi x z.2.1‖ +
        2 * (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log x := by
      gcongr
      exact norm_adjustedTwistedPsi_primitiveLift_sub_le x q z hx

/-- Sum of the primitive-source norms occurring in the conductor partition
at one ambient modulus.  The `q = 0` branch only makes the definition total. -/
noncomputable def primitiveSourceAdjustedNormSum (x q : ℕ) : ℝ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ z : Σ k : ↥q.divisors,
      {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
        ‖adjustedTwistedPsi x z.2.1‖

/-- Primitive adjusted norm at one exact conductor. -/
noncomputable def primitiveConductorAdjustedNormSum (x k : ℕ) : ℝ :=
  ∑ ψ : {χ : DirichletCharacter ℂ k // χ.IsPrimitive},
    ‖adjustedTwistedPsi x ψ.1‖

/-- Expand the source sum at an ambient modulus as a sum over its possible
primitive conductors. -/
theorem primitiveSourceAdjustedNormSum_eq_sum_divisors
    (x q : ℕ) [NeZero q] :
    primitiveSourceAdjustedNormSum x q =
      ∑ k : ↥q.divisors, primitiveConductorAdjustedNormSum x k.1 := by
  rw [primitiveSourceAdjustedNormSum, dif_neg (NeZero.ne q),
    Fintype.sum_sigma]
  rfl

/-- The same conductor expansion with the divisor subtype replaced by the
ordinary finite divisor set. -/
theorem primitiveSourceAdjustedNormSum_eq_sum_divisors'
    (x q : ℕ) [NeZero q] :
    primitiveSourceAdjustedNormSum x q =
      ∑ k ∈ q.divisors, primitiveConductorAdjustedNormSum x k := by
  rw [primitiveSourceAdjustedNormSum_eq_sum_divisors]
  symm
  exact Finset.sum_subtype q.divisors (by simp)
    (primitiveConductorAdjustedNormSum x)

/-- At one positive ambient modulus, replacing every character by its
primitive source costs at most one copy of `imprimitiveLiftError` per
character. -/
theorem primitiveLiftAdjustedNormSum_le_source_add_error
    (x q : ℕ) [NeZero q] (hx : 2 ≤ x) :
    primitiveLiftAdjustedNormSum x q ≤
      primitiveSourceAdjustedNormSum x q +
        (Nat.totient q : ℝ) * imprimitiveLiftError x q := by
  have hcard :
      Fintype.card
          (Σ k : ↥q.divisors,
            {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive}) =
        Nat.totient q := by
    calc
      Fintype.card
          (Σ k : ↥q.divisors,
            {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive}) =
          Fintype.card (DirichletCharacter ℂ q) :=
        Fintype.card_congr (Chen.primitiveLiftEquiv q)
      _ = Nat.totient q := by
        rw [Fintype.card_eq_nat_card]
        exact
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [primitiveLiftAdjustedNormSum, dif_neg (NeZero.ne q),
    primitiveSourceAdjustedNormSum, dif_neg (NeZero.ne q)]
  calc
    (∑ z : Σ k : ↥q.divisors,
        {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
          ‖adjustedTwistedPsi x (Chen.primitiveLift q z)‖) ≤
        ∑ z : Σ k : ↥q.divisors,
          {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
            (‖adjustedTwistedPsi x z.2.1‖ +
              imprimitiveLiftError x q) := by
      apply Finset.sum_le_sum
      intro z hz
      simpa only [imprimitiveLiftError] using
        norm_adjustedTwistedPsi_primitiveLift_le x q z hx
    _ = (∑ z : Σ k : ↥q.divisors,
          {ψ : DirichletCharacter ℂ k.1 // ψ.IsPrimitive},
            ‖adjustedTwistedPsi x z.2.1‖) +
        (Nat.totient q : ℝ) * imprimitiveLiftError x q := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, hcard]

/-- After the `1 / φ(q)` character-orthogonality weight, the cardinality of
the conductor partition cancels and leaves one imprimitive error. -/
theorem totientInv_mul_primitiveLiftAdjustedNormSum_le
    (x q : ℕ) [NeZero q] (hx : 2 ≤ x) :
    (Nat.totient q : ℝ)⁻¹ * primitiveLiftAdjustedNormSum x q ≤
      (Nat.totient q : ℝ)⁻¹ * primitiveSourceAdjustedNormSum x q +
        imprimitiveLiftError x q := by
  have htot : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    (Nat.totient q : ℝ)⁻¹ * primitiveLiftAdjustedNormSum x q ≤
        (Nat.totient q : ℝ)⁻¹ *
          (primitiveSourceAdjustedNormSum x q +
            (Nat.totient q : ℝ) * imprimitiveLiftError x q) :=
      mul_le_mul_of_nonneg_left
        (primitiveLiftAdjustedNormSum_le_source_add_error x q hx)
        (inv_nonneg.mpr htot.le)
    _ = (Nat.totient q : ℝ)⁻¹ * primitiveSourceAdjustedNormSum x q +
        imprimitiveLiftError x q := by
      field_simp

/-- The primitive-source part of the full character mean, before equal
conductors from different ambient moduli are regrouped. -/
noncomputable def primitiveSourceMean (x Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, (Nat.totient q : ℝ)⁻¹ *
    primitiveSourceAdjustedNormSum x q

/-- Exact divisor-incidence form of the primitive-source mean. -/
theorem primitiveSourceMean_eq_sum_divisors (x Q : ℕ) :
    primitiveSourceMean x Q =
      ∑ q ∈ Finset.Icc 1 Q,
        ∑ k ∈ q.divisors,
          (Nat.totient q : ℝ)⁻¹ *
            primitiveConductorAdjustedNormSum x k := by
  rw [primitiveSourceMean]
  apply Finset.sum_congr rfl
  intro q hq
  letI : NeZero q := ⟨by
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
  rw [primitiveSourceAdjustedNormSum_eq_sum_divisors', Finset.mul_sum]

/-- Total `1 / φ(q)` weight with which primitive conductor `k` occurs among
ambient moduli `q ≤ Q`. -/
noncomputable def primitiveConductorWeight (Q k : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if k ∈ q.divisors then (Nat.totient q : ℝ)⁻¹ else 0

/-- Reindex the conductor weight by the complementary factor `r`, so the
ambient modulus is `k*r`. -/
theorem primitiveConductorWeight_eq_sum_multiples
    (Q k : ℕ) (hk : 0 < k) :
    primitiveConductorWeight Q k =
      ∑ r ∈ Finset.Icc 1 (Q / k),
        (Nat.totient (k * r) : ℝ)⁻¹ := by
  rw [primitiveConductorWeight]
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        if k ∈ q.divisors then (Nat.totient q : ℝ)⁻¹ else 0) =
        ∑ q ∈ Finset.Icc 1 Q,
          if k ∣ q then (Nat.totient q : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq0 : q ≠ 0 :=
        Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
      simp [Nat.mem_divisors, hq0]
    _ = ∑ q ∈ (Finset.Icc 1 Q).filter (k ∣ ·),
          (Nat.totient q : ℝ)⁻¹ := by
      rw [Finset.sum_filter]
    _ = ∑ r ∈ Finset.Icc 1 (Q / k),
          (Nat.totient (k * r) : ℝ)⁻¹ := by
      refine Finset.sum_bij (fun q _ => q / k) ?_ ?_ ?_ ?_
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqIcc, hkq⟩
        rcases hkq with ⟨r, rfl⟩
        simp only [Finset.mem_Icc] at hqIcc ⊢
        have hrpos : 0 < r := by
          by_contra hr
          simp only [not_lt, nonpos_iff_eq_zero] at hr
          simp [hr] at hqIcc
        rw [Nat.mul_div_cancel_left _ hk]
        exact ⟨hrpos, (Nat.le_div_iff_mul_le hk).2 (by
          simpa [mul_comm] using hqIcc.2)⟩
      · intro q hq q' hq' heq
        rcases (Finset.mem_filter.mp hq).2 with ⟨r, hr⟩
        rcases (Finset.mem_filter.mp hq').2 with ⟨r', hr'⟩
        subst q
        subst q'
        simpa [Nat.mul_div_cancel_left _ hk] using congrArg (k * ·) heq
      · intro r hr
        have hrIcc := Finset.mem_Icc.mp hr
        refine ⟨k * r, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_Icc.mpr
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr
                (mul_ne_zero hk.ne' (by omega))
            · simpa [mul_comm] using
                (Nat.le_div_iff_mul_le hk).1 hrIcc.2
          · exact dvd_mul_right k r
        · simp [Nat.mul_div_cancel_left _ hk]
      · intro q hq
        rcases (Finset.mem_filter.mp hq).2 with ⟨r, rfl⟩
        rw [Nat.mul_div_cancel_left _ hk]

/-- Partial sum of reciprocal Euler totients. -/
noncomputable def reciprocalTotientSum (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R, (Nat.totient r : ℝ)⁻¹

/-- The elementary inequality `n ≤ φ(n) τ(n)`, obtained by comparing every
term in `n = ∑_{d∣n} φ(d)` with `φ(n)`. -/
theorem le_totient_mul_card_divisors
    {n : ℕ} (hn : 0 < n) :
    n ≤ Nat.totient n * n.divisors.card := by
  calc
    n = ∑ d ∈ n.divisors, Nat.totient d := (Nat.sum_totient n).symm
    _ ≤
        ∑ _d ∈ n.divisors, Nat.totient n := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hn)
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = Nat.totient n * n.divisors.card := by
      simp [mul_comm]

/-- Pointwise reciprocal-totient bound by the divisor function. -/
theorem inv_totient_le_card_divisors_mul_inv
    {n : ℕ} (hn : 0 < n) :
    (Nat.totient n : ℝ)⁻¹ ≤
      (n.divisors.card : ℝ) * (n : ℝ)⁻¹ := by
  have hφ : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmain := le_totient_mul_card_divisors hn
  have hcross :
      (1 : ℝ) * n ≤ (n.divisors.card : ℝ) * Nat.totient n := by
    exact_mod_cast (by simpa [mul_comm] using hmain)
  have hdiv :
      (1 : ℝ) / Nat.totient n ≤ n.divisors.card / n :=
    (div_le_div_iff₀ hφ hnR).2 hcross
  simpa only [one_div, div_eq_mul_inv, one_mul] using hdiv

/-- The divisor-weighted reciprocal sum is bounded by the square of the
harmonic sum. -/
theorem sum_card_divisors_mul_inv_le_harmonic_sq (R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R,
        (n.divisors.card : ℝ) * (n : ℝ)⁻¹) ≤
      (harmonic R : ℝ) ^ 2 := by
  let T := Finset.Icc 1 R
  have hexpand : ∀ n ∈ T,
      (∑ _d ∈ n.divisors, (n : ℝ)⁻¹) =
        ∑ d ∈ T, if d ∣ n then (n : ℝ)⁻¹ else 0 := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hsubset : n.divisors ⊆ T := by
      intro d hd
      have hddata := Nat.mem_divisors.mp hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddata.1 hnpos
      have hdn : d ≤ n := Nat.le_of_dvd hnpos hddata.1
      exact Finset.mem_Icc.mpr
        ⟨hdpos, hdn.trans (Finset.mem_Icc.mp hn).2⟩
    have hfilter : T.filter (· ∣ n) = n.divisors := by
      ext d
      simp only [Finset.mem_filter]
      constructor
      · intro hd
        exact Nat.mem_divisors.mpr ⟨hd.2, hnpos.ne'⟩
      · intro hd
        exact ⟨hsubset hd, Nat.dvd_of_mem_divisors hd⟩
    rw [← Finset.sum_filter, hfilter]
  calc
    (∑ n ∈ T, (n.divisors.card : ℝ) * (n : ℝ)⁻¹) =
        ∑ n ∈ T, ∑ _d ∈ n.divisors, (n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp
    _ = ∑ n ∈ T, ∑ d ∈ T,
          if d ∣ n then (n : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hexpand n hn
    _ = ∑ d ∈ T, ∑ n ∈ T,
          if d ∣ n then (n : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ T,
          ∑ n ∈ T.filter (d ∣ ·), (n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ T, (d : ℝ)⁻¹ * (harmonic R : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      rw [Chen.lemma6_sum_inv_multiples R d hdpos]
      exact mul_le_mul_of_nonneg_left
        (Chen.lemma6_sum_Icc_inv_le_harmonic (Nat.div_le_self R d))
        (by positivity)
    _ = (harmonic R : ℝ) ^ 2 := by
      rw [← Finset.sum_mul, Chen.lemma6_sum_Icc_inv_eq_harmonic]
      ring

/-- A completely elementary logarithmic-square majorant for reciprocal
totients. -/
theorem reciprocalTotientSum_le_harmonic_sq (R : ℕ) :
    reciprocalTotientSum R ≤ (harmonic R : ℝ) ^ 2 := by
  rw [reciprocalTotientSum]
  calc
    (∑ n ∈ Finset.Icc 1 R, (Nat.totient n : ℝ)⁻¹) ≤
        ∑ n ∈ Finset.Icc 1 R,
          (n.divisors.card : ℝ) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact inv_totient_le_card_divisors_mul_inv
        (Finset.mem_Icc.mp hn).1
    _ ≤ (harmonic R : ℝ) ^ 2 :=
      sum_card_divisors_mul_inv_le_harmonic_sq R

/-- Totient supermultiplicativity separates the primitive conductor from
the complementary ambient-modulus factor. -/
theorem primitiveConductorWeight_le_invTotient_mul_sum
    (Q k : ℕ) (hk : 0 < k) :
    primitiveConductorWeight Q k ≤
      (Nat.totient k : ℝ)⁻¹ * reciprocalTotientSum (Q / k) := by
  rw [primitiveConductorWeight_eq_sum_multiples Q k hk,
    reciprocalTotientSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hφk : (0 : ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.mpr hk
  have hφr : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.mpr hrpos
  have hφkr : (0 : ℝ) < Nat.totient (k * r) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hk hrpos)
  have hsuper :
      (Nat.totient k : ℝ) * Nat.totient r ≤ Nat.totient (k * r) := by
    exact_mod_cast Nat.totient_super_multiplicative k r
  calc
    (Nat.totient (k * r) : ℝ)⁻¹ ≤
        ((Nat.totient k : ℝ) * Nat.totient r)⁻¹ :=
      (inv_le_inv₀ hφkr (mul_pos hφk hφr)).2 hsuper
    _ = (Nat.totient k : ℝ)⁻¹ * (Nat.totient r : ℝ)⁻¹ := by
      rw [mul_inv]

/-- A uniform conductor-weight bound with only a harmless harmonic-square
loss. -/
theorem primitiveConductorWeight_le_invTotient_mul_harmonic_sq
    (Q k : ℕ) (hk : 0 < k) :
    primitiveConductorWeight Q k ≤
      (Nat.totient k : ℝ)⁻¹ * (harmonic Q : ℝ) ^ 2 := by
  have hHsmall :
      (harmonic (Q / k) : ℝ) ≤ (harmonic Q : ℝ) := by
    rw [← Chen.lemma6_sum_Icc_inv_eq_harmonic (Q / k)]
    exact Chen.lemma6_sum_Icc_inv_le_harmonic (Nat.div_le_self Q k)
  have hHsmall0 : 0 ≤ (harmonic (Q / k) : ℝ) := by
    rw [← Chen.lemma6_sum_Icc_inv_eq_harmonic]
    positivity
  have hHsq :
      (harmonic (Q / k) : ℝ) ^ 2 ≤ (harmonic Q : ℝ) ^ 2 :=
    pow_le_pow_left₀ hHsmall0 hHsmall 2
  calc
    primitiveConductorWeight Q k ≤
        (Nat.totient k : ℝ)⁻¹ * reciprocalTotientSum (Q / k) :=
      primitiveConductorWeight_le_invTotient_mul_sum Q k hk
    _ ≤ (Nat.totient k : ℝ)⁻¹ * (harmonic (Q / k) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (reciprocalTotientSum_le_harmonic_sq (Q / k)) (by positivity)
    _ ≤ (Nat.totient k : ℝ)⁻¹ * (harmonic Q : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hHsq (by positivity)

/-- Replace the primitive-character subtype by the usual indicator sum over
all characters at the same conductor. -/
theorem primitiveConductorAdjustedNormSum_eq_indicator_sum
    (x k : ℕ) :
    primitiveConductorAdjustedNormSum x k =
      ∑ χ : DirichletCharacter ℂ k,
        if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0 := by
  rw [primitiveConductorAdjustedNormSum]
  symm
  calc
    (∑ χ : DirichletCharacter ℂ k,
        if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) =
        ∑ χ ∈ (Finset.univ.filter
          (fun χ : DirichletCharacter ℂ k => χ.IsPrimitive)),
            ‖adjustedTwistedPsi x χ‖ := by
      rw [Finset.sum_filter]
    _ = ∑ ψ : {χ : DirichletCharacter ℂ k // χ.IsPrimitive},
          ‖adjustedTwistedPsi x ψ.1‖ := by
      exact Finset.sum_subtype _ (by simp)
        (fun χ => ‖adjustedTwistedPsi x χ‖)

/-- Primitive-character mean over all exact conductors up to `Q`. -/
noncomputable def primitiveConductorMean (x Q : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Q, (Nat.totient k : ℝ)⁻¹ *
    primitiveConductorAdjustedNormSum x k

theorem primitiveConductorMean_eq_primitiveAdjustedMean
    (x Q : ℕ) :
    primitiveConductorMean x Q = primitiveAdjustedMean x 0 Q := by
  rw [primitiveConductorMean, primitiveAdjustedMean]
  have hinterval : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [primitiveConductorAdjustedNormSum_eq_indicator_sum]

/-- Regroup the primitive-source mean exactly by primitive conductor. -/
theorem primitiveSourceMean_eq_sum_conductors (x Q : ℕ) :
    primitiveSourceMean x Q =
      ∑ k ∈ Finset.Icc 1 Q,
        primitiveConductorWeight Q k *
          primitiveConductorAdjustedNormSum x k := by
  rw [primitiveSourceMean_eq_sum_divisors]
  have hexpand : ∀ q ∈ Finset.Icc 1 Q,
      (∑ k ∈ q.divisors,
          (Nat.totient q : ℝ)⁻¹ *
            primitiveConductorAdjustedNormSum x k) =
        ∑ k ∈ Finset.Icc 1 Q,
          if k ∈ q.divisors then
            (Nat.totient q : ℝ)⁻¹ *
              primitiveConductorAdjustedNormSum x k
          else 0 := by
    intro q hq
    have hqdata := Finset.mem_Icc.mp hq
    have hsubset : q.divisors ⊆ Finset.Icc 1 Q := by
      intro k hk
      have hkdata := Nat.mem_divisors.mp hk
      have hkpos : 0 < k :=
        Nat.pos_of_dvd_of_pos hkdata.1 hqdata.1
      have hkq : k ≤ q := Nat.le_of_dvd hqdata.1 hkdata.1
      exact Finset.mem_Icc.mpr ⟨hkpos, hkq.trans hqdata.2⟩
    have hfilter :
        (Finset.Icc 1 Q).filter (fun k => k ∈ q.divisors) =
          q.divisors := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · exact fun hk => hk.2
      · exact fun hk => ⟨hsubset hk, hk⟩
    rw [← Finset.sum_filter, hfilter]
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        ∑ k ∈ q.divisors,
          (Nat.totient q : ℝ)⁻¹ *
            primitiveConductorAdjustedNormSum x k) =
        ∑ q ∈ Finset.Icc 1 Q,
          ∑ k ∈ Finset.Icc 1 Q,
            if k ∈ q.divisors then
              (Nat.totient q : ℝ)⁻¹ *
                primitiveConductorAdjustedNormSum x k
            else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hexpand q hq
    _ = ∑ k ∈ Finset.Icc 1 Q,
          ∑ q ∈ Finset.Icc 1 Q,
            if k ∈ q.divisors then
              (Nat.totient q : ℝ)⁻¹ *
                primitiveConductorAdjustedNormSum x k
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 1 Q,
        primitiveConductorWeight Q k *
          primitiveConductorAdjustedNormSum x k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [primitiveConductorWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hkdvd : k ∈ q.divisors <;> simp [hkdvd]

/-- The regrouped primitive-source mean loses at most two harmonic factors. -/
theorem primitiveSourceMean_le_harmonic_sq_mul_primitiveAdjustedMean
    (x Q : ℕ) :
    primitiveSourceMean x Q ≤
      (harmonic Q : ℝ) ^ 2 * primitiveAdjustedMean x 0 Q := by
  rw [primitiveSourceMean_eq_sum_conductors]
  calc
    (∑ k ∈ Finset.Icc 1 Q,
        primitiveConductorWeight Q k *
          primitiveConductorAdjustedNormSum x k) ≤
        ∑ k ∈ Finset.Icc 1 Q,
          ((Nat.totient k : ℝ)⁻¹ * (harmonic Q : ℝ) ^ 2) *
            primitiveConductorAdjustedNormSum x k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      exact mul_le_mul_of_nonneg_right
        (primitiveConductorWeight_le_invTotient_mul_harmonic_sq Q k hkpos)
        (by
          rw [primitiveConductorAdjustedNormSum]
          positivity)
    _ = (harmonic Q : ℝ) ^ 2 * primitiveConductorMean x Q := by
      rw [primitiveConductorMean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (harmonic Q : ℝ) ^ 2 * primitiveAdjustedMean x 0 Q := by
      rw [primitiveConductorMean_eq_primitiveAdjustedMean]

/-- Coarse total bound for all imprimitive-lifting errors up to `Q`. -/
theorem sum_imprimitiveLiftError_le
    (x Q : ℕ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q, imprimitiveLiftError x q) ≤
      2 * (Q : ℝ) * (Q + 1 : ℝ) *
        (Nat.log 2 x + 1 : ℝ) * Real.log x := by
  have hlog : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  let K : ℝ :=
    2 * (Q + 1 : ℝ) * (Nat.log 2 x + 1 : ℝ) * Real.log x
  have hterm : ∀ q ∈ Finset.Icc 1 Q, imprimitiveLiftError x q ≤ K := by
    intro q hq
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    dsimp only [K, imprimitiveLiftError]
    push_cast
    have hqQ' : (q : ℝ) + 1 ≤ (Q : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hqQ 1
    have hfac :
        0 ≤ 2 * ((Nat.log 2 x : ℝ) + 1) * Real.log x := by
      positivity
    calc
      2 * (((q : ℝ) + 1) * ((Nat.log 2 x : ℝ) + 1)) * Real.log x =
          ((q : ℝ) + 1) *
            (2 * ((Nat.log 2 x : ℝ) + 1) * Real.log x) := by ring
      _ ≤ ((Q : ℝ) + 1) *
            (2 * ((Nat.log 2 x : ℝ) + 1) * Real.log x) :=
        mul_le_mul_of_nonneg_right hqQ' hfac
      _ = 2 * ((Q : ℝ) + 1) *
            ((Nat.log 2 x : ℝ) + 1) * Real.log x := by ring
  calc
    (∑ q ∈ Finset.Icc 1 Q, imprimitiveLiftError x q) ≤
        ∑ _q ∈ Finset.Icc 1 Q, K := by
      exact Finset.sum_le_sum fun q hq => hterm q hq
    _ = (Finset.Icc 1 Q).card * K := by simp
    _ = 2 * (Q : ℝ) * (Q + 1 : ℝ) *
        (Nat.log 2 x + 1 : ℝ) * Real.log x := by
      rw [Nat.card_Icc]
      dsimp only [K]
      push_cast
      ring

/-- The whole character mean is bounded by the regroupable primitive-source
mean plus an explicit `O(Q² log x log₂ x)` lifting error. -/
theorem allCharacterMean_le_primitiveSourceMean_add_error
    (x Q : ℕ) (hx : 2 ≤ x) :
    allCharacterMean x Q ≤
      primitiveSourceMean x Q +
        2 * (Q : ℝ) * (Q + 1 : ℝ) *
          (Nat.log 2 x + 1 : ℝ) * Real.log x := by
  rw [allCharacterMean_eq_primitiveLifts, primitiveSourceMean]
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        (Nat.totient q : ℝ)⁻¹ * primitiveLiftAdjustedNormSum x q) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ((Nat.totient q : ℝ)⁻¹ * primitiveSourceAdjustedNormSum x q +
            imprimitiveLiftError x q) := by
      apply Finset.sum_le_sum
      intro q hq
      letI : NeZero q := ⟨by
        exact Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      exact totientInv_mul_primitiveLiftAdjustedNormSum_le x q hx
    _ = (∑ q ∈ Finset.Icc 1 Q,
          (Nat.totient q : ℝ)⁻¹ * primitiveSourceAdjustedNormSum x q) +
        ∑ q ∈ Finset.Icc 1 Q, imprimitiveLiftError x q := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ q ∈ Finset.Icc 1 Q,
          (Nat.totient q : ℝ)⁻¹ * primitiveSourceAdjustedNormSum x q) +
        2 * (Q : ℝ) * (Q + 1 : ℝ) *
          (Nat.log 2 x + 1 : ℝ) * Real.log x := by
      gcongr
      exact sum_imprimitiveLiftError_le x Q hx

/-- Progression errors after the complete imprimitive-character reduction. -/
theorem sum_maxProgressionError_le_primitiveSourceMean_add_error
    (x Q : ℕ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
      primitiveSourceMean x Q +
        2 * (Q : ℝ) * (Q + 1 : ℝ) *
          (Nat.log 2 x + 1 : ℝ) * Real.log x :=
  (sum_maxProgressionError_le_allCharacterMean x Q).trans
    (allCharacterMean_le_primitiveSourceMean_add_error x Q hx)

/-- The complete reduction from all ambient characters to the primitive mean
used by Vaughan's identity. -/
theorem allCharacterMean_le_harmonic_sq_mul_primitiveAdjustedMean_add_error
    (x Q : ℕ) (hx : 2 ≤ x) :
    allCharacterMean x Q ≤
      (harmonic Q : ℝ) ^ 2 * primitiveAdjustedMean x 0 Q +
        2 * (Q : ℝ) * (Q + 1 : ℝ) *
          (Nat.log 2 x + 1 : ℝ) * Real.log x := by
  calc
    allCharacterMean x Q ≤
        primitiveSourceMean x Q +
          2 * (Q : ℝ) * (Q + 1 : ℝ) *
            (Nat.log 2 x + 1 : ℝ) * Real.log x :=
      allCharacterMean_le_primitiveSourceMean_add_error x Q hx
    _ ≤ (harmonic Q : ℝ) ^ 2 * primitiveAdjustedMean x 0 Q +
          2 * (Q : ℝ) * (Q + 1 : ℝ) *
            (Nat.log 2 x + 1 : ℝ) * Real.log x := by
      gcongr
      exact primitiveSourceMean_le_harmonic_sq_mul_primitiveAdjustedMean x Q

/-- Progression errors reduced to the primitive Vaughan mean, with the full
imprimitive-lifting loss explicit. -/
theorem sum_maxProgressionError_le_harmonic_sq_mul_primitiveAdjustedMean_add_error
    (x Q : ℕ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
      (harmonic Q : ℝ) ^ 2 * primitiveAdjustedMean x 0 Q +
        2 * (Q : ℝ) * (Q + 1 : ℝ) *
          (Nat.log 2 x + 1 : ℝ) * Real.log x :=
  (sum_maxProgressionError_le_allCharacterMean x Q).trans
    (allCharacterMean_le_harmonic_sq_mul_primitiveAdjustedMean_add_error
      x Q hx)

end Chen.BombieriVinogradov
