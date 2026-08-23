/-
Unconditional validity of the contour shift in equation (17) of Lemma 6.

The two analytic limit hypotheses of
`lemma6BContour_primComplexSum_verticalIntegral_eq` — vanishing of the
horizontal rectangle edges and integrability of the `B` integrand on the
shifted line `β = 1/2 + 1/log x` — are discharged here.  Everything reduces
to the polynomial growth of `L'` in the critical strip
(`norm_deriv_LFunction_le_of_mem_strip`, proved in `StripGrowth.lean` via
Pólya–Vinogradov and partial summation) combined with the super-polynomial
decay of Chen's smoothing kernel.
-/
import ChenTheorem.Lemma6.ContourShift
import ChenTheorem.Lemma6.StripGrowth
import ChenTheorem.Lemma6.Integration

open Real Set MeasureTheory Filter Topology
open scoped Classical

namespace Chen

/-- Pointwise bound for one summand of the pair Dirichlet polynomial,
depending only on `re s`. -/
theorem norm_pairBlock_summand_le {x m k d : ℕ} (χ : DirichletCharacter ℂ d)
    {q : ℕ × ℕ} (hq : q ∈ lemma6AdmissiblePairBlock x m k) (s : ℂ) :
    ‖χ (q.1 * q.2 : ZMod d) /
        (((q.1 * q.2 : ℕ) : ℂ) ^ s *
          (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ ≤
      ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
        |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  obtain ⟨hq1, hq2⟩ := primes_of_mem_lemma6AdmissiblePairBlock hq
  have hqq : 0 < q.1 * q.2 := Nat.mul_pos hq1.pos hq2.pos
  have hqqR : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) := by positivity
  rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hqq,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖χ (q.1 * q.2 : ZMod d)‖ /
          (((q.1 * q.2 : ℕ) : ℝ) ^ s.re *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|) ≤
        1 / (((q.1 * q.2 : ℕ) : ℝ) ^ s.re *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|) :=
      div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one _ _)
        (by positivity)
    _ = ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
      rw [div_eq_mul_inv, one_mul, mul_inv, ← Real.rpow_neg hqqR.le]

/-- The pair Dirichlet polynomial is bounded by a real sum depending only
on `re s`. -/
theorem norm_lemma6PairBlockPolynomial_le_rpow_sum {x m k d : ℕ}
    (χ : DirichletCharacter ℂ d) (s : ℂ) :
    ‖lemma6PairBlockPolynomial x m k s χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairBlock x m k,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  unfold lemma6PairBlockPolynomial lemma6PairDirichletPolynomial
  calc
    ‖∑ q ∈ lemma6AdmissiblePairBlock x m k,
          χ (q.1 * q.2 : ZMod d) /
            (((q.1 * q.2 : ℕ) : ℂ) ^ s *
              (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ ≤
        ∑ q ∈ lemma6AdmissiblePairBlock x m k,
          ‖χ (q.1 * q.2 : ZMod d) /
            (((q.1 * q.2 : ℕ) : ℂ) ^ s *
              (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ lemma6AdmissiblePairBlock x m k,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact norm_pairBlock_summand_le χ hq s

/-- The real pair-polynomial majorant is antitone in the real part. -/
theorem pairBlock_rpow_sum_antitone {x m k : ℕ} {σ₀ σ₁ : ℝ} (h : σ₀ ≤ σ₁) :
    (∑ q ∈ lemma6AdmissiblePairBlock x m k,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-σ₁) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) ≤
      ∑ q ∈ lemma6AdmissiblePairBlock x m k,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-σ₀) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hq1, hq2⟩ := primes_of_mem_lemma6AdmissiblePairBlock hq
  have hqq : (1 : ℝ) ≤ ((q.1 * q.2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_pos hq1.pos hq2.pos).ne'
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hqq (by linarith)) (by positivity)

/-- On any vertical line with nonnegative real part, the truncated Möbius
mollifier is bounded by its length. -/
theorem norm_lemma6MollifierAt_le_card {q H : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖lemma6MollifierAt H s χ‖ ≤ (H : ℝ) := by
  unfold lemma6MollifierAt
  calc
    ‖∑ n ∈ Finset.Icc 1 H,
        (ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ ≤
        ∑ n ∈ Finset.Icc 1 H,
          ‖(ArithmeticFunction.moebius n : ℂ) * χ n / (n : ℂ) ^ s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : 0 < n := hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hchi : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have hden : (1 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.one_le_rpow hnR hs
      rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
      calc
        ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖χ (n : ZMod q)‖ /
              (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by
          apply div_le_div_of_nonneg_right _
            (Real.rpow_nonneg (by positivity) _)
          nlinarith [norm_nonneg (ArithmeticFunction.moebius n : ℂ),
            norm_nonneg (χ (n : ZMod q))]
        _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos (by positivity) _)]
          exact hden
    _ = (H : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp

/-- The elementary comparison
`(1 + |ν|) / (1 + ν⁴) ≤ 4 / (1 + ν²)`. -/
theorem one_add_abs_div_one_add_pow_four_le (ν : ℝ) :
    (1 + |ν|) / (1 + ν ^ 4) ≤ 4 / (1 + ν ^ 2) := by
  have h1 : (0 : ℝ) < 1 + ν ^ 4 := by positivity
  have h2 : (0 : ℝ) < 1 + ν ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  set t : ℝ := |ν| with ht
  have ht0 : (0 : ℝ) ≤ t := abs_nonneg ν
  have hν2 : ν ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  have hν4 : ν ^ 4 = t ^ 4 := by
    have hsq : ν ^ 4 = (ν ^ 2) ^ 2 := by ring
    rw [hsq, hν2]
    ring
  rw [hν2, hν4]
  have key : 1 + t + t ^ 2 + t ^ 3 ≤ 4 * (1 + t ^ 4) := by
    rcases le_or_gt t 1 with h | h
    · have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
      have ht3 : t ^ 3 ≤ 1 := by
        calc t ^ 3 = t * t ^ 2 := by ring
          _ ≤ 1 * 1 := mul_le_mul h ht2 (sq_nonneg t) zero_lt_one.le
          _ = 1 := one_mul 1
      nlinarith [ht2, ht3, ht0, pow_nonneg ht0 4]
    · have h1t : (1 : ℝ) ≤ t := h.le
      have ht3 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ (by linarith)
      have he1 : t ≤ t ^ 4 := by
        calc t = t * 1 := by ring
          _ ≤ t * t ^ 3 := by gcongr
          _ = t ^ 4 := by ring
      have he2 : t ^ 2 ≤ t ^ 4 := by
        calc t ^ 2 = t ^ 2 * 1 := by ring
          _ ≤ t ^ 2 * t ^ 2 := by gcongr; nlinarith
          _ = t ^ 4 := by ring
      have he3 : t ^ 3 ≤ t ^ 4 := by
        calc t ^ 3 = t ^ 3 * 1 := by ring
          _ ≤ t ^ 3 * t := by gcongr
          _ = t ^ 4 := by ring
      nlinarith [he1, he2, he3, ht0]
  nlinarith [key, sq_nonneg t]

/-- The shifted `B` integrand is integrable on Chen's `β`-line,
unconditionally.  The growth of `L'` in the strip is linear in `‖s‖`
(`norm_deriv_LFunction_le_of_mem_strip`), while the smoothing kernel decays
quarticly. -/
theorem integrable_lemma6BContourIntegrand_beta
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    Integrable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)) := by
  have hLpos : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  set β : ℝ := 1 / 2 + 1 / Real.log (x : ℝ) with hβdef
  have hβge : (1 : ℝ) / 2 ≤ β := by
    rw [hβdef]
    have hnn : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hβle : β ≤ 1 := by
    rw [hβdef]
    have h2 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  set Cpair : ℝ := ∑ q ∈ lemma6AdmissiblePairBlock x m k,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-β) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hCpair
  have hCpair0 : 0 ≤ Cpair := by
    rw [hCpair]
    positivity
  set CL : ℝ := 144 * Real.sqrt d * Real.log (2 * d) with hCL
  have hCL0 : 0 ≤ CL := by
    rw [hCL]
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
    have h2 : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  set K : ℝ := (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
    (2 * Real.log (x : ℝ) ^ 5) * Cpair * CL * (H : ℝ) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  have hpoint : ∀ ν : ℝ,
      ‖lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)‖ ≤
        4 * K * (1 + ν ^ 2)⁻¹ := by
    intro ν
    have hmain := norm_lemma6BContourIntegrand_beta_le hx hxlog m k H χ ν
    have hre : (lemma6BetaPoint x ν).re = β := by
      rw [hβdef]
      exact lemma6BetaPoint_re x ν
    have hpair : ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ ≤
        Cpair := by
      calc
        ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ ≤
            ∑ q ∈ lemma6AdmissiblePairBlock x m k,
              ((q.1 * q.2 : ℕ) : ℝ) ^ (-(lemma6BetaPoint x ν).re) *
                |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ :=
          norm_lemma6PairBlockPolynomial_le_rpow_sum χ _
        _ = Cpair := by
          rw [hCpair, hre]
    have hLbound : ‖deriv (DirichletCharacter.LFunction χ)
        (lemma6BetaPoint x ν)‖ ≤ CL * (1 + |ν|) := by
      have hstrip := norm_deriv_LFunction_le_of_mem_strip hχ hd
        (by linarith : (1 : ℝ) / 2 ≤ (lemma6BetaPoint x ν).re)
        (by linarith : (lemma6BetaPoint x ν).re ≤ 2)
      have hnorm : ‖lemma6BetaPoint x ν‖ ≤ 1 + |ν| := by
        calc
          ‖lemma6BetaPoint x ν‖ ≤ |(lemma6BetaPoint x ν).re| +
              |(lemma6BetaPoint x ν).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = β + |ν| := by
            rw [hre, lemma6BetaPoint_im, abs_of_nonneg (by linarith)]
          _ ≤ 1 + |ν| := by linarith
      calc
        ‖deriv (DirichletCharacter.LFunction χ) (lemma6BetaPoint x ν)‖ ≤
            144 * Real.sqrt d * Real.log (2 * d) *
              ‖lemma6BetaPoint x ν‖ := hstrip
        _ = CL * ‖lemma6BetaPoint x ν‖ := by rw [hCL]
        _ ≤ CL * (1 + |ν|) :=
          mul_le_mul_of_nonneg_left hnorm hCL0
    have hmoll : ‖lemma6MollifierAt H (lemma6BetaPoint x ν) χ‖ ≤ (H : ℝ) :=
      norm_lemma6MollifierAt_le_card χ (by linarith)
    have hbase0 : 0 ≤ (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
        (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) := by positivity
    have e1 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
          ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ ≤
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair :=
      mul_le_mul_of_nonneg_left hpair hbase0
    have e2 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
          ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6BetaPoint x ν)‖ ≤
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair *
          (CL * (1 + |ν|)) :=
      mul_le_mul e1 hLbound (norm_nonneg _) (mul_nonneg hbase0 hCpair0)
    have e3 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) *
          ‖lemma6PairBlockPolynomial x m k (lemma6BetaPoint x ν) χ‖ *
          ‖deriv (DirichletCharacter.LFunction χ) (lemma6BetaPoint x ν)‖ *
          ‖lemma6MollifierAt H (lemma6BetaPoint x ν) χ‖ ≤
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair *
          (CL * (1 + |ν|)) * (H : ℝ) :=
      mul_le_mul e2 hmoll (norm_nonneg _)
        (mul_nonneg (mul_nonneg hbase0 hCpair0)
          (mul_nonneg hCL0 (by positivity)))
    have h1 := hmain.trans e3
    have h2 : (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          (2 * Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4)) * Cpair *
          (CL * (1 + |ν|)) * (H : ℝ) =
        K * ((1 + |ν|) / (1 + ν ^ 4)) := by
      rw [hK]
      ring
    have h3 : K * ((1 + |ν|) / (1 + ν ^ 4)) ≤ 4 * K * (1 + ν ^ 2)⁻¹ := by
      have hcmp := one_add_abs_div_one_add_pow_four_le ν
      calc
        K * ((1 + |ν|) / (1 + ν ^ 4)) ≤ K * (4 / (1 + ν ^ 2)) :=
          mul_le_mul_of_nonneg_left hcmp hK0
        _ = 4 * K * (1 + ν ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          ring
    exact h1.trans (h2.le.trans h3)
  have hmeas : AEStronglyMeasurable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)) := by
    have hbeta : Continuous (lemma6BetaPoint x) := by
      unfold lemma6BetaPoint
      fun_prop
    have hrange : ∀ ν : ℝ, lemma6BetaPoint x ν ∈
        {s : ℂ | 0 < s.re} := by
      intro ν
      have hre : (lemma6BetaPoint x ν).re = β := by
        rw [hβdef]
        exact lemma6BetaPoint_re x ν
      rw [Set.mem_setOf_eq, hre]
      linarith
    exact ((differentiableOn_lemma6BContourIntegrand hd hx m k H
      hχ).continuousOn.comp_continuous hbeta hrange).aestronglyMeasurable
  apply ((integrable_inv_one_add_sq.const_mul (4 * K))).mono' hmeas
  filter_upwards with ν
  exact hpoint ν

/-- The horizontal edges of the rectangle in equation (17) vanish,
unconditionally, for primitive characters of modulus at least two.  The
pointwise decay combines the linear strip growth of `L'` with the quartic
decay of Chen's smoothing kernel. -/
theorem lemma6BHorizontalEdgesVanish_primitive
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    Lemma6BHorizontalEdgesVanish x m k H χ := by
  apply lemma6BHorizontalEdgesVanish_of_pointwiseDecay
  have hLpos : 0 < Real.log (x : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x by omega)
  set β₀ : ℝ := 1 / 2 + 1 / Real.log (x : ℝ) with hβ₀
  set α₀ : ℝ := 1 + 1 / Real.log (x : ℝ) with hα₀
  have hα₀le : α₀ ≤ 2 := by
    rw [hα₀]
    have h1 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 := by
      simpa using h1
    linarith
  have hβ₀ge : (1 : ℝ) / 2 ≤ β₀ := by
    rw [hβ₀]
    have hnn : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  set a : ℝ := lemma6SmoothingScale (x : ℝ) with ha
  have hapos : 0 < a := by
    rw [ha]
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hLpos _
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  set Cpair : ℝ := ∑ q ∈ lemma6AdmissiblePairBlock x m k,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-β₀) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hCpair
  have hCpair0 : 0 ≤ Cpair := by rw [hCpair]; positivity
  set CL : ℝ := 144 * Real.sqrt d * Real.log (2 * d) with hCL
  have hCL0 : 0 ≤ CL := by
    rw [hCL]
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
    have h2 : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  set K₁ : ℝ := Real.exp 1 * (x : ℝ) * 2 * Cpair * CL * (H : ℝ) with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨fun T : ℝ => K₁ * (α₀ + |T|) * ((1 + (T / a) ^ 2) ^ 2)⁻¹,
    ?_, ?_⟩
  · -- Tendsto g atTop 0
    have htend : Tendsto (fun T : ℝ => 2 * K₁ * a ^ 4 * (T⁻¹) ^ 3)
        atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.pow 3).const_mul (2 * K₁ * a ^ 4)
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      htend
    · filter_upwards with T
      positivity
    · filter_upwards [eventually_ge_atTop 2] with T hT
      have hTpos : (0 : ℝ) < T := by linarith
      have habs : |T| = T := abs_of_nonneg hTpos.le
      rw [habs]
      have hstep1 : α₀ + T ≤ 2 * T := by linarith
      have hstep2 : ((1 + (T / a) ^ 2) ^ 2)⁻¹ ≤ a ^ 4 / T ^ 4 := by
        have h1 : (T / a) ^ 2 ≤ 1 + (T / a) ^ 2 := by
          linarith [sq_nonneg (T / a)]
        have h2 : ((T / a) ^ 2) ^ 2 ≤ (1 + (T / a) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) h1 2
        have h3 : ((T / a) ^ 2) ^ 2 = T ^ 4 / a ^ 4 := by
          rw [div_pow, div_pow]
          ring
        rw [h3] at h2
        have h4 : (0 : ℝ) < (1 + (T / a) ^ 2) ^ 2 := by positivity
        have h5 : (0 : ℝ) < T ^ 4 / a ^ 4 := by positivity
        calc
          ((1 + (T / a) ^ 2) ^ 2)⁻¹ ≤ (T ^ 4 / a ^ 4)⁻¹ := by
            rw [inv_le_inv₀ h4 h5]
            exact h2
          _ = a ^ 4 / T ^ 4 := inv_div _ _
      calc
        K₁ * (α₀ + T) * ((1 + (T / a) ^ 2) ^ 2)⁻¹ ≤
            K₁ * (2 * T) * (a ^ 4 / T ^ 4) := by
          apply mul_le_mul _ hstep2 (by positivity)
            (mul_nonneg hK₁0 (by linarith))
          exact mul_le_mul_of_nonneg_left hstep1 hK₁0
        _ = 2 * K₁ * a ^ 4 * (T⁻¹) ^ 3 := by
          field_simp [hTpos.ne']
  · -- pointwise bound
    intro T σ hσ
    have hσlo : (1 : ℝ) / 2 ≤ σ := hβ₀ge.trans hσ.1
    have hσhi : σ ≤ 2 := hσ.2.trans hα₀le
    have hσpos : (0 : ℝ) < σ := by linarith
    have hσinv : σ⁻¹ ≤ 2 := by
      have h22 : (2 : ℝ) = (1 / 2)⁻¹ := by norm_num
      rw [h22, inv_le_inv₀ hσpos (by norm_num)]
      linarith
    -- the pointwise bound, uniform in the imaginary displacement `τ`
    have hbound : ∀ τ : ℝ,
        ‖lemma6BContourIntegrand x m k H χ
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          K₁ * (α₀ + |τ|) * ((1 + (τ / a) ^ 2) ^ 2)⁻¹ := by
      intro τ
      have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by
        simp [Complex.add_re, Complex.mul_re]
      have him : ((σ : ℂ) + (τ : ℂ) * Complex.I).im = τ := by
        simp [Complex.add_im, Complex.mul_im]
      have hkernel : ‖lemma6SmoothingMellinKernel (x : ℝ)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹ := by
        have hk := norm_lemma6SmoothingMellinKernel_le_quartic
          (x := (x : ℝ)) hapos hn hσpos τ
        exact hk.trans (mul_le_mul_of_nonneg_right hσinv (by positivity))
      have hxpow : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          Real.exp 1 * (x : ℝ) := by
        have hxpos : (0 : ℝ) < x := by positivity
        have hxne : (x : ℝ) ≠ 1 := by
          exact_mod_cast (show x ≠ 1 by omega)
        change ‖((x : ℝ) : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          Real.exp 1 * (x : ℝ)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hre]
        calc
          (x : ℝ) ^ σ ≤ (x : ℝ) ^ α₀ :=
            Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast (show 1 ≤ x by omega)) hσ.2
          _ = Real.exp 1 * (x : ℝ) := by
            rw [hα₀, Real.rpow_add hxpos, Real.rpow_one,
              show (1 : ℝ) / Real.log (x : ℝ) = (Real.log (x : ℝ))⁻¹ from
                one_div _, Real.rpow_inv_log hxpos hxne]
            ring
      have hpair : ‖lemma6PairBlockPolynomial x m k
            ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤ Cpair := by
        calc
          ‖lemma6PairBlockPolynomial x m k
                ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
              ∑ q ∈ lemma6AdmissiblePairBlock x m k,
                ((q.1 * q.2 : ℕ) : ℝ) ^ (-(((σ : ℂ) + (τ : ℂ) * Complex.I).re)) *
                  |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ :=
            norm_lemma6PairBlockPolynomial_le_rpow_sum χ _
          _ ≤ Cpair := by
            rw [hCpair]
            apply pairBlock_rpow_sum_antitone
            rw [hre]
            exact hσ.1
      have hLbound : ‖deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          CL * (α₀ + |τ|) := by
        have hstrip := norm_deriv_LFunction_le_of_mem_strip hχ hd
          (by linarith : (1 : ℝ) / 2 ≤
            ((σ : ℂ) + (τ : ℂ) * Complex.I).re)
          (by linarith : ((σ : ℂ) + (τ : ℂ) * Complex.I).re ≤ 2)
        have hnorm : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤ α₀ + |τ| := by
          calc
            ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤
                |((σ : ℂ) + (τ : ℂ) * Complex.I).re| +
                  |((σ : ℂ) + (τ : ℂ) * Complex.I).im| :=
              Complex.norm_le_abs_re_add_abs_im _
            _ = σ + |τ| := by
              rw [hre, him, abs_of_nonneg hσpos.le]
            _ ≤ α₀ + |τ| := by linarith [hσ.2]
        calc
          ‖deriv (DirichletCharacter.LFunction χ)
                ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
              144 * Real.sqrt d * Real.log (2 * d) *
                ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ := hstrip
          _ = CL * ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ := by rw [hCL]
          _ ≤ CL * (α₀ + |τ|) := mul_le_mul_of_nonneg_left hnorm hCL0
      have hmoll : ‖lemma6MollifierAt H ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
          (H : ℝ) :=
        norm_lemma6MollifierAt_le_card χ (by linarith)
      unfold lemma6BContourIntegrand
      simp only [norm_neg, norm_mul]
      have e1 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) :=
        mul_le_mul hxpow hkernel (norm_nonneg _) (by positivity)
      have e2 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairBlockPolynomial x m k
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair :=
        mul_le_mul e1 hpair (norm_nonneg _)
          (mul_nonneg (by positivity) (by positivity))
      have e3 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairBlockPolynomial x m k
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ *
            ‖deriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair * (CL * (α₀ + |τ|)) :=
        mul_le_mul e2 hLbound (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hCpair0)
      have e4 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairBlockPolynomial x m k
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ *
            ‖deriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6MollifierAt H ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair * (CL * (α₀ + |τ|)) * (H : ℝ) :=
        mul_le_mul e3 hmoll (norm_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
            (by positivity)) hCpair0)
            (mul_nonneg hCL0 (by positivity)))
      apply e4.trans
      apply le_of_eq
      rw [hK₁]
      ring
    constructor
    · have hrewrite : (σ : ℂ) - (T : ℂ) * Complex.I =
          (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
        rw [Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
      rw [hrewrite]
      have h := hbound (-T)
      rwa [abs_neg, neg_div, neg_sq] at h
    · exact hbound T

end Chen
