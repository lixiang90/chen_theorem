/-
The zero-free-region contour shift and the character-level estimate of
equation (21) in Lemma 6, completing the last unproved step of Lemma 6
beyond the isolated zero-free-region interface.

Unlike the `A + B` split used in equations (16)–(20), equation (21) moves
the *unsplit* logarithmic-derivative integrand
`-x^s · K(s) · P(s, χ) · (L'/L)(s, χ)` from Chen's line `α = 1 + 1/log x`
to the line `γ = 1 - 1/sqrt(log x)` inside the classical zero-free region.
The single analytic input is the interface `PrimitiveZeroFreeRegion` of
`ZeroFreeRegion.lean` (nonvanishing together with the companion `L'/L`
bound); both factors are needed because the kernel and the pair polynomial
alone do not supply the required decay on the `α`-line.

Pipeline (all proved below except the single documented input):

* `lemma6Equation21Point` — Chen's shifted contour point,
  `1 - 1/sqrt(log x) + i ν`;
* elementary pair estimates: the product of a Chen prime pair is at most
  `x^(2/3)`, hence `log (x / (p₁p₂)) ≥ (1/3) log x`;
* `norm_kernel_le_half_power` — the exact decay of the rational Mellin
  kernel, `‖K(σ + iν)‖ ≤ σ⁻¹ · (1 + (ν/a)²)^(-(n+1)/2)`, together with
  the weaker quadratic form `σ⁻¹ · (1 + (ν/a)²)⁻²` used downstream;
* `eq21LogDerivIntegrand` — the unsplit integrand, holomorphic on the
  zero-free region intersected with `1/2 ≤ re s`;
* Cauchy–Goursat on finite rectangles
  (`eq21LogDeriv_finite_rectangle`), uniform decay of the horizontal edges
  from the super-polynomial kernel decay
  (`eq21LogDeriv_horizontalEdgesVanish`), and integrability of the
  integrand on both vertical lines;
* equality of the two vertical integrals
  (`eq21LogDeriv_verticalIntegral_eq`) and the explicit bound of the
  shifted integral by `16 · x^γ · P_γ · c₂ (log l + 1)² · a⁴ · π`;
* the assembly `eq21_characterIntegral_bound`, bounding the `α`-line
  character integral by `C · (log x)^90` times the shifted prime-pair
  power sum, matching `Lemma6Equation21CharacterBound` of `Core.lean`.
-/
import ChenTheorem.Lemma6.ZeroFreeRegion
import ChenTheorem.Lemma6.ContourShift
import ChenTheorem.Lemma6.BIntegrability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Real Set MeasureTheory Filter Topology
open scoped Classical Interval

namespace Chen

/-! ### The shifted contour point of equation (21) -/

/-- The vertical point `1 - 1/sqrt(log x) + i nu` of equation (21). -/
noncomputable def lemma6Equation21Point (x : ℕ) (ν : ℝ) : ℂ :=
  ((1 - 1 / Real.sqrt (Real.log x) : ℝ) : ℂ) + (ν : ℂ) * Complex.I

@[simp]
theorem lemma6Equation21Point_re (x : ℕ) (ν : ℝ) :
    (lemma6Equation21Point x ν).re = 1 - 1 / Real.sqrt (Real.log x) := by
  change
    (1 - 1 / Real.sqrt (Real.log (x : ℝ))) +
        ((ν * 0 - 0 * 1 : ℝ)) =
      1 - 1 / Real.sqrt (Real.log (x : ℝ))
  ring

@[simp]
theorem lemma6Equation21Point_im (x : ℕ) (ν : ℝ) :
    (lemma6Equation21Point x ν).im = ν := by
  change (0 : ℝ) + (ν * 1 + 0 * 0) = ν
  ring

/-! ### Elementary estimates -/

/-- The elementary inequality `(1 + t²)^{1/2} ≤ 1 + t` for `t ≥ 0`. -/
theorem sqrt_one_add_sq_le_one_add {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (1 + t ^ 2) ≤ 1 + t := by
  have hsq : (1 + t ^ 2) ≤ (1 + t) ^ 2 := by
    nlinarith [sq_nonneg t]
  calc
    Real.sqrt (1 + t ^ 2) ≤ Real.sqrt ((1 + t) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = |1 + t| := by
        rw [Real.sqrt_sq_eq_abs]
    _ = 1 + t := abs_of_nonneg (by linarith)

/-- The product of a Chen prime pair is at most `x^(2/3)`.  Local copy of
`chenPairs_product_le_rpow` from `Core.lean`, which this file cannot
import. -/
theorem eq21_chenPairs_product_le_rpow {x : ℕ} (hx : 1 ≤ x) {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) :
    ((q.1 * q.2 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := by
  have hqdata := (Finset.mem_filter.mp hq).2
  obtain ⟨hprime1, hprime2, hlo1, hup1, hlo2, hup2⟩ := hqdata
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hp1pos : (0 : ℝ) < q.1 := by exact_mod_cast hprime1.pos
  have hsqhalf : (((x : ℝ) / q.1) ^ ((1 : ℝ) / 2)) ^ 2 = x / q.1 := by
    have h1 : (((x : ℝ) / q.1) ^ ((1 : ℝ) / 2)) ^ 2 =
        ((x : ℝ) / q.1) ^ (((1 : ℝ) / 2) * 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    rw [h1, show ((1 : ℝ) / 2) * 2 = 1 by norm_num, Real.rpow_one]
  have hp2sq : (q.2 : ℝ) ^ 2 ≤ x / q.1 := by
    calc (q.2 : ℝ) ^ 2 ≤ (((x : ℝ) / q.1) ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hup2 2
      _ = x / q.1 := hsqhalf
  have hsq : ((q.1 * q.2 : ℕ) : ℝ) ^ 2 ≤ (x : ℝ) ^ ((4 : ℝ) / 3) := by
    have h3 : ((q.1 * q.2 : ℕ) : ℝ) ^ 2 = (q.1 : ℝ) ^ 2 * (q.2 : ℝ) ^ 2 := by
      rw [Nat.cast_mul]
      ring
    have h4 : (q.1 : ℝ) ^ 2 * (q.2 : ℝ) ^ 2 ≤ (q.1 : ℝ) ^ 2 * (x / q.1) :=
      mul_le_mul_of_nonneg_left hp2sq (by positivity)
    have h5 : (q.1 : ℝ) ^ 2 * (x / q.1) = q.1 * x := by
      field_simp [hp1pos.ne']
    have hup1x : (q.1 : ℝ) * x ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * x :=
      mul_le_mul_of_nonneg_right hup1 hxpos.le
    have h6 : (x : ℝ) ^ ((1 : ℝ) / 3) * x = (x : ℝ) ^ ((4 : ℝ) / 3) := by
      have e : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ (1 : ℝ) =
          (x : ℝ) ^ ((4 : ℝ) / 3) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        norm_num
      rwa [Real.rpow_one] at e
    calc ((q.1 * q.2 : ℕ) : ℝ) ^ 2 = (q.1 : ℝ) ^ 2 * (q.2 : ℝ) ^ 2 := h3
      _ ≤ q.1 * x := h4.trans_eq h5
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * x := hup1x
      _ = (x : ℝ) ^ ((4 : ℝ) / 3) := h6
  have hbase : (0 : ℝ) ≤ ((q.1 * q.2 : ℕ) : ℝ) := by positivity
  calc ((q.1 * q.2 : ℕ) : ℝ) = Real.sqrt (((q.1 * q.2 : ℕ) : ℝ) ^ 2) :=
      (Real.sqrt_sq hbase).symm
    _ ≤ Real.sqrt ((x : ℝ) ^ ((4 : ℝ) / 3)) := Real.sqrt_le_sqrt hsq
    _ = (x : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
      congr 1
      norm_num

/-- For a Chen prime pair, `log (x / (p₁p₂)) ≥ (1/3) log x`, since
`p₁p₂ ≤ x^(2/3)`. -/
theorem eq21_chenPairs_log_div_ge {x : ℕ} (hx : 2 ≤ x) {q : ℕ × ℕ}
    (hq : q ∈ chenPairs x) :
    (1 / 3) * Real.log (x : ℝ) ≤
      Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) := by
  have hqdata := (Finset.mem_filter.mp hq).2
  have hp1pos : (0 : ℝ) < (q.1 : ℝ) := by exact_mod_cast hqdata.1.pos
  have hp2pos : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hqdata.2.1.pos
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hprod := eq21_chenPairs_product_le_rpow (by omega : 1 ≤ x) hq
  have hqpos : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hqdata.1.pos hqdata.2.1.pos
  have hr23 : (0 : ℝ) < (x : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hxpos _
  have hdiv : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ) := by
    have h1 : (x : ℝ) / ((x : ℝ) ^ ((2 : ℝ) / 3)) ≤
        (x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_left hxpos.le hqpos hprod
    have h2 : (x : ℝ) / ((x : ℝ) ^ ((2 : ℝ) / 3)) = (x : ℝ) ^ ((1 : ℝ) / 3) := by
      have h3 : (x : ℝ) = (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_add hxpos, show (1 : ℝ) / 3 + 2 / 3 = 1 by norm_num,
          Real.rpow_one]
      exact (div_eq_iff hr23.ne').mpr h3
    rwa [h2] at h1
  calc (1 / 3) * Real.log (x : ℝ) = Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) :=
      (Real.log_rpow hxpos _).symm
    _ ≤ Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) :=
      Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hdiv

/-- Membership in the admissible pair set exposes the two primality
hypotheses. -/
theorem eq21_primes_of_mem_admissiblePairs {x m : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ lemma6AdmissiblePairs x m) :
    q.1.Prime ∧ q.2.Prime := by
  have hqchen : q ∈ chenPairs x := (Finset.mem_filter.mp hq).1
  have hqdata := (Finset.mem_filter.mp hqchen).2
  exact ⟨hqdata.1, hqdata.2.1⟩

/-- Pointwise bound for one summand of the admissible pair Dirichlet
polynomial, depending only on `re s`. -/
theorem norm_eq21Pair_summand_le {x m l : ℕ} (χ : DirichletCharacter ℂ l)
    {q : ℕ × ℕ} (hq : q ∈ lemma6AdmissiblePairs x m) (s : ℂ) :
    ‖χ (q.1 * q.2 : ZMod l) /
        (((q.1 * q.2 : ℕ) : ℂ) ^ s *
          (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ ≤
      ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
        |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  obtain ⟨hq1, hq2⟩ := eq21_primes_of_mem_admissiblePairs hq
  have hqq : 0 < q.1 * q.2 := Nat.mul_pos hq1.pos hq2.pos
  have hqqR : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) := by positivity
  rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hqq,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖χ (q.1 * q.2 : ZMod l)‖ /
          (((q.1 * q.2 : ℕ) : ℝ) ^ s.re *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|) ≤
        1 / (((q.1 * q.2 : ℕ) : ℝ) ^ s.re *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|) :=
      div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one _ _)
        (by positivity)
    _ = ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
      rw [div_eq_mul_inv, one_mul, mul_inv, ← Real.rpow_neg hqqR.le]

/-- The admissible pair Dirichlet polynomial is bounded by a real sum
depending only on `re s`. -/
theorem norm_eq21PairPoly_le {x m l : ℕ}
    (χ : DirichletCharacter ℂ l) (s : ℂ) :
    ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m) s χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  unfold lemma6PairDirichletPolynomial
  calc
    ‖∑ q ∈ lemma6AdmissiblePairs x m,
          χ (q.1 * q.2 : ZMod l) /
            (((q.1 * q.2 : ℕ) : ℂ) ^ s *
              (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ ≤
        ∑ q ∈ lemma6AdmissiblePairs x m,
          ‖χ (q.1 * q.2 : ZMod l) /
            (((q.1 * q.2 : ℕ) : ℂ) ^ s *
              (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-s.re) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact norm_eq21Pair_summand_le χ hq s

/-- The real pair-polynomial majorant is antitone in the real part. -/
theorem eq21Pair_rpow_sum_antitone {x m : ℕ} {σ₀ σ₁ : ℝ} (h : σ₀ ≤ σ₁) :
    (∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-σ₁) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) ≤
      ∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-σ₀) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hq1, hq2⟩ := eq21_primes_of_mem_admissiblePairs hq
  have hqq : (1 : ℝ) ≤ ((q.1 * q.2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_pos hq1.pos hq2.pos).ne'
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hqq (by linarith)) (by positivity)

/-- The admissible prime-pair polynomial is an entire Dirichlet polynomial
in its complex argument.  The possible zero of the fixed logarithmic
denominator is harmless because Lean's division is totalized. -/
theorem differentiable_eq21PairPoly {l : ℕ} (x m : ℕ)
    (χ : DirichletCharacter ℂ l) :
    Differentiable ℂ
      (fun s => lemma6PairDirichletPolynomial x
        (lemma6AdmissiblePairs x m) s χ) := by
  unfold lemma6PairDirichletPolynomial
  simp only [Nat.cast_mul]
  apply Differentiable.fun_sum
  intro q hq
  obtain ⟨hp1, hp2⟩ := eq21_primes_of_mem_admissiblePairs hq
  have hn0 : (q.1 * q.2 : ℂ) ≠ 0 := by
    norm_cast
    exact Nat.mul_ne_zero hp1.ne_zero hp2.ne_zero
  letI : NeZero (q.1 * q.2 : ℂ) := ⟨hn0⟩
  have hpow : Differentiable ℂ (fun s : ℂ => (q.1 * q.2 : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  by_cases hlog : Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) = 0
  · have hlogC :
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ) = 0 := by
      exact_mod_cast hlog
    simp only [hlogC, mul_zero, div_zero]
    exact differentiable_const _
  · have hden : Differentiable ℂ (fun s : ℂ =>
        (q.1 * q.2 : ℂ) ^ s *
          (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ)) := by
      fun_prop
    have hdeninv : Differentiable ℂ (fun s : ℂ =>
        ((q.1 * q.2 : ℂ) ^ s *
          (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ))⁻¹) :=
      hden.inv (fun s => mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))
        (Complex.ofReal_ne_zero.mpr hlog))
    have hmul := hdeninv.const_mul
      (χ (q.1 : ZMod l) * χ (q.2 : ZMod l))
    simpa only [div_eq_mul_inv, Nat.cast_mul, map_mul] using hmul

/-! ### Kernel decay -/

/-- **Exact decay of the smoothing kernel at large height.**  The norm of
the rational Mellin kernel decays like `(1 + (ν/a)²)^(-(n+1)/2)` — the
square root of the squared-modulus decay.  This is genuinely weaker than a
fourth-power bound: `(1+(τ/a)²)^(-(n+1)/2)` is *larger* than
`(1+(τ/a)²)^(-2·(n+1))` whenever `τ/a ≥ √3`. -/
theorem norm_kernel_le_half_power {x σ : ℝ}
    (ha : 0 < lemma6SmoothingScale x)
    (_hn : 1 ≤ lemma6SmoothingOrder x) (hσ : 0 < σ) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel x
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      σ⁻¹ * ((1 + (ν / lemma6SmoothingScale x) ^ 2) ^
        (((lemma6SmoothingOrder x + 1 : ℕ) : ℝ) / 2))⁻¹ := by
  let a : ℝ := lemma6SmoothingScale x
  let n : ℕ := lemma6SmoothingOrder x
  let s : ℂ := (σ : ℂ) + (ν : ℂ) * Complex.I
  let z : ℂ := 1 + s / (a : ℂ)
  have ha' : 0 < a := ha
  have hsre : s.re = σ := by
    dsimp only [s]
    simp
  have hsim : s.im = ν := by
    dsimp only [s]
    simp
  have hsNorm : σ ≤ ‖s‖ := by
    rw [← hsre]
    exact Complex.abs_re_le_norm s |>.trans' (le_abs_self _)
  have hzre : z.re = 1 + σ / a := by
    dsimp only [z]
    rw [Complex.add_re, Complex.one_re, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hsre, hsim,
      Complex.normSq_ofReal]
    field_simp
    ring
  have hzim : z.im = ν / a := by
    dsimp only [z]
    rw [Complex.add_im, Complex.one_im, Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hsre, hsim, mul_zero,
      zero_add, Complex.normSq_ofReal]
    field_simp
    ring
  have hzsq : ‖z‖ ^ 2 = (1 + σ / a) ^ 2 + (ν / a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hzOne : 1 ≤ ‖z‖ := by
    have hz0 := norm_nonneg z
    have hσa : 0 ≤ σ / a := (div_pos hσ ha').le
    rw [← sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1) hz0, hzsq]
    nlinarith [sq_nonneg (ν / a)]
  have hbase : 1 + (ν / a) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hzsq]
    have hσa : 0 ≤ σ / a := (div_pos hσ ha').le
    nlinarith [sq_nonneg (1 + σ / a - 1)]
  have hsqrt : Real.sqrt (1 + (ν / a) ^ 2) ≤ ‖z‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg z, hbase⟩
  have hu : (0 : ℝ) ≤ 1 + (ν / a) ^ 2 := by positivity
  have hkey : (Real.sqrt (1 + (ν / a) ^ 2)) ^ (n + 1) =
      (1 + (ν / a) ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + (ν / a) ^ 2) ^ ((1 : ℝ) / 2)),
      ← Real.rpow_mul hu]
    congr 1
    ring
  have hden : (1 + (ν / a) ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2) ≤ ‖z‖ ^ (n + 1) :=
    hkey ▸ pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt (n + 1)
  have hdenPos : 0 < (1 + (ν / a) ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hsInv : ‖s‖⁻¹ ≤ σ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hσ hsNorm
  have hzInv : (‖z‖ ^ (n + 1))⁻¹ ≤
      ((1 + (ν / a) ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hdenPos hden
  change ‖s⁻¹ * (z ^ (n + 1))⁻¹‖ ≤
    σ⁻¹ * ((1 + (ν / a) ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2))⁻¹
  rw [norm_mul, norm_inv, norm_inv, norm_pow]
  exact mul_le_mul hsInv hzInv
    (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))
    (inv_nonneg.mpr hσ.le)

/-- The quadratic weakening of the half-power kernel decay, valid as soon
as the smoothing order is at least three. -/
theorem norm_kernel_le_quadratic_inv {x σ : ℝ}
    (ha : 0 < lemma6SmoothingScale x)
    (hn : 3 ≤ lemma6SmoothingOrder x) (hσ : 0 < σ) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel x
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      σ⁻¹ * ((1 + (ν / lemma6SmoothingScale x) ^ 2) ^ 2)⁻¹ := by
  have h1 := norm_kernel_le_half_power ha (by omega) hσ ν
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hσ.le))
  have hu1 : (1 : ℝ) ≤ 1 + (ν / lemma6SmoothingScale x) ^ 2 := by
    nlinarith [sq_nonneg (ν / lemma6SmoothingScale x)]
  have hexp : (2 : ℝ) ≤
      (((lemma6SmoothingOrder x + 1 : ℕ) : ℝ)) / 2 := by
    have h4 : (4 : ℝ) ≤ ((lemma6SmoothingOrder x + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 4 ≤ lemma6SmoothingOrder x + 1 by omega)
    linarith
  have hpow : (1 + (ν / lemma6SmoothingScale x) ^ 2) ^ 2 ≤
      (1 + (ν / lemma6SmoothingScale x) ^ 2) ^
        (((lemma6SmoothingOrder x + 1 : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_two (1 + (ν / lemma6SmoothingScale x) ^ 2)]
    exact Real.rpow_le_rpow_of_exponent_le hu1 hexp
  have hp2 : (0 : ℝ) < (1 + (ν / lemma6SmoothingScale x) ^ 2) ^ 2 := by
    positivity
  simpa only [one_div] using one_div_le_one_div_of_le hp2 hpow

/-- Domination of the quadratic kernel decay by the integrable envelope
`(1 + ν²)⁻¹`, at the price of the factor `a⁴`. -/
theorem eq21_quarticInv_le_a4_sq {a : ℝ} (ha : 1 ≤ a) (ν : ℝ) :
    ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤ a ^ 4 * ((1 + ν ^ 2) ^ 2)⁻¹ := by
  have ha0 : (0 : ℝ) < a := by linarith
  have ha1sq : (1 : ℝ) ≤ a ^ 2 := one_le_pow₀ ha
  have hsq : (1 + ν ^ 2) ^ 2 ≤ (a ^ 2 + ν ^ 2) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg ν]
  have heq : (1 + (ν / a) ^ 2) ^ 2 = (a ^ 2 + ν ^ 2) ^ 2 / a ^ 4 := by
    have h1 : (a ^ 2 + ν ^ 2) / a ^ 2 = 1 + (ν / a) ^ 2 := by
      rw [add_div, div_self (pow_pos ha0 2).ne', div_pow]
    rw [← h1, div_pow, show (a ^ 2) ^ 2 = a ^ 4 by ring]
  have ha2pos : (0 : ℝ) < (a ^ 2 + ν ^ 2) ^ 2 := by
    have hle : (1 : ℝ) ≤ a ^ 2 + ν ^ 2 := by nlinarith [sq_nonneg ν]
    exact pow_pos (by linarith) 2
  have hu2pos : (0 : ℝ) < (1 + ν ^ 2) ^ 2 := by
    positivity
  rw [heq, inv_div]
  have h2 : a ^ 4 / (a ^ 2 + ν ^ 2) ^ 2 ≤ a ^ 4 * ((1 + ν ^ 2) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ ha2pos hu2pos).mpr hsq)
      (pow_nonneg ha0.le 4)
  exact h2

/-- Domination of the quadratic kernel decay by `a⁴ · (1 + ν²)⁻¹`. -/
theorem eq21_quarticInv_le {a : ℝ} (ha : 1 ≤ a) (ν : ℝ) :
    ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤ a ^ 4 * (1 + ν ^ 2)⁻¹ := by
  have h1 := eq21_quarticInv_le_a4_sq ha ν
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hu : (0 : ℝ) < 1 + ν ^ 2 := by positivity
  have hs : (1 : ℝ) ≤ 1 + ν ^ 2 := by nlinarith [sq_nonneg ν]
  rw [pow_two, mul_inv]
  calc (1 + ν ^ 2)⁻¹ * (1 + ν ^ 2)⁻¹ ≤ 1 * (1 + ν ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hs)
        (inv_nonneg.mpr hu.le)
    _ = (1 + ν ^ 2)⁻¹ := one_mul _

/-- The kernel decay absorbs one factor `4 + |ν|` coming from the
logarithmic-derivative companion bound, still dominated by the integrable
envelope `(1 + ν²)⁻¹`. -/
theorem eq21_four_add_abs_mul_quarticInv_le {a : ℝ} (ha : 1 ≤ a) (ν : ℝ) :
    (4 + |ν|) * ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤ 8 * a ^ 4 * (1 + ν ^ 2)⁻¹ := by
  have hq := eq21_quarticInv_le_a4_sq ha ν
  have hν : (4 : ℝ) + |ν| ≤ 8 * (1 + ν ^ 2) := by
    nlinarith [sq_nonneg (|ν| - 1), abs_nonneg ν, sq_abs ν]
  have hu : (0 : ℝ) < 1 + ν ^ 2 := by positivity
  calc (4 + |ν|) * ((1 + (ν / a) ^ 2) ^ 2)⁻¹
      ≤ (4 + |ν|) * (a ^ 4 * ((1 + ν ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ (8 * (1 + ν ^ 2)) * (a ^ 4 * ((1 + ν ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right hν (by positivity)
    _ = 8 * a ^ 4 * (1 + ν ^ 2)⁻¹ := by
        have h3 : (1 + ν ^ 2) * ((1 + ν ^ 2) ^ 2)⁻¹ = (1 + ν ^ 2)⁻¹ := by
          rw [pow_two (1 + ν ^ 2), mul_inv, ← mul_assoc,
            mul_inv_cancel₀ hu.ne', one_mul]
        calc (8 * (1 + ν ^ 2)) * (a ^ 4 * ((1 + ν ^ 2) ^ 2)⁻¹)
            = 8 * a ^ 4 * ((1 + ν ^ 2) * ((1 + ν ^ 2) ^ 2)⁻¹) := by ring
          _ = 8 * a ^ 4 * (1 + ν ^ 2)⁻¹ := by rw [h3]

/-! ### The unsplit logarithmic-derivative integrand -/

/-- The unsplit logarithmic-derivative integrand of equation (21): exactly
the body of `lemma6Equation21CharacterIntegral` of `Core.lean`, before
moving the contour. -/
noncomputable def eq21LogDerivIntegrand (x m : ℕ) {l : ℕ} [NeZero l]
    (χ : DirichletCharacter ℂ l) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s * lemma6SmoothingMellinKernel (x : ℝ) s) *
      lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m) s χ *
      (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s))

/-- On Chen's `α`-line, the horizontal power has constant modulus `e·x`. -/
theorem norm_nat_cpow_eq21AlphaPoint {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ = Real.exp 1 * (x : ℝ) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxne : (x : ℝ) ≠ 1 := by
    exact_mod_cast (show x ≠ 1 by omega)
  change ‖((x : ℝ) : ℂ) ^ lemma6AlphaPoint x ν‖ = Real.exp 1 * (x : ℝ)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, lemma6AlphaPoint_re,
    Real.rpow_add hxpos, Real.rpow_one,
    show (1 : ℝ) / Real.log (x : ℝ) = (Real.log (x : ℝ))⁻¹ from one_div _,
    Real.rpow_inv_log hxpos hxne]
  ring

/-- The content of `PrimitiveZeroFreeRegion` at fixed constants `c₁, c₂`:
nonvanishing of primitive `L`-functions together with the standard
companion bound on the logarithmic derivative in the region
`re s ≥ 1 - c₁ l^{-1/300}`. -/
def Eq21ZeroFreeBound (c₁ c₂ : ℝ) : Prop :=
  ∀ (l : ℕ) (_ : NeZero l) (χ : DirichletCharacter ℂ l),
    χ.IsPrimitive → ∀ s : ℂ,
      (1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300)) ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
          ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ ≤
            c₂ * (Real.log l + 1) ^ 2 * Real.log (2 + ‖s‖)

/-- Holomorphy of the unsplit integrand on the zero-free region
intersected with `1/2 ≤ re s`.  The extra `1/2 ≤ re s` condition keeps the
smoothing kernel holomorphic; the region condition keeps `L` nonvanishing,
so the quotient `L'/L` is holomorphic. -/
theorem differentiableOn_eq21LogDerivIntegrand
    {c₁ c₂ : ℝ} (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) :
    DifferentiableOn ℂ (eq21LogDerivIntegrand x m χ)
      {s : ℂ | (1 : ℝ) / 2 ≤ s.re ∧
          1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤ s.re} := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 by omega)
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  have hk : DifferentiableOn ℂ (lemma6SmoothingMellinKernel (x : ℝ))
      {s : ℂ | (1 : ℝ) / 2 ≤ s.re ∧
        1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤ s.re} :=
    (differentiableOn_lemma6SmoothingMellinKernel
      (x := (x : ℝ)) (by exact_mod_cast (show 1 < x by omega))).mono
        (fun s hs => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs.1)
  have hP : DifferentiableOn ℂ
      (fun s => lemma6PairDirichletPolynomial x
        (lemma6AdmissiblePairs x m) s χ)
      {s : ℂ | (1 : ℝ) / 2 ≤ s.re ∧
        1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤ s.re} :=
    (differentiable_eq21PairPoly x m χ).differentiableOn
  have hLq : DifferentiableOn ℂ
      (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
      {s : ℂ | (1 : ℝ) / 2 ≤ s.re ∧
        1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤ s.re} := by
    intro s hs
    exact ((primitiveCharacter_differentiable_LFunction_deriv hl
        hχ).differentiableAt.div
      (primitiveCharacter_differentiable_LFunction hl hχ).differentiableAt
      (hzfb l inferInstance χ hχ s hs.2).1).differentiableWithinAt
  unfold eq21LogDerivIntegrand
  exact (((hxpow.differentiableOn.mul hk).mul hP).mul hLq).neg

/-- Cauchy–Goursat on the rectangle with vertical sides
`1 - 1/sqrt(log x)` and `alpha = 1 + 1/log x`, heights `[-T, T]`. -/
theorem eq21LogDeriv_finite_rectangle
    {c₁ c₂ : ℝ} (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    (hγregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) (T : ℝ) :
    let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
    let α : ℝ := 1 + 1 / Real.log (x : ℝ)
    let F : ℂ → ℂ := eq21LogDerivIntegrand x m χ
    (∫ σ : ℝ in γ..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ σ : ℝ in γ..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((α : ℂ) + (ν : ℂ) * Complex.I)) -
      Complex.I • (∫ ν : ℝ in (-T)..T,
        F ((γ : ℂ) + (ν : ℂ) * Complex.I)) = 0 := by
  dsimp only
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let z : ℂ := (γ : ℂ) + (-T : ℂ) * Complex.I
  let w : ℂ := (α : ℂ) + (T : ℂ) * Complex.I
  let F : ℂ → ℂ := eq21LogDerivIntegrand x m χ
  have hlog : 0 < Real.log (x : ℝ) := by linarith
  have hγα : γ ≤ α := by
    dsimp only [γ, α]
    have h1 : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := div_nonneg zero_le_one hlog.le
    linarith
  have hzre : z.re = γ := by
    dsimp only [z]
    simp
  have hwre : w.re = α := by
    dsimp only [w]
    simp
  have hzim : z.im = -T := by
    dsimp only [z]
    simp
  have hwim : w.im = T := by
    dsimp only [w]
    simp
  have hdiff : DifferentiableOn ℂ F
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    apply (differentiableOn_eq21LogDerivIntegrand (m := m) hzfb hl hx hχ).mono
    intro s hs
    change (1 : ℝ) / 2 ≤ s.re ∧
      1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤ s.re
    have hre := hs.1
    rw [hzre, hwre, uIcc_of_le hγα] at hre
    exact ⟨hγpos.trans hre.1, hγregion.trans hre.1⟩
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  rw [hzre, hwre, hzim, hwim] at hrect
  dsimp only [F] at hrect
  simpa only [γ, α, sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hrect

/-- The growth condition made precise: the two horizontal edge integrals
of the equation-(21) contour tend to zero. -/
def Eq21LogDerivHorizontalEdgesVanish {l : ℕ} [NeZero l] (x m : ℕ)
    (χ : DirichletCharacter ℂ l) : Prop :=
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := eq21LogDerivIntegrand x m χ
  Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α, F ((σ : ℂ) - (T : ℂ) * Complex.I))
      atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α, F ((σ : ℂ) + (T : ℂ) * Complex.I))
      atTop (𝓝 0)

/-- Uniform pointwise decay across the compact horizontal segment implies
the vanishing of the two horizontal edge integrals. -/
theorem eq21LogDerivHorizontalEdgesVanish_of_pointwiseDecay
    {x m l : ℕ} [NeZero l] {χ : DirichletCharacter ℂ l}
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hdecay : ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ T σ : ℝ, σ ∈ Icc (1 - 1 / Real.sqrt (Real.log (x : ℝ)))
          (1 + 1 / Real.log (x : ℝ)) →
        ‖eq21LogDerivIntegrand x m χ
            ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤ g T ∧
        ‖eq21LogDerivIntegrand x m χ
            ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ g T) :
    Eq21LogDerivHorizontalEdgesVanish x m χ := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := eq21LogDerivIntegrand x m χ
  rcases hdecay with ⟨g, hg, hbound⟩
  have hlog : 0 < Real.log (x : ℝ) := by linarith
  have hγα : γ ≤ α := by
    dsimp only [γ, α]
    have h1 : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := div_nonneg zero_le_one hlog.le
    linarith
  have hwidth : Tendsto (fun T : ℝ => g T * |α - γ|)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hg.mul_const |α - γ|
  have hbotBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in γ..α,
          F ((σ : ℂ) - (T : ℂ) * Complex.I)‖ ≤
        g T * |α - γ| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc γ α := by
      rw [← uIcc_of_le hγα]
      exact uIoc_subset_uIcc hσ
    exact (hbound T σ (by simpa only [γ, α] using hσ')).1
  have htopBound : ∀ T : ℝ,
      ‖∫ σ : ℝ in γ..α,
          F ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        g T * |α - γ| := by
    intro T
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc γ α := by
      rw [← uIcc_of_le hγα]
      exact uIoc_subset_uIcc hσ
    exact (hbound T σ (by simpa only [γ, α] using hσ')).2
  have hbot : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α,
          F ((σ : ℂ) - (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      hbotBound hwidth
  have htop : Tendsto (fun T : ℝ =>
      ∫ σ : ℝ in γ..α,
          F ((σ : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun T => norm_nonneg _)
      htopBound hwidth
  simpa only [Eq21LogDerivHorizontalEdgesVanish, γ, α, F] using
    And.intro hbot htop

/-- The horizontal edges of the equation-(21) rectangle vanish: the
companion `L'/L` bound of the zero-free region contributes only a
logarithmic factor, while the smoothing kernel decays super-polynomially
in the height. -/
theorem eq21LogDeriv_horizontalEdgesVanish
    {c₁ c₂ : ℝ} (hc₂ : 0 < c₂) (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (_hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    (hγregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) :
    Eq21LogDerivHorizontalEdgesVanish x m χ := by
  apply eq21LogDerivHorizontalEdgesVanish_of_pointwiseDecay hxlog
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  set γ₀ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ)) with hγ₀
  set α₀ : ℝ := 1 + 1 / Real.log (x : ℝ) with hα₀
  have hα₀le : α₀ ≤ 2 := by
    rw [hα₀]
    have h1 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 := by
      simpa using h1
    linarith
  have hγ₀ge : (1 : ℝ) / 2 ≤ γ₀ := hγpos
  set a : ℝ := lemma6SmoothingScale (x : ℝ) with ha
  have hapos : 0 < a := by
    rw [ha]
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hLpos _
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  set Cpair : ℝ := ∑ q ∈ lemma6AdmissiblePairs x m,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ₀) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hCpair
  have hCpair0 : 0 ≤ Cpair := by rw [hCpair]; positivity
  set CL : ℝ := c₂ * (Real.log (l : ℝ) + 1) ^ 2 with hCL
  have hCL0 : 0 ≤ CL := by
    rw [hCL]
    exact mul_nonneg hc₂.le (sq_nonneg _)
  set K₁ : ℝ := Real.exp 1 * (x : ℝ) * 2 * Cpair * CL with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨fun T : ℝ => K₁ * (4 + |T|) * ((1 + (T / a) ^ 2) ^ 2)⁻¹,
    ?_, ?_⟩
  · -- Tendsto g atTop 0
    have htend : Tendsto (fun T : ℝ => 5 * K₁ * a ^ 4 * (T⁻¹) ^ 3)
        atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.pow 3).const_mul (5 * K₁ * a ^ 4)
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      htend
    · filter_upwards with T
      positivity
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hTpos : (0 : ℝ) < T := by linarith
      have habs : |T| = T := abs_of_nonneg hTpos.le
      rw [habs]
      have hstep1 : 4 + T ≤ 5 * T := by linarith
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
        K₁ * (4 + T) * ((1 + (T / a) ^ 2) ^ 2)⁻¹ ≤
            K₁ * (5 * T) * (a ^ 4 / T ^ 4) := by
          apply mul_le_mul _ hstep2 (by positivity)
            (mul_nonneg hK₁0 (by linarith))
          exact mul_le_mul_of_nonneg_left hstep1 hK₁0
        _ = 5 * K₁ * a ^ 4 * (T⁻¹) ^ 3 := by
          field_simp [hTpos.ne']
  · -- pointwise bound
    intro T σ hσ
    have hσlo : (1 : ℝ) / 2 ≤ σ := hγ₀ge.trans hσ.1
    have hσhi : σ ≤ 2 := hσ.2.trans hα₀le
    have hσpos : (0 : ℝ) < σ := by linarith
    have hσinv : σ⁻¹ ≤ 2 := by
      have h22 : (2 : ℝ) = (1 / 2)⁻¹ := by norm_num
      rw [h22, inv_le_inv₀ hσpos (by norm_num)]
      linarith
    -- the pointwise bound, uniform in the imaginary displacement `τ`
    have hbound : ∀ τ : ℝ,
        ‖eq21LogDerivIntegrand x m χ
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          K₁ * (4 + |τ|) * ((1 + (τ / a) ^ 2) ^ 2)⁻¹ := by
      intro τ
      have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by
        simp [Complex.add_re, Complex.mul_re]
      have him : ((σ : ℂ) + (τ : ℂ) * Complex.I).im = τ := by
        simp [Complex.add_im, Complex.mul_im]
      have hkernel : ‖lemma6SmoothingMellinKernel (x : ℝ)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹ := by
        have hk := norm_kernel_le_quadratic_inv
          (x := (x : ℝ)) hapos hn hσpos τ
        exact hk.trans (mul_le_mul_of_nonneg_right hσinv (by positivity))
      have hxpow : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          Real.exp 1 * (x : ℝ) := by
        have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
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
      have hpair : ‖lemma6PairDirichletPolynomial x
            (lemma6AdmissiblePairs x m)
            ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤ Cpair := by
        calc
          ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
                ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
              ∑ q ∈ lemma6AdmissiblePairs x m,
                ((q.1 * q.2 : ℕ) : ℝ) ^
                    (-(((σ : ℂ) + (τ : ℂ) * Complex.I).re)) *
                  |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ :=
            norm_eq21PairPoly_le (x := x) (m := m) χ _
          _ ≤ Cpair := by
            rw [hCpair]
            apply eq21Pair_rpow_sum_antitone
            rw [hre]
            exact hσ.1
      have hLbound : ‖deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (τ : ℂ) * Complex.I) /
            DirichletCharacter.LFunction χ
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          CL * (4 + |τ|) := by
        have hregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
            ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by
          rw [hre]
          exact hγregion.trans hσ.1
        obtain ⟨hne, hb⟩ := hzfb l inferInstance χ hχ _ hregion
        have hnorm : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤ α₀ + |τ| := by
          calc
            ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤
                |((σ : ℂ) + (τ : ℂ) * Complex.I).re| +
                  |((σ : ℂ) + (τ : ℂ) * Complex.I).im| :=
              Complex.norm_le_abs_re_add_abs_im _
            _ = σ + |τ| := by
              rw [hre, him, abs_of_nonneg hσpos.le]
            _ ≤ α₀ + |τ| := by linarith [hσ.2]
        have hlog2 : Real.log
            (2 + ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖) ≤ 4 + |τ| := by
          have h1 := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < 2 + ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ by
              positivity)
          have h3 : α₀ ≤ 2 := hα₀le
          linarith [abs_nonneg τ]
        calc
          ‖deriv (DirichletCharacter.LFunction χ)
                ((σ : ℂ) + (τ : ℂ) * Complex.I) /
              DirichletCharacter.LFunction χ
                ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
              c₂ * (Real.log (l : ℝ) + 1) ^ 2 *
                Real.log (2 + ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖) := hb
          _ = CL * Real.log (2 + ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖) := by
              rw [hCL]
          _ ≤ CL * (4 + |τ|) := mul_le_mul_of_nonneg_left hlog2 hCL0
      unfold eq21LogDerivIntegrand
      simp only [norm_neg, norm_mul]
      have e1 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) :=
        mul_le_mul hxpow hkernel (norm_nonneg _) (by positivity)
      have e2 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair :=
        mul_le_mul e1 hpair (norm_nonneg _)
          (mul_nonneg (by positivity) (by positivity))
      have e3 : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6SmoothingMellinKernel (x : ℝ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
            ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
              ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ *
            ‖deriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I) /
              DirichletCharacter.LFunction χ
                ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
          (Real.exp 1 * (x : ℝ)) * (2 * ((1 + (τ / a) ^ 2) ^ 2)⁻¹) *
            Cpair * (CL * (4 + |τ|)) :=
        mul_le_mul e2 hLbound (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hCpair0)
      apply e3.trans
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

/-- Pointwise bound for the unsplit integrand on the shifted line
`γ = 1 - 1/sqrt(log x)`: the modulus of `x^s` is exactly `x^γ`, the kernel
contributes the quadratic decay, the pair polynomial its `γ`-majorant, and
`L'/L` the zero-free-region companion bound. -/
theorem norm_eq21LogDerivIntegrand_eq21Point_le
    {c₁ c₂ : ℝ} (hc₂ : 0 < c₂) (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (hx : 2 ≤ x) (hxlog : 3 ≤ Real.log (x : ℝ))
    (ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    (hγregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) (ν : ℝ) :
    ‖eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ ≤
      (16 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (c₂ * (Real.log (l : ℝ) + 1) ^ 2) *
          (lemma6SmoothingScale (x : ℝ)) ^ 4) * (1 + ν ^ 2)⁻¹ := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have ha0 : (0 : ℝ) < lemma6SmoothingScale (x : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hn3 : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hγ0 : (0 : ℝ) < 1 - 1 / Real.sqrt (Real.log (x : ℝ)) := by linarith
  have hPγ0 : (0 : ℝ) ≤ ∑ q ∈ lemma6AdmissiblePairs x m,
      ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
        |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by positivity
  have hCL0 : (0 : ℝ) ≤ c₂ * (Real.log (l : ℝ) + 1) ^ 2 :=
    mul_nonneg hc₂.le (sq_nonneg _)
  have hq0 : (0 : ℝ) ≤
      ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by positivity
  have e_x : ‖(x : ℂ) ^ lemma6Equation21Point x ν‖ =
      (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) := by
    change ‖((x : ℝ) : ℂ) ^ lemma6Equation21Point x ν‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, lemma6Equation21Point_re]
  have e_K : ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6Equation21Point x ν)‖ ≤
      2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
    have hk := norm_kernel_le_quadratic_inv
      (x := (x : ℝ)) (σ := 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
      ha0 hn3 hγ0 ν
    have hγinv : (1 - 1 / Real.sqrt (Real.log (x : ℝ)))⁻¹ ≤ 2 := by
      have h := (inv_le_inv₀ hγ0 (by norm_num : (0 : ℝ) < 1 / 2)).mpr hγpos
      rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at h
    calc ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6Equation21Point x ν)‖
        ≤ (1 - 1 / Real.sqrt (Real.log (x : ℝ)))⁻¹ *
            ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := hk
      _ ≤ 2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hγinv hq0
  have e_P : ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
        (lemma6Equation21Point x ν) χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
    have h := norm_eq21PairPoly_le (x := x) (m := m) χ (lemma6Equation21Point x ν)
    rwa [lemma6Equation21Point_re] at h
  have e_L : ‖deriv (DirichletCharacter.LFunction χ)
        (lemma6Equation21Point x ν) /
        DirichletCharacter.LFunction χ (lemma6Equation21Point x ν)‖ ≤
      (c₂ * (Real.log (l : ℝ) + 1) ^ 2) * (4 + |ν|) := by
    have hregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
        (lemma6Equation21Point x ν).re := by
      rw [lemma6Equation21Point_re]
      exact hγregion
    obtain ⟨hne, hb⟩ := hzfb l inferInstance χ hχ _ hregion
    have hnorm : ‖lemma6Equation21Point x ν‖ ≤ 1 + |ν| := by
      have hγ1 : 1 - 1 / Real.sqrt (Real.log (x : ℝ)) ≤ 1 := by
        have hnn : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by
          positivity
        linarith
      calc ‖lemma6Equation21Point x ν‖ ≤
            |(lemma6Equation21Point x ν).re| +
              |(lemma6Equation21Point x ν).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = (1 - 1 / Real.sqrt (Real.log (x : ℝ))) + |ν| := by
          rw [lemma6Equation21Point_re, lemma6Equation21Point_im,
            abs_of_nonneg hγ0.le]
        _ ≤ 1 + |ν| := by linarith
    have hlog : Real.log (2 + ‖lemma6Equation21Point x ν‖) ≤ 4 + |ν| := by
      have h1 := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 2 + ‖lemma6Equation21Point x ν‖ by positivity)
      linarith [abs_nonneg ν]
    calc ‖deriv (DirichletCharacter.LFunction χ)
            (lemma6Equation21Point x ν) /
          DirichletCharacter.LFunction χ (lemma6Equation21Point x ν)‖ ≤
          c₂ * (Real.log (l : ℝ) + 1) ^ 2 *
            Real.log (2 + ‖lemma6Equation21Point x ν‖) := hb
      _ ≤ c₂ * (Real.log (l : ℝ) + 1) ^ 2 * (4 + |ν|) :=
          mul_le_mul_of_nonneg_left hlog hCL0
  unfold eq21LogDerivIntegrand
  simp only [norm_neg, norm_mul]
  have e1 : ‖(x : ℂ) ^ lemma6Equation21Point x ν‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6Equation21Point x ν)‖ ≤
      (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) :=
    mul_le_mul e_x.le e_K (norm_nonneg _) (Real.rpow_nonneg hxpos.le _)
  have e12nn : (0 : ℝ) ≤ (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
      (2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) := by
    positivity
  have e2 : ‖(x : ℂ) ^ lemma6Equation21Point x ν‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6Equation21Point x ν)‖ *
        ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
          (lemma6Equation21Point x ν) χ‖ ≤
      (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) :=
    mul_le_mul e1 e_P (norm_nonneg _) e12nn
  have e123nn : (0 : ℝ) ≤ (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
      (2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) *
      (∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) :=
    mul_nonneg e12nn hPγ0
  have e3 : ‖(x : ℂ) ^ lemma6Equation21Point x ν‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6Equation21Point x ν)‖ *
        ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
          (lemma6Equation21Point x ν) χ‖ *
        ‖deriv (DirichletCharacter.LFunction χ)
          (lemma6Equation21Point x ν) /
          DirichletCharacter.LFunction χ (lemma6Equation21Point x ν)‖ ≤
      (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        ((c₂ * (Real.log (l : ℝ) + 1) ^ 2) * (4 + |ν|)) :=
    mul_le_mul e2 e_L (norm_nonneg _) e123nn
  refine e3.trans ?_
  have h2xPC : (0 : ℝ) ≤ 2 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
      (∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
      (c₂ * (Real.log (l : ℝ) + 1) ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg hxpos.le _)) hPγ0) hCL0
  calc (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        ((c₂ * (Real.log (l : ℝ) + 1) ^ 2) * (4 + |ν|))
      = (2 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (c₂ * (Real.log (l : ℝ) + 1) ^ 2)) *
        ((4 + |ν|) *
          ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) := by ring
    _ ≤ (2 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (c₂ * (Real.log (l : ℝ) + 1) ^ 2)) *
        (8 * (lemma6SmoothingScale (x : ℝ)) ^ 4 * (1 + ν ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (eq21_four_add_abs_mul_quarticInv_le ha1 ν) h2xPC
    _ = (16 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (c₂ * (Real.log (l : ℝ) + 1) ^ 2) *
          (lemma6SmoothingScale (x : ℝ)) ^ 4) * (1 + ν ^ 2)⁻¹ := by ring

/-- Pointwise bound for the unsplit integrand on Chen's `α`-line: no
zero-free-region input is needed here since `re s > 1`. -/
theorem norm_eq21LogDerivIntegrand_alphaPoint_le
    {x m l : ℕ} [NeZero l] (hx : 2 ≤ x) (hxlog : 3 ≤ Real.log (x : ℝ))
    (ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ))
    (χ : DirichletCharacter ℂ l) (ν : ℝ) :
    ‖eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
      ((Real.exp 1 * (x : ℝ)) * (4 * Real.log (x : ℝ) ^ 2) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (lemma6SmoothingScale (x : ℝ)) ^ 4) * (1 + ν ^ 2)⁻¹ := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have ha0 : (0 : ℝ) < lemma6SmoothingScale (x : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hn3 : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hαpos : (0 : ℝ) < 1 + 1 / Real.log (x : ℝ) := by
    have hnn : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := div_nonneg zero_le_one
      hlogpos.le
    linarith
  have hα1 : (1 : ℝ) ≤ 1 + 1 / Real.log (x : ℝ) := by
    have hnn : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := div_nonneg zero_le_one
      hlogpos.le
    linarith
  have e_x : ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ = Real.exp 1 * (x : ℝ) :=
    norm_nat_cpow_eq21AlphaPoint hx ν
  have e_K : ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ ≤
      ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
    have hk := norm_kernel_le_quadratic_inv
      (x := (x : ℝ)) (σ := 1 + 1 / Real.log (x : ℝ)) ha0 hn3 hαpos ν
    have hσinv : (1 + 1 / Real.log (x : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hα1
    calc ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖
        ≤ (1 + 1 / Real.log (x : ℝ))⁻¹ *
            ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := hk
      _ ≤ 1 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hσinv (by positivity)
      _ = ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := one_mul _
  have e_P : ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
        (lemma6AlphaPoint x ν) χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
    have h := norm_eq21PairPoly_le (x := x) (m := m) χ (lemma6AlphaPoint x ν)
    rwa [lemma6AlphaPoint_re] at h
  have e_L : ‖deriv (DirichletCharacter.LFunction χ)
        (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)‖ ≤
      4 * Real.log (x : ℝ) ^ 2 :=
    (lemma6_norm_logDeriv_le_majorant χ
      (one_lt_lemma6AlphaPoint_re hx ν)).trans
        (lemma6LogDerivMajorant_alpha_le hx ν)
  unfold eq21LogDerivIntegrand
  simp only [norm_neg, norm_mul]
  have e1 : ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ ≤
      (Real.exp 1 * (x : ℝ)) *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ :=
    mul_le_mul e_x.le e_K (norm_nonneg _) (by positivity)
  have e12nn : (0 : ℝ) ≤ (Real.exp 1 * (x : ℝ)) *
      ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by positivity
  have e2 : ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
        ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
          (lemma6AlphaPoint x ν) χ‖ ≤
      (Real.exp 1 * (x : ℝ)) *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) :=
    mul_le_mul e1 e_P (norm_nonneg _) e12nn
  have e123nn : (0 : ℝ) ≤ (Real.exp 1 * (x : ℝ)) *
      ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ *
      (∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) := by positivity
  have e3 : ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
        ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
          (lemma6AlphaPoint x ν) χ‖ *
        ‖deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)‖ ≤
      (Real.exp 1 * (x : ℝ)) *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        (4 * Real.log (x : ℝ) ^ 2) :=
    mul_le_mul e2 e_L (norm_nonneg _) e123nn
  refine e3.trans ?_
  have hq := eq21_quarticInv_le ha1 ν
  calc (Real.exp 1 * (x : ℝ)) *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        (4 * Real.log (x : ℝ) ^ 2)
      = ((Real.exp 1 * (x : ℝ)) * (4 * Real.log (x : ℝ) ^ 2) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹)) *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by ring
    _ ≤ ((Real.exp 1 * (x : ℝ)) * (4 * Real.log (x : ℝ) ^ 2) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹)) *
        ((lemma6SmoothingScale (x : ℝ)) ^ 4 * (1 + ν ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = ((Real.exp 1 * (x : ℝ)) * (4 * Real.log (x : ℝ) ^ 2) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (lemma6SmoothingScale (x : ℝ)) ^ 4) * (1 + ν ^ 2)⁻¹ := by ring

/-- The unsplit integrand is integrable on the shifted line
`γ = 1 - 1/sqrt(log x)`. -/
theorem integrable_eq21LogDerivIntegrand_eq21Point
    {c₁ c₂ : ℝ} (hc₂ : 0 < c₂) (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    (hγregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) :
    Integrable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)) := by
  have hmeas : AEStronglyMeasurable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)) := by
    have hcont : Continuous (lemma6Equation21Point x) := by
      unfold lemma6Equation21Point
      fun_prop
    have hrange : ∀ ν : ℝ, lemma6Equation21Point x ν ∈
        {s : ℂ | (1 : ℝ) / 2 ≤ s.re ∧
          1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤ s.re} := by
      intro ν
      rw [Set.mem_setOf_eq, lemma6Equation21Point_re]
      exact ⟨hγpos, hγregion⟩
    exact ((differentiableOn_eq21LogDerivIntegrand hzfb hl hx
      hχ).continuousOn.comp_continuous hcont hrange).aestronglyMeasurable
  apply ((integrable_inv_one_add_sq.const_mul _)).mono' hmeas
  filter_upwards with ν
  exact norm_eq21LogDerivIntegrand_eq21Point_le (m := m) hc₂ hzfb hx hxlog ha1
    hγpos hγregion hχ ν

/-- The unsplit integrand is integrable on Chen's `α`-line. -/
theorem integrable_eq21LogDerivIntegrand_alphaPoint
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) :
    Integrable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)) := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hmeas : AEStronglyMeasurable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)) := by
    have hcont : Continuous (lemma6AlphaPoint x) := by
      unfold lemma6AlphaPoint
      fun_prop
    have hrange : ∀ ν : ℝ, lemma6AlphaPoint x ν ∈
        {s : ℂ | (1 : ℝ) / 2 ≤ s.re ∧
          1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤ s.re} := by
      intro ν
      rw [Set.mem_setOf_eq, lemma6AlphaPoint_re]
      have hnn : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) := div_nonneg zero_le_one
        hlogpos.le
      have hp : (0 : ℝ) ≤ c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) :=
        mul_nonneg hc₁.le (Real.rpow_nonneg (by positivity) _)
      constructor <;> linarith
    exact ((differentiableOn_eq21LogDerivIntegrand hzfb hl hx
      hχ).continuousOn.comp_continuous hcont hrange).aestronglyMeasurable
  apply ((integrable_inv_one_add_sq.const_mul _)).mono' hmeas
  filter_upwards with ν
  exact norm_eq21LogDerivIntegrand_alphaPoint_le (m := m) hx hxlog ha1 χ ν

/-- Once the two horizontal edges vanish and both boundary restrictions
are integrable, the finite rectangle identity gives equality of the two
improper vertical integrals. -/
theorem eq21LogDeriv_verticalIntegral_eq
    {c₁ c₂ : ℝ} (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    (hγregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    (hhor : Eq21LogDerivHorizontalEdgesVanish x m χ)
    (hα : Integrable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)))
    (hγ : Integrable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν))) :
    (∫ ν : ℝ, eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)) =
      ∫ ν : ℝ, eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν) := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := eq21LogDerivIntegrand x m χ
  let bot : ℝ → ℂ := fun T =>
    ∫ σ : ℝ in γ..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)
  let top : ℝ → ℂ := fun T =>
    ∫ σ : ℝ in γ..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)
  let va : ℝ → ℂ := fun T =>
    ∫ ν : ℝ in (-T)..T, F ((α : ℂ) + (ν : ℂ) * Complex.I)
  let vb : ℝ → ℂ := fun T =>
    ∫ ν : ℝ in (-T)..T, F ((γ : ℂ) + (ν : ℂ) * Complex.I)
  have hpointα : (fun ν : ℝ => F ((α : ℂ) + (ν : ℂ) * Complex.I)) =
      fun ν : ℝ =>
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν) := by
    funext ν
    rfl
  have hpointγ : (fun ν : ℝ => F ((γ : ℂ) + (ν : ℂ) * Complex.I)) =
      fun ν : ℝ =>
        eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν) := by
    funext ν
    rfl
  have hva : Tendsto va atTop
      (𝓝 (∫ ν : ℝ,
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν))) := by
    have ht := intervalIntegral_tendsto_integral hα
      tendsto_neg_atTop_atBot
      (show Tendsto (fun T : ℝ => T) atTop atTop from tendsto_id)
    simpa only [va, hpointα, id_eq] using ht
  have hvb : Tendsto vb atTop
      (𝓝 (∫ ν : ℝ,
        eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν))) := by
    have ht := intervalIntegral_tendsto_integral hγ
      tendsto_neg_atTop_atBot
      (show Tendsto (fun T : ℝ => T) atTop atTop from tendsto_id)
    simpa only [vb, hpointγ, id_eq] using ht
  have hhor' : Tendsto bot atTop (𝓝 0) ∧ Tendsto top atTop (𝓝 0) := by
    simpa only [Eq21LogDerivHorizontalEdgesVanish, bot, top, F, γ, α] using
      hhor
  have hcalc := (hhor'.1.sub hhor'.2).add
    ((hva.const_smul Complex.I).sub (hvb.const_smul Complex.I))
  have heq : ∀ T : ℝ,
      bot T - top T + (Complex.I • va T - Complex.I • vb T) = 0 := by
    intro T
    simpa only [bot, top, va, vb, F, γ, α, sub_eq_add_neg,
      add_assoc] using
      eq21LogDeriv_finite_rectangle (m := m) hzfb hl hx hxlog hγpos hγregion hχ T
  have hzero : Tendsto
      (fun T : ℝ => bot T - top T +
        (Complex.I • va T - Complex.I • vb T))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun T => (heq T).symm)
  have hlim :
      (0 : ℂ) - 0 +
        (Complex.I •
            (∫ ν : ℝ,
              eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)) -
          Complex.I •
            (∫ ν : ℝ,
              eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν))) = 0 :=
    tendsto_nhds_unique hcalc hzero
  have hmul : Complex.I *
      ((∫ ν : ℝ,
          eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)) -
        ∫ ν : ℝ,
          eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)) = 0 := by
    simpa only [zero_sub, zero_add, neg_zero, smul_eq_mul, mul_sub] using
      hlim
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero)

/-- The shifted vertical integral is bounded by
`16 · x^γ · P_γ · c₂ (log l + 1)² · a⁴ · π`. -/
theorem norm_integral_eq21Point_le
    {c₁ c₂ : ℝ} (hc₂ : 0 < c₂) (hzfb : Eq21ZeroFreeBound c₁ c₂)
    {x m l : ℕ} [NeZero l] (hx : 2 ≤ x) (hxlog : 3 ≤ Real.log (x : ℝ))
    (ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    (hγregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    (hint : Integrable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν))) :
    ‖∫ ν : ℝ, eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ ≤
      16 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        (c₂ * (Real.log (l : ℝ) + 1) ^ 2) *
        (lemma6SmoothingScale (x : ℝ)) ^ 4 * Real.pi := by
  have h1 : ‖∫ ν : ℝ,
        eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ ≤
      ∫ ν : ℝ,
        ‖eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ :=
    norm_integral_le_integral_norm _
  refine h1.trans ?_
  calc (∫ ν : ℝ,
        ‖eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖)
      ≤ ∫ ν : ℝ, (16 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (c₂ * (Real.log (l : ℝ) + 1) ^ 2) *
          (lemma6SmoothingScale (x : ℝ)) ^ 4) * (1 + ν ^ 2)⁻¹ := by
        apply integral_mono_ae hint.norm
          (integrable_inv_one_add_sq.const_mul _)
        filter_upwards with ν
        exact norm_eq21LogDerivIntegrand_eq21Point_le hc₂ hzfb hx hxlog
          ha1 hγpos hγregion hχ ν
    _ = 16 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          (c₂ * (Real.log (l : ℝ) + 1) ^ 2) *
          (lemma6SmoothingScale (x : ℝ)) ^ 4 * Real.pi := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]

set_option maxHeartbeats 800000 in
/-- **The character-level estimate of equation (21).**  After moving the
contour to `Re s = 1 - 1/sqrt(log x)`, the `α`-line logarithmic-derivative
integral of one primitive character is bounded by `C (log x)^90` times the
shifted prime-pair power sum.  The only analytic input is the classical
zero-free region interface `PrimitiveZeroFreeRegion`. -/
theorem eq21_characterIntegral_bound (hzf : PrimitiveZeroFreeRegion) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (m l : ℕ) [NeZero l] (χ : DirichletCharacter ℂ l),
        2 ≤ l → (l : ℝ) ≤ (Real.log (x : ℝ)) ^ 100 → χ.IsPrimitive →
          ‖(1 / (2 * Real.pi) : ℝ) • ∫ ν : ℝ,
              eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
            C * (Real.log (x : ℝ)) ^ 90 *
              ∑ q ∈ chenPairs x,
                ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^
                  (1 - 1 / Real.sqrt (Real.log (x : ℝ))) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hzfb⟩ := hzf
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev4 : ∀ᶠ x : ℕ in atTop, (4 : ℝ) ≤ Real.log (x : ℝ) :=
    hlogT.eventually (eventually_ge_atTop 4)
  have hevreg : ∀ᶠ x : ℕ in atTop,
      c₁⁻¹ ≤ (Real.log (x : ℝ)) ^ ((1 : ℝ) / 6) :=
    ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).comp
      hlogT).eventually (eventually_ge_atTop c₁⁻¹)
  refine ⟨244824 * c₂ + 1, by linarith [hc₂], ?_⟩
  filter_upwards [eventually_ge_atTop 2, hev4, hevreg] with x hx2 hxlog4
    hregc
  intro m l _ χ hl2 hl100 hχ
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hxlog3 : 3 ≤ Real.log (x : ℝ) := by linarith
  have ha0 : (0 : ℝ) < lemma6SmoothingScale (x : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have ha1 : (1 : ℝ) ≤ lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.one_le_rpow hlog1 (by norm_num)
  -- the shifted line is in the right half-plane
  have hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)) := by
    have hsp : (0 : ℝ) < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.mpr hlogpos
    have h2s : (2 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← h4]
      exact Real.sqrt_le_sqrt (by linarith)
    have hinv : 1 / Real.sqrt (Real.log (x : ℝ)) ≤ 1 / 2 := by
      rw [one_div, one_div]
      exact (inv_le_inv₀ hsp (by norm_num)).mpr h2s
    linarith
  -- the shifted line lies inside the zero-free region
  have hlpos : (0 : ℝ) < (l : ℝ) := by
    exact_mod_cast (show 0 < l by omega)
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (show 1 ≤ l by omega)
  have hpow1 : ((Real.log (x : ℝ)) ^ 100) ^ ((-1 : ℝ) / 300) ≤
      (l : ℝ) ^ ((-1 : ℝ) / 300) :=
    Real.rpow_le_rpow_of_nonpos hlpos hl100 (by norm_num)
  have hpow2 : ((Real.log (x : ℝ)) ^ 100) ^ ((-1 : ℝ) / 300) =
      (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (Real.log (x : ℝ)) 100,
      ← Real.rpow_mul hlogpos.le]
    congr 1
    norm_num
  have hpow1' : (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 3) ≤
      (l : ℝ) ^ ((-1 : ℝ) / 300) := hpow2 ▸ hpow1
  have hc1 : (1 : ℝ) ≤ c₁ * (Real.log (x : ℝ)) ^ ((1 : ℝ) / 6) := by
    have h := mul_le_mul_of_nonneg_left hregc hc₁.le
    rwa [mul_inv_cancel₀ hc₁.ne'] at h
  have h3 : (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 2) ≤
      c₁ * (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 3) := by
    have hrw : (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 2) *
          (Real.log (x : ℝ)) ^ ((1 : ℝ) / 6) =
        (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 3) := by
      rw [← Real.rpow_add hlogpos]
      congr 1
      ring
    calc (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 2)
        = (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 2) * 1 := (mul_one _).symm
      _ ≤ (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 2) *
            (c₁ * (Real.log (x : ℝ)) ^ ((1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left hc1 (Real.rpow_nonneg hlogpos.le _)
      _ = c₁ * (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 3) := by
          rw [← hrw]
          ring
  have h4 : (Real.log (x : ℝ)) ^ ((-1 : ℝ) / 2) =
      1 / Real.sqrt (Real.log (x : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hlogpos.le]
    congr 1
    ring
  have hγregion : 1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)) := by
    have hle : 1 / Real.sqrt (Real.log (x : ℝ)) ≤
        c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300) := by
      rw [← h4]
      exact h3.trans (mul_le_mul_of_nonneg_left hpow1' hc₁.le)
    linarith
  -- contour shift and the shifted-line bound
  have hγI := integrable_eq21LogDerivIntegrand_eq21Point (m := m) hc₂ hzfb hl2 hx2
    hxlog3 ha1 hγpos hγregion hχ
  have hαI := integrable_eq21LogDerivIntegrand_alphaPoint (m := m) hc₁ hzfb hl2 hx2
    hxlog3 ha1 hχ
  have hhor := eq21LogDeriv_horizontalEdgesVanish (m := m) hc₂ hzfb hl2 hx2 hxlog3
    hγpos hγregion hχ
  have hveq := eq21LogDeriv_verticalIntegral_eq (m := m) hzfb hl2 hx2 hxlog3 hγpos
    hγregion hχ hhor hαI hγI
  have hγbound := norm_integral_eq21Point_le (m := m) hc₂ hzfb hx2 hxlog3 ha1 hγpos
    hγregion hχ hγI
  -- abbreviations
  set γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ)) with hγdef
  set a : ℝ := lemma6SmoothingScale (x : ℝ) with hadef
  set Pγ : ℝ := ∑ q ∈ lemma6AdmissiblePairs x m,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hPγdef
  set CL : ℝ := c₂ * (Real.log (l : ℝ) + 1) ^ 2 with hCLdef
  set S1' : ℝ := ∑ q ∈ lemma6AdmissiblePairs x m,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) with hS1'def
  set S1 : ℝ := ∑ q ∈ lemma6AdmissiblePairs x m,
    ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ γ with hS1def
  set S : ℝ := ∑ q ∈ chenPairs x,
    ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ γ with hSdef
  -- the pair-polynomial majorant costs a factor `3`
  have hS1'nn : (0 : ℝ) ≤ S1' := by rw [hS1'def]; positivity
  have hS1nn : (0 : ℝ) ≤ S1 := by rw [hS1def]; positivity
  have hSnn : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  have hCL0 : (0 : ℝ) ≤ CL := by
    rw [hCLdef]
    exact mul_nonneg hc₂.le (sq_nonneg _)
  have hperq : ∀ q ∈ lemma6AdmissiblePairs x m,
      ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) *
          |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ ≤
        (3 / Real.log (x : ℝ)) * ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) := by
    intro q hq
    have hqchen : q ∈ chenPairs x := (Finset.mem_filter.mp hq).1
    have hlog3 := eq21_chenPairs_log_div_ge hx2 hqchen
    have hlogpos' : (0 : ℝ) <
        Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) := by
      have hpos : (0 : ℝ) < (1 / 3) * Real.log (x : ℝ) := by positivity
      linarith
    have hinv : |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ ≤
        3 / Real.log (x : ℝ) := by
      rw [abs_of_nonneg hlogpos'.le]
      have h1 : (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)))⁻¹ ≤
          ((1 / 3) * Real.log (x : ℝ))⁻¹ :=
        (inv_le_inv₀ hlogpos' (by positivity)).mpr hlog3
      have h2 : ((1 / 3) * Real.log (x : ℝ))⁻¹ = 3 / Real.log (x : ℝ) := by
        field_simp
      rwa [h2] at h1
    calc ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) *
            |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ ≤
          ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) * (3 / Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg (by positivity) _)
      _ = (3 / Real.log (x : ℝ)) * ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) :=
        mul_comm _ _
  have hsum : Pγ ≤ (3 / Real.log (x : ℝ)) * S1' := by
    rw [hPγdef, hS1'def, Finset.mul_sum]
    exact Finset.sum_le_sum hperq
  have h3L : (3 : ℝ) / Real.log (x : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [hlog1]
  have hPγle : Pγ ≤ 3 * S1' :=
    hsum.trans (mul_le_mul_of_nonneg_right h3L hS1'nn)
  -- the `x^γ` factor turns the pair powers into the shifted pair sum
  have hqid : ∀ q ∈ lemma6AdmissiblePairs x m,
      (x : ℝ) ^ γ * ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) =
        ((x : ℝ) / ((q.1 : ℝ) * q.2)) ^ γ := by
    intro q hq
    obtain ⟨hp1, hp2⟩ := eq21_primes_of_mem_admissiblePairs hq
    have hqpos' : (0 : ℝ) < (q.1 : ℝ) * (q.2 : ℝ) :=
      mul_pos (by exact_mod_cast hp1.pos) (by exact_mod_cast hp2.pos)
    rw [Nat.cast_mul, Real.div_rpow hxpos.le hqpos'.le,
      Real.rpow_neg hqpos'.le, div_eq_mul_inv]
  have hS1eq : S1 = (x : ℝ) ^ γ * S1' := by
    rw [hS1def, hS1'def, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q hq => (hqid q hq).symm)
  have hxP : (x : ℝ) ^ γ * Pγ ≤ 3 * S1 := by
    calc (x : ℝ) ^ γ * Pγ ≤ (x : ℝ) ^ γ * (3 * S1') :=
          mul_le_mul_of_nonneg_left hPγle (Real.rpow_nonneg hxpos.le _)
      _ = 3 * ((x : ℝ) ^ γ * S1') := by ring
      _ = 3 * S1 := by rw [← hS1eq]
  have hS1S : S1 ≤ S := by
    rw [hS1def, hSdef]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro q hq _
    positivity
  -- the conductor factor `(log l + 1)²` costs `(log x)²`
  have hlogl : Real.log (l : ℝ) ≤ 100 * Real.log (Real.log (x : ℝ)) := by
    have h1 : Real.log (l : ℝ) ≤ Real.log ((Real.log (x : ℝ)) ^ 100) :=
      Real.log_le_log hlpos hl100
    rwa [Real.log_pow] at h1
  have hloglog : Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) :=
    (Real.log_le_sub_one_of_pos hlogpos).trans (by linarith)
  have hCLle : CL ≤ 10201 * c₂ * (Real.log (x : ℝ)) ^ 2 := by
    have hbase : Real.log (l : ℝ) + 1 ≤ 101 * Real.log (x : ℝ) := by
      nlinarith [hlogl, hloglog, hlog1]
    have hb0 : (0 : ℝ) ≤ Real.log (l : ℝ) + 1 := by
      have h1 : (0 : ℝ) ≤ Real.log (l : ℝ) := Real.log_nonneg hl1
      linarith
    have h2 : (Real.log (l : ℝ) + 1) ^ 2 ≤ (101 * Real.log (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hb0 hbase 2
    have h3' : (101 * Real.log (x : ℝ)) ^ 2 =
        10201 * (Real.log (x : ℝ)) ^ 2 := by ring
    rw [hCLdef]
    calc c₂ * (Real.log (l : ℝ) + 1) ^ 2 ≤
          c₂ * (10201 * (Real.log (x : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (h3' ▸ h2) hc₂.le
      _ = 10201 * c₂ * (Real.log (x : ℝ)) ^ 2 := by ring
  -- the kernel-height integral costs `a⁴ = (log x)^4.4`
  have ha4 : a ^ 4 = (Real.log (x : ℝ)) ^ ((4.4 : ℝ)) := by
    rw [hadef]
    unfold lemma6SmoothingScale
    rw [← Real.rpow_natCast ((Real.log (x : ℝ)) ^ (1.1 : ℝ)) 4,
      ← Real.rpow_mul hlogpos.le]
    congr 1
    norm_num
  have hL64 : a ^ 4 * (Real.log (x : ℝ)) ^ 2 =
      (Real.log (x : ℝ)) ^ ((6.4 : ℝ)) := by
    rw [ha4, ← Real.rpow_natCast (Real.log (x : ℝ)) 2,
      ← Real.rpow_add hlogpos]
    congr 1
    norm_num
  have hLle : (Real.log (x : ℝ)) ^ ((6.4 : ℝ)) ≤
      (Real.log (x : ℝ)) ^ (90 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log (x : ℝ)) 90]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
  -- the final chain
  rw [hveq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) * ‖∫ ν : ℝ,
          eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖
      ≤ (1 / (2 * Real.pi)) * (16 * (x : ℝ) ^ γ * Pγ * CL * a ^ 4 *
          Real.pi) :=
        mul_le_mul_of_nonneg_left hγbound (by positivity)
    _ = 8 * ((x : ℝ) ^ γ * Pγ) * CL * a ^ 4 := by
        field_simp [Real.pi_pos.ne']
        ring
    _ ≤ 8 * (3 * S) * (10201 * c₂ * (Real.log (x : ℝ)) ^ 2) * a ^ 4 := by
        have hA : 8 * ((x : ℝ) ^ γ * Pγ) ≤ 8 * (3 * S) :=
          mul_le_mul_of_nonneg_left
            (hxP.trans (mul_le_mul_of_nonneg_left hS1S
              (by norm_num : (0 : ℝ) ≤ 3))) (by norm_num)
        have h8nn : (0 : ℝ) ≤ 8 * (3 * S) := by positivity
        have hstep : 8 * ((x : ℝ) ^ γ * Pγ) * CL ≤
            8 * (3 * S) * (10201 * c₂ * (Real.log (x : ℝ)) ^ 2) :=
          (mul_le_mul_of_nonneg_right hA hCL0).trans
            (mul_le_mul_of_nonneg_left hCLle h8nn)
        exact mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = 244824 * c₂ * (a ^ 4 * (Real.log (x : ℝ)) ^ 2) * S := by ring
    _ = 244824 * c₂ * (Real.log (x : ℝ)) ^ ((6.4 : ℝ)) * S := by
        rw [hL64]
    _ ≤ 244824 * c₂ * (Real.log (x : ℝ)) ^ (90 : ℕ) * S :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLle
            (mul_nonneg (by norm_num) hc₂.le)) hSnn
    _ ≤ (244824 * c₂ + 1) * (Real.log (x : ℝ)) ^ (90 : ℕ) * S :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith)
            (by positivity : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ 90)) hSnn

end Chen
