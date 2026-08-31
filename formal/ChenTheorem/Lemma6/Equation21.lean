/-
The zero-free-region contour shift and the character-level estimate of
equation (21) in Lemma 6, completing the last unproved step of Lemma 6
beyond the isolated zero-free-region interface.

Unlike the `A + B` split used in equations (16)–(20), equation (21) moves
the *unsplit* logarithmic-derivative integrand
`-x^s · K(s) · P(s, χ) · (L'/L)(s, χ)` from Chen's line `α = 1 + 1/log x`
to the line `γ = 1 - 1/sqrt(log x)` inside the classical zero-free region.
The single analytic input is the interface `PrimitiveZeroFreeRegion` of
`ZeroFreeRegion.lean`: a height-dependent classical mixed zero-free width,
together with its companion `L'/L` bound on the half-width region.  It is
used only inside a finite rectangle of height `(log x)^10`.

Pipeline (all proved below except the single documented input):

* `lemma6Equation21Point` — Chen's shifted contour point,
  `1 - 1/sqrt(log x) + i ν`;
* elementary pair estimates: the product of a Chen prime pair is at most
  `x^(2/3)`, hence `log (x / (p₁p₂)) ≥ (1/3) log x`;
* `norm_kernel_le_half_power` — the exact decay of the rational Mellin
  kernel, `‖K(σ + iν)‖ ≤ σ⁻¹ · (1 + (ν/a)²)^(-(n+1)/2)`, together with
  the weaker quadratic form `σ⁻¹ · (1 + (ν/a)²)⁻²` used downstream;
* `eq21LogDerivIntegrand` — the unsplit integrand, holomorphic throughout
  the finite rectangle by the half-width classical region;
* Cauchy–Goursat on that rectangle
  (`eq21LogDeriv_finite_rectangle_classical`), an explicit bound for its
  truncated shifted side, and full-kernel `x^(-1/10)` bounds for both
  horizontal sides;
* a direct absolutely-convergent-half-plane estimate for the part of the
  original `α` line outside the rectangle, again using the full kernel
  order, so no fixed shifted line is asserted at unbounded height;
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

/-- The finite height used for the equation-(21) contour.  Its exponent is
well above the smoothing scale `(log x)^1.1`, while its logarithm is only
`O(log log x)` for the classical zero-free region. -/
noncomputable def lemma6Equation21Height (x : ℕ) : ℝ :=
  Real.log (x : ℝ) ^ 10

theorem primitiveZeroFreeHeightLog_pos
    {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := by
  apply Real.log_pos
  have hqcast : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  nlinarith

theorem primitiveZeroFreeWidth_pos
    {cHeight cSiegel : ℝ} (hcHeight : 0 < cHeight)
    (hcSiegel : 0 < cSiegel) {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    0 < primitiveZeroFreeWidth cHeight cSiegel q t := by
  unfold primitiveZeroFreeWidth
  apply lt_min
  · exact div_pos hcHeight (primitiveZeroFreeHeightLog_pos hq t)
  · exact mul_pos hcSiegel (Real.rpow_pos_of_pos (by positivity) _)

/-- A point in the closed half-width region lies strictly inside the
nonvanishing region. -/
theorem one_sub_width_lt_of_half_width_le
    {width re : ℝ} (hwidth : 0 < width)
    (hhalf : 1 - width / 2 ≤ re) :
    1 - width < re := by
  have : 1 - width < 1 - width / 2 := by linarith
  exact this.trans_le hhalf

theorem eventually_two_mul_111_log_log_lt_mul_sqrt_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      222 * Real.log (Real.log (x : ℝ)) <
        c * Real.sqrt (Real.log (x : ℝ)) := by
  have hsmallReal : ∀ᶠ y : ℝ in atTop,
      ‖Real.log y ^ (1 : ℝ)‖ ≤
        (c / 444) * ‖y ^ ((1 : ℝ) / 2)‖ :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).def (by positivity : 0 < c / 444)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogT.eventually hsmallReal,
      hlogT.eventually (eventually_gt_atTop 1)] with x hx hL1
  have hlogLpos : 0 < Real.log (Real.log (x : ℝ)) := Real.log_pos hL1
  have hLpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans hL1
  have hrpowpos : 0 < (Real.log (x : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hLpos _
  have hx' : Real.log (Real.log (x : ℝ)) ≤
      (c / 444) * (Real.log (x : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos hlogLpos,
      Real.norm_eq_abs, abs_of_pos hrpowpos] at hx
    exact hx
  rw [Real.sqrt_eq_rpow]
  nlinarith [mul_pos hc hrpowpos]

/-- Uniformly for the finite equation-(21) rectangle and conductors
`q ≤ (log x)^100`, the shifted line eventually lies in the half-width
classical zero-free region. -/
theorem eventually_two_div_sqrt_log_lt_primitiveZeroFreeWidth
    {cHeight cSiegel : ℝ} (hcHeight : 0 < cHeight)
    (hcSiegel : 0 < cSiegel) :
    ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ), 2 ≤ q →
        (q : ℝ) ≤ Real.log (x : ℝ) ^ 100 →
        ∀ t : ℝ, |t| ≤ lemma6Equation21Height x →
          2 / Real.sqrt (Real.log (x : ℝ)) <
            primitiveZeroFreeWidth cHeight cSiegel q t := by
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hheight :=
    eventually_two_mul_111_log_log_lt_mul_sqrt_log hcHeight
  have hsiegelReal : ∀ᶠ y : ℝ in atTop,
      2 < cSiegel * y ^ ((1 : ℝ) / 6) := by
    have ht := tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)
    have hev := ht.eventually (eventually_gt_atTop (2 / cSiegel))
    filter_upwards [hev, eventually_gt_atTop 0] with y hy hy0
    have := mul_lt_mul_of_pos_left hy hcSiegel
    field_simp [hcSiegel.ne'] at this
    simpa only [mul_comm] using this
  have hsiegel := hlogT.eventually hsiegelReal
  have hLtwo := hlogT.eventually (eventually_ge_atTop 2)
  filter_upwards [hheight, hsiegel, hLtwo] with x hheight hsiegel hLtwo
  intro q hq hlq t ht
  let L : ℝ := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hTnonneg : 0 ≤ lemma6Equation21Height x := by
    unfold lemma6Equation21Height
    positivity
  have ht2 : |t| + 2 ≤ L ^ 11 := by
    have h10two : (2 : ℝ) ≤ L ^ 10 := by
      calc (2 : ℝ) ≤ L := hLtwo
        _ ≤ L ^ 10 := by
          have := pow_le_pow_right₀ hLone (show 1 ≤ 10 by omega)
          simpa using this
    calc
      |t| + 2 ≤ lemma6Equation21Height x + 2 := by linarith
      _ = L ^ 10 + 2 := by rfl
      _ ≤ 2 * L ^ 10 := by linarith
      _ ≤ L * L ^ 10 :=
        mul_le_mul_of_nonneg_right hLtwo (pow_nonneg hLpos.le _)
      _ = L ^ 11 := by ring
  have harg : (q : ℝ) * (|t| + 2) ≤ L ^ 111 := by
    calc
      (q : ℝ) * (|t| + 2) ≤ L ^ 100 * L ^ 11 :=
        mul_le_mul hlq ht2 (by positivity) (by positivity)
      _ = L ^ 111 := by ring
  have hargpos : 0 < (q : ℝ) * (|t| + 2) := by positivity
  have hlogarg : Real.log ((q : ℝ) * (|t| + 2)) ≤
      111 * Real.log L := by
    have hlogle := Real.log_le_log hargpos harg
    rw [Real.log_pow] at hlogle
    simpa only [Nat.cast_ofNat, mul_comm] using hlogle
  have hlogargpos := primitiveZeroFreeHeightLog_pos hq t
  have hheightWidth : 2 / Real.sqrt L <
      cHeight / Real.log ((q : ℝ) * (|t| + 2)) := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.2 hLpos) hlogargpos]
    calc
      2 * Real.log ((q : ℝ) * (|t| + 2)) ≤
          222 * Real.log L := by linarith
      _ < cHeight * Real.sqrt L := by simpa only [L] using hheight
  have hpowq : L ^ ((-1 : ℝ) / 3) ≤
      (q : ℝ) ^ ((-1 : ℝ) / 300) := by
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < q)
      hlq (by norm_num : ((-1 : ℝ) / 300) ≤ 0)
    have hpow : (L ^ 100) ^ ((-1 : ℝ) / 300) =
        L ^ ((-1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast L 100, ← Real.rpow_mul hLpos.le]
      congr 1
      norm_num
    exact hpow ▸ hp
  have hsiegelWidth : 2 / Real.sqrt L <
      cSiegel * (q : ℝ) ^ ((-1 : ℝ) / 300) := by
    have hpowid : L ^ ((-1 : ℝ) / 2) * L ^ ((1 : ℝ) / 6) =
        L ^ ((-1 : ℝ) / 3) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    have hinvSqrt : 1 / Real.sqrt L = L ^ ((-1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hLpos.le]
      congr 1
      ring
    have hinvSqrt' : (Real.sqrt L)⁻¹ = L ^ ((-1 : ℝ) / 2) := by
      simpa only [one_div] using hinvSqrt
    calc
      2 / Real.sqrt L = 2 * L ^ ((-1 : ℝ) / 2) := by
        rw [div_eq_mul_inv, hinvSqrt']
      _ < cSiegel * L ^ ((1 : ℝ) / 6) * L ^ ((-1 : ℝ) / 2) := by
        have hnonneg : 0 ≤ L ^ ((-1 : ℝ) / 2) :=
          Real.rpow_nonneg hLpos.le _
        exact mul_lt_mul_of_pos_right hsiegel
          (Real.rpow_pos_of_pos hLpos _)
      _ = cSiegel * L ^ ((-1 : ℝ) / 3) := by rw [← hpowid]; ring
      _ ≤ cSiegel * (q : ℝ) ^ ((-1 : ℝ) / 300) :=
        mul_le_mul_of_nonneg_left hpowq hcSiegel.le
  unfold primitiveZeroFreeWidth
  exact lt_min hheightWidth hsiegelWidth

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

/-- Split the exact half-power kernel decay into a quadratic integrable
factor and an additional fixed power saving.  The substantive large-height
estimate is isolated in `hden`; this algebraic lemma is reused on the
horizontal edges and the `alpha`-line tails. -/
theorem norm_kernel_le_quadratic_inv_mul_rpow_neg
    {x σ X δ : ℝ} (hX : 0 < X)
    (ha : 0 < lemma6SmoothingScale x)
    (hn : 1 ≤ lemma6SmoothingOrder x) (hσ : (1 : ℝ) / 2 ≤ σ)
    (ν : ℝ)
    (hden : X ^ δ *
        (1 + (ν / lemma6SmoothingScale x) ^ 2) ^ 2 ≤
      (1 + (ν / lemma6SmoothingScale x) ^ 2) ^
        (((lemma6SmoothingOrder x + 1 : ℕ) : ℝ) / 2)) :
    ‖lemma6SmoothingMellinKernel x
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      2 * X ^ (-δ) *
        ((1 + (ν / lemma6SmoothingScale x) ^ 2) ^ 2)⁻¹ := by
  have hσpos : 0 < σ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hσ
  have hk := norm_kernel_le_half_power ha hn hσpos ν
  let u : ℝ := 1 + (ν / lemma6SmoothingScale x) ^ 2
  let E : ℝ := (((lemma6SmoothingOrder x + 1 : ℕ) : ℝ) / 2)
  have hu : 0 < u := by dsimp only [u]; positivity
  have hXE : 0 < X ^ δ * u ^ 2 :=
    mul_pos (Real.rpow_pos_of_pos hX _) (pow_pos hu 2)
  have hE : 0 < u ^ E := Real.rpow_pos_of_pos hu _
  have hinv : (u ^ E)⁻¹ ≤ (X ^ δ * u ^ 2)⁻¹ := by
    rw [inv_le_inv₀ hE hXE]
    exact hden
  have hsplit : (X ^ δ * u ^ 2)⁻¹ =
      X ^ (-δ) * (u ^ 2)⁻¹ := by
    rw [mul_inv, ← Real.rpow_neg hX.le]
  have hσinv : σ⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ hσpos
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr hσ
    rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at h
  calc
    ‖lemma6SmoothingMellinKernel x
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖
        ≤ σ⁻¹ * (u ^ E)⁻¹ := by simpa only [u, E] using hk
    _ ≤ 2 * (X ^ δ * u ^ 2)⁻¹ :=
      mul_le_mul hσinv hinv (by positivity) (by positivity)
    _ = 2 * X ^ (-δ) * (u ^ 2)⁻¹ := by rw [hsplit]; ring
    _ = 2 * X ^ (-δ) *
        ((1 + (ν / lemma6SmoothingScale x) ^ 2) ^ 2)⁻¹ := by rfl

/-- At the polylogarithmic truncation height, the unused part of the exact
kernel exponent supplies a fixed power saving in `x`. -/
theorem eventually_large_height_kernel_denominator :
    ∀ᶠ x : ℕ in atTop,
      ∀ ν : ℝ, lemma6Equation21Height x ≤ |ν| →
        (x : ℝ) ^ ((1 : ℝ) / 10) *
            (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2 ≤
          (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
            (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2) := by
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogT.eventually (eventually_ge_atTop 16),
      eventually_ge_atTop 2] with x hL16 hx2
  intro ν hν
  let L : ℝ := Real.log (x : ℝ)
  let a : ℝ := lemma6SmoothingScale (x : ℝ)
  let n : ℕ := lemma6SmoothingOrder (x : ℝ)
  let u : ℝ := 1 + (ν / a) ^ 2
  let E : ℝ := (((n + 1 : ℕ) : ℝ) / 2)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hLpos _
  have haT : a ≤ lemma6Equation21Height x := by
    dsimp only [a, lemma6SmoothingScale, lemma6Equation21Height, L]
    rw [← Real.rpow_natCast (Real.log (x : ℝ)) 10]
    exact Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hratio : 1 ≤ |ν| / a := by
    rw [le_div_iff₀ ha]
    simpa only [one_mul] using haT.trans hν
  have hratioSq : (1 : ℝ) ≤ (ν / a) ^ 2 := by
    have habsdiv : |ν / a| = |ν| / a := by
      rw [abs_div, abs_of_pos ha]
    have hratio' : 1 ≤ |ν / a| := by rwa [habsdiv]
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hratio' 2
    simpa only [one_pow, sq_abs] using hs
  have hu2 : (2 : ℝ) ≤ u := by dsimp only [u]; linarith
  have huone : (1 : ℝ) ≤ u := one_le_two.trans hu2
  have hu : 0 < u := zero_lt_one.trans_le huone
  have hnL : L < (n + 1 : ℕ) := by
    dsimp only [n, lemma6SmoothingOrder, L]
    exact_mod_cast Nat.lt_floor_add_one (Real.log (x : ℝ))
  have hEgap : L / 4 ≤ E - 2 := by
    dsimp only [E]
    have hnL' : L < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hnL
    linarith
  have hL4 : 0 ≤ L / 4 := by positivity
  have hgap0 : 0 ≤ E - 2 := hL4.trans hEgap
  have hexp : (1 : ℝ) / 10 ≤ Real.log 2 / 4 := by
    linarith [Real.log_two_gt_d9]
  have hpowX : (x : ℝ) ^ ((1 : ℝ) / 10) ≤
      (2 : ℝ) ^ (L / 4) := by
    calc
      (x : ℝ) ^ ((1 : ℝ) / 10) ≤
          (x : ℝ) ^ (Real.log 2 / 4) :=
        Real.rpow_le_rpow_of_exponent_le hxone hexp
      _ = (2 : ℝ) ^ (L / 4) := by
        rw [Real.rpow_def_of_pos hxpos,
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        dsimp only [L]
        congr 1
        ring
  have hpowBase : (2 : ℝ) ^ (L / 4) ≤ u ^ (E - 2) := by
    calc
      (2 : ℝ) ^ (L / 4) ≤ u ^ (L / 4) :=
        Real.rpow_le_rpow (by norm_num) hu2 hL4
      _ ≤ u ^ (E - 2) :=
        Real.rpow_le_rpow_of_exponent_le huone hEgap
  have hsave : (x : ℝ) ^ ((1 : ℝ) / 10) ≤ u ^ (E - 2) :=
    hpowX.trans hpowBase
  calc
    (x : ℝ) ^ ((1 : ℝ) / 10) *
        (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2
        = (x : ℝ) ^ ((1 : ℝ) / 10) * u ^ 2 := by rfl
    _ ≤ u ^ (E - 2) * u ^ 2 :=
      mul_le_mul_of_nonneg_right hsave (pow_nonneg hu.le _)
    _ = u ^ E := by
      rw [← Real.rpow_natCast u 2, ← Real.rpow_add hu]
      congr 1
      ring
    _ = (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
        (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2) := by rfl

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

/-- Holomorphy of the unsplit integrand in the absolutely convergent
half-plane.  This is used for the original `alpha` line and is independent
of every zero-free-region input. -/
theorem differentiableOn_eq21LogDerivIntegrand_one_lt_re
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) :
    DifferentiableOn ℂ (eq21LogDerivIntegrand x m χ)
      {s : ℂ | 1 < s.re} := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 by omega)
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  have hk : DifferentiableOn ℂ (lemma6SmoothingMellinKernel (x : ℝ))
      {s : ℂ | 1 < s.re} :=
    (differentiableOn_lemma6SmoothingMellinKernel
      (x := (x : ℝ)) (by exact_mod_cast (show 1 < x by omega))).mono
        (fun s hs => by
          change 0 < s.re
          exact zero_lt_one.trans hs)
  have hP : DifferentiableOn ℂ
      (fun s => lemma6PairDirichletPolynomial x
        (lemma6AdmissiblePairs x m) s χ) {s : ℂ | 1 < s.re} :=
    (differentiable_eq21PairPoly x m χ).differentiableOn
  have hLq : DifferentiableOn ℂ
      (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) {s : ℂ | 1 < s.re} := by
    intro s hs
    have hne : DirichletCharacter.LFunction χ s ≠ 0 := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
      exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
    exact ((primitiveCharacter_differentiable_LFunction_deriv hl
        hχ).differentiableAt.div
      (primitiveCharacter_differentiable_LFunction hl hχ).differentiableAt
      hne).differentiableWithinAt
  unfold eq21LogDerivIntegrand
  exact (((hxpow.differentiableOn.mul hk).mul hP).mul hLq).neg

/-- Cauchy-Goursat on the finite equation-(21) rectangle using the
height-dependent classical region.  The hypothesis `hwidth` places the
whole rectangle in the half-width region; unlike
`eq21LogDeriv_finite_rectangle`, no assertion at heights beyond `T` is
used. -/
theorem eq21LogDeriv_finite_rectangle_classical
    (data : PrimitiveZeroFreeRegionData)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ t : ℝ, |t| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        primitiveZeroFreeWidth data.cHeight data.cSiegel l t) :
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
    have h2 : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) :=
      div_nonneg zero_le_one hlog.le
    linarith
  have hzre : z.re = γ := by dsimp only [z]; simp
  have hwre : w.re = α := by dsimp only [w]; simp
  have hzim : z.im = -T := by dsimp only [z]; simp
  have hwim : w.im = T := by dsimp only [w]; simp
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast (show x ≠ 0 by omega)
  letI : NeZero (x : ℂ) := ⟨hxC⟩
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  have hk : DifferentiableOn ℂ (lemma6SmoothingMellinKernel (x : ℝ))
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    (differentiableOn_lemma6SmoothingMellinKernel
      (x := (x : ℝ)) (by exact_mod_cast (show 1 < x by omega))).mono
        (fun s hs => by
          have hre := hs.1
          rw [hzre, hwre, uIcc_of_le hγα] at hre
          exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
            (hγpos.trans hre.1))
  have hP : DifferentiableOn ℂ
      (fun s => lemma6PairDirichletPolynomial x
        (lemma6AdmissiblePairs x m) s χ)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    (differentiable_eq21PairPoly x m χ).differentiableOn
  have hLq : DifferentiableOn ℂ
      (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro s hs
    have hre := hs.1
    have him := hs.2
    rw [hzre, hwre, uIcc_of_le hγα] at hre
    rw [hzim, hwim, uIcc_of_le (by linarith)] at him
    have habs : |s.im| ≤ T := abs_le.mpr ⟨by linarith [him.1], him.2⟩
    have hwidths := hwidth s.im habs
    have hsqrtpos : 0 < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.2 hlog
    have htwoDiv : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwoDiv] at hwidths
    have hhalfwidth : 1 / Real.sqrt (Real.log (x : ℝ)) <
        primitiveZeroFreeWidth data.cHeight data.cSiegel l s.im / 2 := by
      linarith
    have hhalf : 1 -
        primitiveZeroFreeWidth data.cHeight data.cSiegel l s.im / 2 < γ := by
      dsimp only [γ]
      linarith
    have hregion : 1 -
        primitiveZeroFreeWidth data.cHeight data.cSiegel l s.im < s.re := by
      have hwpos := primitiveZeroFreeWidth_pos data.cHeight_pos
        data.cSiegel_pos hl s.im
      exact one_sub_width_lt_of_half_width_le hwpos
        (hhalf.le.trans hre.1)
    have hne := data.nonvanishing l inferInstance χ hl hχ s hregion
    exact ((primitiveCharacter_differentiable_LFunction_deriv hl
        hχ).differentiableAt.div
      (primitiveCharacter_differentiable_LFunction hl hχ).differentiableAt
      hne).differentiableWithinAt
  have hdiff : DifferentiableOn ℂ F
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    unfold F eq21LogDerivIntegrand
    exact (((hxpow.differentiableOn.mul hk).mul hP).mul hLq).neg
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  rw [hzre, hwre, hzim, hwim] at hrect
  dsimp only [F] at hrect
  simpa only [γ, α, sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hrect

/-- Pointwise bound for the unsplit integrand on the shifted line
`γ = 1 - 1/sqrt(log x)`: the modulus of `x^s` is exactly `x^γ`, the kernel
contributes the quadratic decay, the pair polynomial its `γ`-majorant, and
`L'/L` the zero-free-region companion bound. -/
theorem norm_eq21LogDerivIntegrand_eq21Point_le_of_logDeriv
    {x m l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} {M : ℝ} (_hM : 0 ≤ M) (ν : ℝ)
    (hlogDeriv :
      ‖deriv (DirichletCharacter.LFunction χ)
          (lemma6Equation21Point x ν) /
        DirichletCharacter.LFunction χ (lemma6Equation21Point x ν)‖ ≤ M) :
    ‖eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ ≤
      2 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) * M *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 0 < x by omega)
  have ha0 : (0 : ℝ) < lemma6SmoothingScale (x : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hn3 : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hγ0 : (0 : ℝ) < 1 - 1 / Real.sqrt (Real.log (x : ℝ)) := by
    linarith
  have e_x : ‖(x : ℂ) ^ lemma6Equation21Point x ν‖ =
      (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) := by
    change ‖((x : ℝ) : ℂ) ^ lemma6Equation21Point x ν‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      lemma6Equation21Point_re]
  have e_K : ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6Equation21Point x ν)‖ ≤
      2 * ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
    have hk := norm_kernel_le_quadratic_inv
      (x := (x : ℝ))
      (σ := 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
      ha0 hn3 hγ0 ν
    have hγinv :
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))⁻¹ ≤ 2 := by
      have h := (inv_le_inv₀ hγ0
        (by norm_num : (0 : ℝ) < 1 / 2)).mpr hγpos
      rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at h
    exact hk.trans (mul_le_mul_of_nonneg_right hγinv (by positivity))
  have e_P : ‖lemma6PairDirichletPolynomial x
        (lemma6AdmissiblePairs x m) (lemma6Equation21Point x ν) χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^
            (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
          |Real.log ((x : ℝ) /
            ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
    have h := norm_eq21PairPoly_le (x := x) (m := m) χ
      (lemma6Equation21Point x ν)
    rwa [lemma6Equation21Point_re] at h
  unfold eq21LogDerivIntegrand
  simp only [norm_neg, norm_mul]
  calc
    ‖(x : ℂ) ^ lemma6Equation21Point x ν‖ *
          ‖lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6Equation21Point x ν)‖ *
          ‖lemma6PairDirichletPolynomial x
            (lemma6AdmissiblePairs x m)
            (lemma6Equation21Point x ν) χ‖ *
          ‖deriv (DirichletCharacter.LFunction χ)
              (lemma6Equation21Point x ν) /
            DirichletCharacter.LFunction χ
              (lemma6Equation21Point x ν)‖
        ≤ (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            (2 * ((1 +
              (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) *
            (∑ q ∈ lemma6AdmissiblePairs x m,
              ((q.1 * q.2 : ℕ) : ℝ) ^
                  (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
                |Real.log ((x : ℝ) /
                  ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) * M := by
          gcongr
          exact e_x.le
    _ = 2 * (x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) * M *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
          ring

/-- A height-uniform logarithmic-derivative majorant on the finite
equation-(21) rectangle. -/
noncomputable def eq21ClassicalLogDerivMajorant
    (data : PrimitiveZeroFreeRegionData) (l : ℕ) (T : ℝ) : ℝ :=
  data.cLogDeriv *
    ((l : ℝ) ^ ((1 : ℝ) / 300) +
      Real.log ((l : ℝ) * (T + 2)) + 1) ^ 2

theorem eq21ClassicalLogDerivMajorant_nonneg
    (data : PrimitiveZeroFreeRegionData) (l : ℕ) (T : ℝ) :
    0 ≤ eq21ClassicalLogDerivMajorant data l T := by
  unfold eq21ClassicalLogDerivMajorant
  exact mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _)

theorem norm_eq21LogDerivIntegrand_eq21Point_le_classical
    (data : PrimitiveZeroFreeRegionData)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    {T ν : ℝ} (_hT : 0 ≤ T) (hν : |ν| ≤ T)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      primitiveZeroFreeWidth data.cHeight data.cSiegel l ν) :
    ‖eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ ≤
      2 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        eq21ClassicalLogDerivMajorant data l T *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hwpos := primitiveZeroFreeWidth_pos data.cHeight_pos
    data.cSiegel_pos hl ν
  have hhalf : 1 -
      primitiveZeroFreeWidth data.cHeight data.cSiegel l ν / 2 ≤
      (lemma6Equation21Point x ν).re := by
    rw [lemma6Equation21Point_re]
    have htwo : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwo] at hwidth
    linarith
  have hhalf' : 1 - primitiveZeroFreeWidth data.cHeight data.cSiegel l
        (lemma6Equation21Point x ν).im / 2 ≤
      (lemma6Equation21Point x ν).re := by
    simpa only [lemma6Equation21Point_im] using hhalf
  have hraw := data.logDeriv_bound l inferInstance χ hl hχ
    (lemma6Equation21Point x ν) hhalf'
  have hraw' : ‖deriv (DirichletCharacter.LFunction χ)
          (lemma6Equation21Point x ν) /
        DirichletCharacter.LFunction χ
          (lemma6Equation21Point x ν)‖ ≤
      data.cLogDeriv *
        ((l : ℝ) ^ ((1 : ℝ) / 300) +
          Real.log ((l : ℝ) * (|ν| + 2)) + 1) ^ 2 := by
    simpa only [lemma6Equation21Point_im] using hraw
  have hargpos : 0 < (l : ℝ) * (|ν| + 2) := by positivity
  have hargle : (l : ℝ) * (|ν| + 2) ≤ (l : ℝ) * (T + 2) := by
    gcongr
  have hlogle : Real.log ((l : ℝ) * (|ν| + 2)) ≤
      Real.log ((l : ℝ) * (T + 2)) :=
    Real.log_le_log hargpos hargle
  have hbase0 : 0 ≤ (l : ℝ) ^ ((1 : ℝ) / 300) +
      Real.log ((l : ℝ) * (|ν| + 2)) + 1 := by
    have := primitiveZeroFreeHeightLog_pos hl ν
    positivity
  have hbasele : (l : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((l : ℝ) * (|ν| + 2)) + 1 ≤
      (l : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((l : ℝ) * (T + 2)) + 1 := by linarith
  have hM : ‖deriv (DirichletCharacter.LFunction χ)
          (lemma6Equation21Point x ν) /
        DirichletCharacter.LFunction χ
          (lemma6Equation21Point x ν)‖ ≤
      eq21ClassicalLogDerivMajorant data l T := by
    exact hraw'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbasele 2) data.cLogDeriv_pos.le)
  exact norm_eq21LogDerivIntegrand_eq21Point_le_of_logDeriv
    hx hxlog hγpos (eq21ClassicalLogDerivMajorant_nonneg data l T) ν hM

/-- The shifted vertical segment is bounded without extending it beyond
the classical zero-free region. -/
theorem norm_intervalIntegral_eq21Point_le_classical
    (data : PrimitiveZeroFreeRegionData)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ ν : ℝ, |ν| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        primitiveZeroFreeWidth data.cHeight data.cSiegel l ν) :
    ‖∫ ν : ℝ in (-T)..T,
        eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ ≤
      4 * T *
        ((x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          eq21ClassicalLogDerivMajorant data l T) := by
  let C : ℝ :=
    2 * (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
      (∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^
            (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
          |Real.log ((x : ℝ) /
            ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
      eq21ClassicalLogDerivMajorant data l T
  have hM0 := eq21ClassicalLogDerivMajorant_nonneg data l T
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmain : ‖∫ ν : ℝ in (-T)..T,
        eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖ ≤
      C * |T - (-T)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro ν hνmem
    rw [uIoc_of_le (by linarith)] at hνmem
    have hν : |ν| ≤ T := abs_le.mpr ⟨hνmem.1.le, hνmem.2⟩
    have hp := norm_eq21LogDerivIntegrand_eq21Point_le_classical
      (m := m) data hl hx hxlog hγpos hχ hT hν (hwidth ν hν)
    have hinv : ((1 +
        (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ ≤ 1 := by
      have hbase : (1 : ℝ) ≤
          (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2 := by
        nlinarith [sq_nonneg
          (ν / lemma6SmoothingScale (x : ℝ)),
          sq_nonneg (1 +
            (ν / lemma6SmoothingScale (x : ℝ)) ^ 2)]
      exact inv_le_one_of_one_le₀ hbase
    exact hp.trans (mul_le_of_le_one_right hC0 hinv)
  calc
    ‖∫ ν : ℝ in (-T)..T,
        eq21LogDerivIntegrand x m χ (lemma6Equation21Point x ν)‖
        ≤ C * |T - (-T)| := hmain
    _ = 4 * T *
        ((x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          eq21ClassicalLogDerivMajorant data l T) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]
      dsimp only [C]
      ring

/-- Uniform pointwise bound on either horizontal edge of the finite classical
rectangle.  The full kernel order supplies `x^(-1/10)`; the logarithmic
derivative is invoked only at heights at most `T`. -/
theorem norm_eq21LogDerivIntegrand_horizontal_le_classical
    (data : PrimitiveZeroFreeRegionData)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    {T τ σ : ℝ} (_hT : 0 ≤ T) (hτ : |τ| ≤ T)
    (hσ : σ ∈ Set.Icc
      (1 - 1 / Real.sqrt (Real.log (x : ℝ)))
      (1 + 1 / Real.log (x : ℝ)))
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      primitiveZeroFreeWidth data.cHeight data.cSiegel l τ)
    (hden : (x : ℝ) ^ ((1 : ℝ) / 10) *
        (1 + (τ / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2 ≤
      (1 + (τ / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
        (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2)) :
    ‖eq21LogDerivIntegrand x m χ
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (2 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          eq21ClassicalLogDerivMajorant data l T *
          lemma6SmoothingScale (x : ℝ) ^ 4) *
        ((1 + τ ^ 2) ^ 2)⁻¹ := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 0 < x by omega)
  have hxone : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have ha0 : (0 : ℝ) < lemma6SmoothingScale (x : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have ha1 : (1 : ℝ) ≤ lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn1 : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    linarith
  have hσhalf : (1 : ℝ) / 2 ≤ σ := hγpos.trans hσ.1
  have hσpos : 0 < σ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hσhalf
  have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
  have hxpow : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Real.exp 1 * (x : ℝ) := by
    have hxne : (x : ℝ) ≠ 1 := by
      exact_mod_cast (show x ≠ 1 by omega)
    change ‖((x : ℝ) : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hre]
    calc
      (x : ℝ) ^ σ ≤ (x : ℝ) ^ (1 + 1 / Real.log (x : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hxone hσ.2
      _ = Real.exp 1 * (x : ℝ) := by
        rw [Real.rpow_add hxpos, Real.rpow_one,
          show (1 : ℝ) / Real.log (x : ℝ) =
            (Real.log (x : ℝ))⁻¹ from one_div _,
          Real.rpow_inv_log hxpos hxne]
        ring
  have hkernel : ‖lemma6SmoothingMellinKernel (x : ℝ)
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
        (lemma6SmoothingScale (x : ℝ) ^ 4 *
          ((1 + τ ^ 2) ^ 2)⁻¹) := by
    have hk := norm_kernel_le_quadratic_inv_mul_rpow_neg
      hxpos ha0 hn1 hσhalf τ hden
    have hq := eq21_quarticInv_le_a4_sq ha1 τ
    calc
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
          ≤ 2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
              ((1 + (τ / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
            simpa only [neg_div] using hk
      _ ≤ 2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          (lemma6SmoothingScale (x : ℝ) ^ 4 *
            ((1 + τ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
  have hpair : ‖lemma6PairDirichletPolynomial x
        (lemma6AdmissiblePairs x m)
        ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^
            (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
          |Real.log ((x : ℝ) /
            ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
    calc
      ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
          ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤
        ∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(((σ : ℂ) + (τ : ℂ) * Complex.I).re)) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ :=
        norm_eq21PairPoly_le (x := x) (m := m) χ _
      _ ≤ _ := by
        apply eq21Pair_rpow_sum_antitone
        rw [hre]
        exact hσ.1
  have hhalf : 1 - primitiveZeroFreeWidth data.cHeight data.cSiegel l τ / 2 ≤
      σ := by
    have htwo : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwo] at hwidth
    linarith [hσ.1]
  have hhalf' : 1 - primitiveZeroFreeWidth data.cHeight data.cSiegel l
        (((σ : ℂ) + (τ : ℂ) * Complex.I).im) / 2 ≤
      ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by
    simpa only [hre, him] using hhalf
  have hraw := data.logDeriv_bound l inferInstance χ hl hχ
    ((σ : ℂ) + (τ : ℂ) * Complex.I) hhalf'
  have hraw' : ‖deriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + (τ : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      data.cLogDeriv *
        ((l : ℝ) ^ ((1 : ℝ) / 300) +
          Real.log ((l : ℝ) * (|τ| + 2)) + 1) ^ 2 := by
    simpa only [him] using hraw
  have hargpos : 0 < (l : ℝ) * (|τ| + 2) := by positivity
  have hargle : (l : ℝ) * (|τ| + 2) ≤ (l : ℝ) * (T + 2) := by gcongr
  have hlogle : Real.log ((l : ℝ) * (|τ| + 2)) ≤
      Real.log ((l : ℝ) * (T + 2)) :=
    Real.log_le_log hargpos hargle
  have hbase0 : 0 ≤ (l : ℝ) ^ ((1 : ℝ) / 300) +
      Real.log ((l : ℝ) * (|τ| + 2)) + 1 := by
    have := primitiveZeroFreeHeightLog_pos hl τ
    positivity
  have hbasele : (l : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((l : ℝ) * (|τ| + 2)) + 1 ≤
      (l : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((l : ℝ) * (T + 2)) + 1 := by linarith
  have hLbound : ‖deriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + (τ : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      eq21ClassicalLogDerivMajorant data l T :=
    hraw'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbasele 2) data.cLogDeriv_pos.le)
  unfold eq21LogDerivIntegrand
  simp only [norm_neg, norm_mul]
  have hprod : ‖(x : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ)
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
        ‖lemma6PairDirichletPolynomial x (lemma6AdmissiblePairs x m)
          ((σ : ℂ) + (τ : ℂ) * Complex.I) χ‖ *
        ‖deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (τ : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ
            ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (Real.exp 1 * (x : ℝ)) *
        (2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          (lemma6SmoothingScale (x : ℝ) ^ 4 *
            ((1 + τ ^ 2) ^ 2)⁻¹)) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        eq21ClassicalLogDerivMajorant data l T := by
    gcongr
  exact hprod.trans_eq (by ring)

/-- Each horizontal side of the finite rectangle has length at most one and
inherits the pointwise full-kernel saving. -/
theorem norm_intervalIntegral_horizontal_le_classical
    (data : PrimitiveZeroFreeRegionData)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    {T τ : ℝ} (hT : 0 ≤ T) (hτ : |τ| = T)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      primitiveZeroFreeWidth data.cHeight data.cSiegel l τ)
    (hden : (x : ℝ) ^ ((1 : ℝ) / 10) *
        (1 + (τ / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2 ≤
      (1 + (τ / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
        (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2)) :
    ‖∫ σ : ℝ in
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))..
          (1 + 1 / Real.log (x : ℝ)),
        eq21LogDerivIntegrand x m χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      2 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        eq21ClassicalLogDerivMajorant data l T *
        lemma6SmoothingScale (x : ℝ) ^ 4 := by
  let C : ℝ :=
    2 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
      (∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^
            (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
          |Real.log ((x : ℝ) /
            ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
      eq21ClassicalLogDerivMajorant data l T *
      lemma6SmoothingScale (x : ℝ) ^ 4
  have hC0 : 0 ≤ C := by
    have hM0 := eq21ClassicalLogDerivMajorant_nonneg data l T
    dsimp only [C]
    positivity
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hinvlog : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
  have hinvsqrt : 0 ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by positivity
  have hwidthOne :
      |(1 + 1 / Real.log (x : ℝ)) -
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| ≤ 1 := by
    have hsqrt : 1 / Real.sqrt (Real.log (x : ℝ)) ≤ 1 / 2 := by
      linarith [hγpos]
    have hlog : 1 / Real.log (x : ℝ) ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num) hxlog
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hmain : ‖∫ σ : ℝ in
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))..
          (1 + 1 / Real.log (x : ℝ)),
        eq21LogDerivIntegrand x m χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      C * |(1 + 1 / Real.log (x : ℝ)) -
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσmem
    have hγα : 1 - 1 / Real.sqrt (Real.log (x : ℝ)) ≤
        1 + 1 / Real.log (x : ℝ) := by linarith
    have hσ : σ ∈ Set.Icc
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))
        (1 + 1 / Real.log (x : ℝ)) := by
      rw [← uIcc_of_le hγα]
      exact uIoc_subset_uIcc hσmem
    have hp := norm_eq21LogDerivIntegrand_horizontal_le_classical
      (m := m) data hl hx hxlog hγpos hχ hT hτ.le hσ hwidth hden
    have hinv : ((1 + τ ^ 2) ^ 2)⁻¹ ≤ 1 := by
      have hb : (1 : ℝ) ≤ (1 + τ ^ 2) ^ 2 := by
        nlinarith [sq_nonneg τ, sq_nonneg (1 + τ ^ 2)]
      exact inv_le_one_of_one_le₀ hb
    exact hp.trans (mul_le_of_le_one_right hC0 hinv)
  exact hmain.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hwidthOne hC0)

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

/-- On the `alpha`-line beyond the finite contour height, the unused exact
kernel exponent supplies the fixed saving `x^(-1/10)` in addition to the
quadratic integrable envelope. -/
theorem norm_eq21LogDerivIntegrand_alphaPoint_le_large_height
    {x m l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (χ : DirichletCharacter ℂ l) (ν : ℝ)
    (hden : (x : ℝ) ^ ((1 : ℝ) / 10) *
        (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2 ≤
      (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
        (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2)) :
    ‖eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
      (8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          lemma6SmoothingScale (x : ℝ) ^ 4) *
        ((1 + ν ^ 2) ^ 2)⁻¹ := by
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 0 < x by omega)
  have ha0 : (0 : ℝ) < lemma6SmoothingScale (x : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hn1 : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    linarith
  have hαhalf : (1 : ℝ) / 2 ≤ 1 + 1 / Real.log (x : ℝ) := by
    have : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have e_x : ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ =
      Real.exp 1 * (x : ℝ) := norm_nat_cpow_eq21AlphaPoint hx ν
  have e_K : ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x ν)‖ ≤
      2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
        ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹ := by
    change ‖lemma6SmoothingMellinKernel (x : ℝ)
        (((1 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) +
          (ν : ℂ) * Complex.I)‖ ≤ _
    simpa only [neg_div] using
      (norm_kernel_le_quadratic_inv_mul_rpow_neg hxpos ha0 hn1
        hαhalf ν hden)
  have e_P : ‖lemma6PairDirichletPolynomial x
        (lemma6AdmissiblePairs x m) (lemma6AlphaPoint x ν) χ‖ ≤
      ∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^
            (-(1 + 1 / Real.log (x : ℝ))) *
          |Real.log ((x : ℝ) /
            ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ := by
    have h := norm_eq21PairPoly_le (x := x) (m := m) χ
      (lemma6AlphaPoint x ν)
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
  have hraw : ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ *
        ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x ν)‖ *
        ‖lemma6PairDirichletPolynomial x
          (lemma6AdmissiblePairs x m) (lemma6AlphaPoint x ν) χ‖ *
        ‖deriv (DirichletCharacter.LFunction χ)
            (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ
            (lemma6AlphaPoint x ν)‖ ≤
      Real.exp 1 * (x : ℝ) *
        (2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 + 1 / Real.log (x : ℝ))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        (4 * Real.log (x : ℝ) ^ 2) := by
    gcongr
    exact e_x.le
  refine hraw.trans ?_
  have hquartic := eq21_quarticInv_le_a4_sq
    (show 1 ≤ lemma6SmoothingScale (x : ℝ) by
      unfold lemma6SmoothingScale
      exact Real.one_le_rpow (by linarith) (by norm_num)) ν
  calc
    Real.exp 1 * (x : ℝ) *
        (2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          ((1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2)⁻¹) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 + 1 / Real.log (x : ℝ))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        (4 * Real.log (x : ℝ) ^ 2)
      ≤ Real.exp 1 * (x : ℝ) *
        (2 * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          (lemma6SmoothingScale (x : ℝ) ^ 4 *
            ((1 + ν ^ 2) ^ 2)⁻¹)) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 + 1 / Real.log (x : ℝ))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        (4 * Real.log (x : ℝ) ^ 2) := by gcongr
    _ = (8 * Real.exp 1 * (x : ℝ) *
          (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          lemma6SmoothingScale (x : ℝ) ^ 4) *
        ((1 + ν ^ 2) ^ 2)⁻¹ := by ring

/-- Integrability on the original `alpha` line uses only absolute
convergence in `re s > 1`; it is independent of the zero-free region. -/
theorem integrable_eq21LogDerivIntegrand_alphaPoint_classical
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive) :
    Integrable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)) := by
  have hmeas : AEStronglyMeasurable (fun ν : ℝ =>
      eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)) := by
    have hcont : Continuous (lemma6AlphaPoint x) := by
      unfold lemma6AlphaPoint
      fun_prop
    have hrange : ∀ ν : ℝ, lemma6AlphaPoint x ν ∈
        {s : ℂ | 1 < s.re} := by
      intro ν
      change 1 < (lemma6AlphaPoint x ν).re
      exact one_lt_lemma6AlphaPoint_re hx ν
    exact ((differentiableOn_eq21LogDerivIntegrand_one_lt_re
      (m := m) hl hx hχ).continuousOn.comp_continuous
        hcont hrange).aestronglyMeasurable
  apply (integrable_inv_one_add_sq.const_mul _).mono' hmeas
  filter_upwards with ν
  exact norm_eq21LogDerivIntegrand_alphaPoint_le
    (m := m) hx hxlog ha1 χ ν

/-- The part of the original `alpha` line outside the finite rectangle is
controlled directly by the full smoothing-kernel exponent.  No zero-free
region is used on this tail. -/
theorem norm_integral_alphaPoint_compl_Ioc_le_classical
    {x m l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (χ : DirichletCharacter ℂ l) {T : ℝ} (hT : 0 ≤ T)
    (hden : ∀ ν : ℝ, T ≤ |ν| →
      (x : ℝ) ^ ((1 : ℝ) / 10) *
          (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2 ≤
        (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
          (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2)) :
    ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
      (8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          lemma6SmoothingScale (x : ℝ) ^ 4) * Real.pi := by
  let C : ℝ :=
    8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
      Real.log (x : ℝ) ^ 2 *
      (∑ q ∈ lemma6AdmissiblePairs x m,
        ((q.1 * q.2 : ℕ) : ℝ) ^
            (-(1 + 1 / Real.log (x : ℝ))) *
          |Real.log ((x : ℝ) /
            ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
      lemma6SmoothingScale (x : ℝ) ^ 4
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hg : Integrable (fun ν : ℝ => C * (1 + ν ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  have hmain : ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
      ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, C * (1 + ν ^ 2)⁻¹ := by
    apply MeasureTheory.norm_integral_le_of_norm_le hg.integrableOn
    filter_upwards [MeasureTheory.ae_restrict_mem
      measurableSet_Ioc.compl] with ν hνmem
    have hνlarge : T ≤ |ν| := by
      rw [Set.mem_compl_iff, Set.mem_Ioc] at hνmem
      by_cases hleft : ν ≤ -T
      · have : T ≤ -ν := by linarith
        exact this.trans_eq (abs_of_nonpos (by linarith)).symm
      · have hright : T < ν := by
          by_contra hnot
          exact hνmem ⟨lt_of_not_ge hleft, le_of_not_gt hnot⟩
        exact hright.le.trans (le_abs_self ν)
    have hp := norm_eq21LogDerivIntegrand_alphaPoint_le_large_height
      (m := m) hx hxlog χ ν (hden ν hνlarge)
    have hinv : ((1 + ν ^ 2) ^ 2)⁻¹ ≤ (1 + ν ^ 2)⁻¹ := by
      have hu : (1 : ℝ) ≤ 1 + ν ^ 2 := by nlinarith [sq_nonneg ν]
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
        (by nlinarith [sq_nonneg (1 + ν ^ 2)])
    exact hp.trans (mul_le_mul_of_nonneg_left hinv hC0)
  refine hmain.trans ?_
  have hrestrict :
      (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, C * (1 + ν ^ 2)⁻¹) ≤
        ∫ ν : ℝ, C * (1 + ν ^ 2)⁻¹ := by
    exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun ν => by positivity)) hg
  calc
    (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, C * (1 + ν ^ 2)⁻¹)
        ≤ ∫ ν : ℝ, C * (1 + ν ^ 2)⁻¹ := hrestrict
    _ = C * Real.pi := by
      rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
    _ = (8 * Real.exp 1 * (x : ℝ) *
          (x : ℝ) ^ ((-1 : ℝ) / 10) * Real.log (x : ℝ) ^ 2 *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          lemma6SmoothingScale (x : ℝ) ^ 4) * Real.pi := by rfl

/-- Finite-contour replacement for the former equality of two improper
vertical integrals.  Only the `gamma` segment is moved; the original-line
tail and both horizontal sides are retained as explicit errors. -/
theorem norm_integral_alphaPoint_le_finite_classical
    (data : PrimitiveZeroFreeRegionData)
    {x m l : ℕ} [NeZero l] (hl : 2 ≤ l) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ))
    (ha1 : 1 ≤ lemma6SmoothingScale (x : ℝ))
    (hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ l} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ ν : ℝ, |ν| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        primitiveZeroFreeWidth data.cHeight data.cSiegel l ν)
    (hden : ∀ ν : ℝ, T ≤ |ν| →
      (x : ℝ) ^ ((1 : ℝ) / 10) *
          (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^ 2 ≤
        (1 + (ν / lemma6SmoothingScale (x : ℝ)) ^ 2) ^
          (((lemma6SmoothingOrder (x : ℝ) + 1 : ℕ) : ℝ) / 2)) :
    ‖∫ ν : ℝ,
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
      4 * T *
        ((x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          eq21ClassicalLogDerivMajorant data l T) +
      4 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        eq21ClassicalLogDerivMajorant data l T *
        lemma6SmoothingScale (x : ℝ) ^ 4 +
      (8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          lemma6SmoothingScale (x : ℝ) ^ 4) * Real.pi := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := eq21LogDerivIntegrand x m χ
  let A : ℂ := ∫ ν : ℝ in (-T)..T,
    F ((α : ℂ) + (ν : ℂ) * Complex.I)
  let G : ℂ := ∫ ν : ℝ in (-T)..T,
    F ((γ : ℂ) + (ν : ℂ) * Complex.I)
  let bot : ℂ := ∫ σ : ℝ in γ..α,
    F ((σ : ℂ) - (T : ℂ) * Complex.I)
  let top : ℂ := ∫ σ : ℝ in γ..α,
    F ((σ : ℂ) + (T : ℂ) * Complex.I)
  let tail : ℂ := ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
    F ((α : ℂ) + (ν : ℂ) * Complex.I)
  have hαI := integrable_eq21LogDerivIntegrand_alphaPoint_classical
    (m := m) hl hx hxlog ha1 hχ
  have hsplit : A + tail = ∫ ν : ℝ,
      eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν) := by
    have hs := MeasureTheory.integral_add_compl
      (s := Set.Ioc (-T) T) measurableSet_Ioc hαI
    rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at hs
    simpa only [A, tail, F, α, lemma6AlphaPoint] using hs
  have hrect : bot - top + Complex.I • A - Complex.I • G = 0 := by
    simpa only [bot, top, A, G, F, γ, α] using
      (eq21LogDeriv_finite_rectangle_classical (m := m) data hl hx hxlog
        hγpos hχ hT hwidth)
  have hIA : Complex.I • A = Complex.I • G - bot + top := by
    linear_combination hrect
  have hAG : ‖A‖ ≤ ‖G‖ + ‖bot‖ + ‖top‖ := by
    calc
      ‖A‖ = ‖Complex.I • A‖ := by simp
      _ = ‖Complex.I • G - bot + top‖ := congrArg norm hIA
      _ ≤ ‖Complex.I • G - bot‖ + ‖top‖ := norm_add_le _ _
      _ ≤ (‖Complex.I • G‖ + ‖bot‖) + ‖top‖ :=
        by linarith [norm_sub_le (Complex.I • G) bot]
      _ = ‖G‖ + ‖bot‖ + ‖top‖ := by simp
  have hG : ‖G‖ ≤
      4 * T *
        ((x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          eq21ClassicalLogDerivMajorant data l T) := by
    simpa only [G, F, γ, lemma6Equation21Point] using
      (norm_intervalIntegral_eq21Point_le_classical (m := m) data hl hx
        hxlog hγpos hχ hT hwidth)
  have htop : ‖top‖ ≤
      2 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        eq21ClassicalLogDerivMajorant data l T *
        lemma6SmoothingScale (x : ℝ) ^ 4 := by
    simpa only [top, F, γ, α, abs_of_nonneg hT] using
      (norm_intervalIntegral_horizontal_le_classical (m := m) data hl hx
        hxlog hγpos hχ hT (abs_of_nonneg hT)
        (hwidth T (by rw [abs_of_nonneg hT]))
        (hden T (by rw [abs_of_nonneg hT])))
  have hbot : ‖bot‖ ≤
      2 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
        (∑ q ∈ lemma6AdmissiblePairs x m,
          ((q.1 * q.2 : ℕ) : ℝ) ^
              (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
            |Real.log ((x : ℝ) /
              ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
        eq21ClassicalLogDerivMajorant data l T *
        lemma6SmoothingScale (x : ℝ) ^ 4 := by
    have hb := norm_intervalIntegral_horizontal_le_classical (m := m)
      data hl hx hxlog hγpos hχ hT
      (show |-T| = T by rw [abs_neg, abs_of_nonneg hT])
      (hwidth (-T) (by rw [abs_neg, abs_of_nonneg hT]))
      (hden (-T) (by rw [abs_neg, abs_of_nonneg hT]))
    simpa only [bot, F, γ, α, Complex.ofReal_neg, neg_mul,
      sub_eq_add_neg] using hb
  have htail : ‖tail‖ ≤
      (8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          lemma6SmoothingScale (x : ℝ) ^ 4) * Real.pi := by
    simpa only [tail, F, α, lemma6AlphaPoint] using
      (norm_integral_alphaPoint_compl_Ioc_le_classical (m := m)
        hx hxlog χ hT hden)
  calc
    ‖∫ ν : ℝ,
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖
        = ‖A + tail‖ := congrArg norm hsplit.symm
    _ ≤ ‖A‖ + ‖tail‖ := norm_add_le _ _
    _ ≤ (‖G‖ + ‖bot‖ + ‖top‖) + ‖tail‖ :=
      by linarith
    _ ≤ (4 * T *
          ((x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            (∑ q ∈ lemma6AdmissiblePairs x m,
              ((q.1 * q.2 : ℕ) : ℝ) ^
                  (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
                |Real.log ((x : ℝ) /
                  ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
            eq21ClassicalLogDerivMajorant data l T) +
        4 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 - 1 / Real.sqrt (Real.log (x : ℝ)))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          eq21ClassicalLogDerivMajorant data l T *
          lemma6SmoothingScale (x : ℝ) ^ 4) +
        (8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 *
          (∑ q ∈ lemma6AdmissiblePairs x m,
            ((q.1 * q.2 : ℕ) : ℝ) ^
                (-(1 + 1 / Real.log (x : ℝ))) *
              |Real.log ((x : ℝ) /
                ((q.1 * q.2 : ℕ) : ℝ))|⁻¹) *
          lemma6SmoothingScale (x : ℝ) ^ 4) * Real.pi := by
      linarith [hG, hbot, htop, htail]
    _ = _ := by ring

/-- At the polylogarithmic contour height and for the conductors occurring in
equation (21), the classical logarithmic-derivative majorant costs only two
powers of `log x`. -/
theorem eq21ClassicalLogDerivMajorant_height_le
    (data : PrimitiveZeroFreeRegionData) {x l : ℕ}
    (hxlog : 4 ≤ Real.log (x : ℝ)) (hl : 2 ≤ l)
    (hl100 : (l : ℝ) ≤ Real.log (x : ℝ) ^ 100) :
    eq21ClassicalLogDerivMajorant data l (lemma6Equation21Height x) ≤
      12996 * data.cLogDeriv * Real.log (x : ℝ) ^ 2 := by
  let L : ℝ := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hlpow : (l : ℝ) ^ ((1 : ℝ) / 300) ≤ L := by
    calc
      (l : ℝ) ^ ((1 : ℝ) / 300) ≤ (L ^ 100) ^ ((1 : ℝ) / 300) :=
        Real.rpow_le_rpow hlpos.le hl100 (by norm_num)
      _ = L ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast L 100, ← Real.rpow_mul hLpos.le]
        congr 1
        norm_num
      _ ≤ L ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
      _ = L := Real.rpow_one L
  have hlogL : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hlogl : Real.log (l : ℝ) ≤ 100 * Real.log L := by
    have hle := Real.log_le_log hlpos hl100
    rw [Real.log_pow] at hle
    exact hle
  have hTtwo : L ^ 10 + 2 ≤ 3 * L ^ 10 := by
    have : (1 : ℝ) ≤ L ^ 10 := one_le_pow₀ hLone
    linarith
  have hlogTtwo : Real.log (L ^ 10 + 2) ≤ 12 * L := by
    have hpos : 0 < L ^ 10 + 2 := by positivity
    have hmono : Real.log (L ^ 10 + 2) ≤ Real.log (3 * L ^ 10) :=
      Real.log_le_log hpos hTtwo
    have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
      nlinarith [Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 3 by norm_num)]
    have heq : Real.log (3 * L ^ 10) =
        Real.log 3 + 10 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    rw [heq] at hmono
    linarith
  have hlogarg : Real.log ((l : ℝ) *
        (lemma6Equation21Height x + 2)) ≤ 112 * L := by
    have heq : Real.log ((l : ℝ) *
          (lemma6Equation21Height x + 2)) =
        Real.log (l : ℝ) + Real.log (L ^ 10 + 2) := by
      have hh : 0 < lemma6Equation21Height x + 2 := by
        unfold lemma6Equation21Height
        positivity
      rw [Real.log_mul hlpos.ne' hh.ne']
      rfl
    rw [heq]
    linarith
  have hbase : (l : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((l : ℝ) * (lemma6Equation21Height x + 2)) + 1 ≤
      114 * L := by linarith
  have hbase0 : 0 ≤ (l : ℝ) ^ ((1 : ℝ) / 300) +
      Real.log ((l : ℝ) * (lemma6Equation21Height x + 2)) + 1 := by
    have hheight0 : 0 ≤ lemma6Equation21Height x := by
      unfold lemma6Equation21Height
      positivity
    have := primitiveZeroFreeHeightLog_pos hl (lemma6Equation21Height x)
    rw [abs_of_nonneg hheight0] at this
    have hrpow : 0 ≤ (l : ℝ) ^ ((1 : ℝ) / 300) :=
      Real.rpow_nonneg (by positivity) _
    linarith
  have hsquare : ((l : ℝ) ^ ((1 : ℝ) / 300) +
        Real.log ((l : ℝ) * (lemma6Equation21Height x + 2)) + 1) ^ 2 ≤
      (114 * L) ^ 2 := pow_le_pow_left₀ hbase0 hbase 2
  unfold eq21ClassicalLogDerivMajorant
  calc
    data.cLogDeriv * ((l : ℝ) ^ ((1 : ℝ) / 300) +
          Real.log ((l : ℝ) * (lemma6Equation21Height x + 2)) + 1) ^ 2
        ≤ data.cLogDeriv * (114 * L) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare data.cLogDeriv_pos.le
    _ = 12996 * data.cLogDeriv * Real.log (x : ℝ) ^ 2 := by
      dsimp only [L]
      ring

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
  obtain ⟨data⟩ := hzf
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev100 : ∀ᶠ x : ℕ in atTop, (100 : ℝ) ≤ Real.log (x : ℝ) :=
    hlogT.eventually (eventually_ge_atTop 100)
  have hevwidth := eventually_two_div_sqrt_log_lt_primitiveZeroFreeWidth
    data.cHeight_pos data.cSiegel_pos
  have hevden := eventually_large_height_kernel_denominator
  refine ⟨1000000 * (data.cLogDeriv + 1), by
    nlinarith [data.cLogDeriv_pos], ?_⟩
  filter_upwards [eventually_ge_atTop 2, hev100, hevwidth, hevden] with
    x hx2 hxlog100 hwidthAll hden
  intro m l _ χ hl2 hl100 hχ
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hlogpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hxlog4 : 4 ≤ Real.log (x : ℝ) := by linarith
  have hxlog3 : 3 ≤ Real.log (x : ℝ) := by linarith
  have ha1 : (1 : ℝ) ≤ lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.one_le_rpow hlog1 (by norm_num)
  have hT0 : 0 ≤ lemma6Equation21Height x := by
    unfold lemma6Equation21Height
    positivity
  have hγpos : (1 : ℝ) / 2 ≤ 1 - 1 / Real.sqrt (Real.log (x : ℝ)) := by
    have hsqrt : (2 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← hsqrt4]
      exact Real.sqrt_le_sqrt (by linarith)
    have hinv : 1 / Real.sqrt (Real.log (x : ℝ)) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hsqrt
    linarith
  have hfinite := norm_integral_alphaPoint_le_finite_classical
    (m := m) data hl2 hx2 hxlog3 ha1 hγpos hχ hT0
    (fun ν hν => hwidthAll l hl2 hl100 ν hν) hden
  -- abbreviations
  set γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ)) with hγdef
  set a : ℝ := lemma6SmoothingScale (x : ℝ) with hadef
  set T : ℝ := lemma6Equation21Height x with hTdef
  set Pγ : ℝ := ∑ q ∈ lemma6AdmissiblePairs x m,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-γ) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hPγdef
  set Pα : ℝ := ∑ q ∈ lemma6AdmissiblePairs x m,
    ((q.1 * q.2 : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (x : ℝ))) *
      |Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ))|⁻¹ with hPαdef
  set M : ℝ := eq21ClassicalLogDerivMajorant data l T with hMdef
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
  have hPγ0 : 0 ≤ Pγ := by rw [hPγdef]; positivity
  have hPα0 : 0 ≤ Pα := by rw [hPαdef]; positivity
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact eq21ClassicalLogDerivMajorant_nonneg data l T
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
  have hαγ : γ ≤ 1 + 1 / Real.log (x : ℝ) := by
    rw [hγdef]
    have h1 : 0 ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by positivity
    have h2 : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hPαPγ : Pα ≤ Pγ := by
    rw [hPαdef, hPγdef]
    exact eq21Pair_rpow_sum_antitone hαγ
  have hMle : M ≤ 12996 * data.cLogDeriv *
      Real.log (x : ℝ) ^ 2 := by
    rw [hMdef, hTdef]
    exact eq21ClassicalLogDerivMajorant_height_le data hxlog4 hl2 hl100
  -- the smoothing scale costs fewer than five powers of `log x`
  have ha4 : a ^ 4 = (Real.log (x : ℝ)) ^ ((4.4 : ℝ)) := by
    rw [hadef]
    unfold lemma6SmoothingScale
    rw [← Real.rpow_natCast ((Real.log (x : ℝ)) ^ (1.1 : ℝ)) 4,
      ← Real.rpow_mul hlogpos.le]
    congr 1
    norm_num
  have ha4le : a ^ 4 ≤ Real.log (x : ℝ) ^ 5 := by
    rw [ha4, ← Real.rpow_natCast (Real.log (x : ℝ)) 5]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
  have hγ09 : (9 : ℝ) / 10 ≤ γ := by
    have hsqrt : (10 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have hsqrt100 : Real.sqrt (100 : ℝ) = 10 := by
        rw [show (100 : ℝ) = 10 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← hsqrt100]
      exact Real.sqrt_le_sqrt hxlog100
    have hinv : 1 / Real.sqrt (Real.log (x : ℝ)) ≤ 1 / 10 :=
      one_div_le_one_div_of_le (by norm_num) hsqrt
    rw [hγdef]
    linarith
  have hxdecay : (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) ≤
      (x : ℝ) ^ γ := by
    have heq : (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) =
        (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc
        (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) =
            (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) := by
              rw [Real.rpow_one]
        _ = (x : ℝ) ^ ((1 : ℝ) + ((-1 : ℝ) / 10)) := by
              rw [Real.rpow_add hxpos]
        _ = (x : ℝ) ^ ((9 : ℝ) / 10) := by norm_num
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hγ09
  have hxPfull : (x : ℝ) ^ γ * Pγ ≤ 3 * S :=
    hxP.trans (mul_le_mul_of_nonneg_left hS1S (by norm_num))
  have hxPα : (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) * Pα ≤
      3 * S := by
    calc
      (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) * Pα
          ≤ (x : ℝ) ^ γ * Pα :=
        mul_le_mul_of_nonneg_right hxdecay hPα0
      _ ≤ (x : ℝ) ^ γ * Pγ :=
        mul_le_mul_of_nonneg_left hPαPγ (Real.rpow_nonneg hxpos.le _)
      _ ≤ 3 * S := hxPfull
  have hxPγdecay : (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) * Pγ ≤
      3 * S :=
    (mul_le_mul_of_nonneg_right hxdecay hPγ0).trans hxPfull
  have hL7 : Real.log (x : ℝ) ^ 7 ≤ Real.log (x : ℝ) ^ 90 :=
    pow_le_pow_right₀ hlog1 (by omega)
  have hL12 : Real.log (x : ℝ) ^ 12 ≤ Real.log (x : ℝ) ^ 90 :=
    pow_le_pow_right₀ hlog1 (by omega)
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hcLog0 : 0 ≤ data.cLogDeriv := data.cLogDeriv_pos.le
  have hfinite' : ‖∫ ν : ℝ,
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
      4 * T * ((x : ℝ) ^ γ * Pγ * M) +
        4 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Pγ * M * a ^ 4 +
        (8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 * Pα * a ^ 4) * Real.pi := by
    simpa only [T, γ, Pγ, Pα, M, a] using hfinite
  have hB1 : 4 * T * ((x : ℝ) ^ γ * Pγ * M) ≤
      155952 * data.cLogDeriv * Real.log (x : ℝ) ^ 90 * S := by
    calc
      4 * T * ((x : ℝ) ^ γ * Pγ * M)
          ≤ 4 * Real.log (x : ℝ) ^ 10 *
              ((3 * S) *
                (12996 * data.cLogDeriv * Real.log (x : ℝ) ^ 2)) := by
            rw [hTdef]
            unfold lemma6Equation21Height
            gcongr
      _ = 155952 * data.cLogDeriv * Real.log (x : ℝ) ^ 12 * S := by ring
      _ ≤ 155952 * data.cLogDeriv * Real.log (x : ℝ) ^ 90 * S := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL12
            (mul_nonneg (by norm_num) hcLog0)) hSnn
  have hB2 : 4 * Real.exp 1 * (x : ℝ) *
        (x : ℝ) ^ ((-1 : ℝ) / 10) * Pγ * M * a ^ 4 ≤
      467856 * data.cLogDeriv * Real.log (x : ℝ) ^ 90 * S := by
    calc
      4 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Pγ * M * a ^ 4
          = 4 * Real.exp 1 *
              ((x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) * Pγ) *
              M * a ^ 4 := by ring
      _ ≤ 4 * 3 * (3 * S) *
              (12996 * data.cLogDeriv * Real.log (x : ℝ) ^ 2) *
              Real.log (x : ℝ) ^ 5 := by gcongr
      _ = 467856 * data.cLogDeriv * Real.log (x : ℝ) ^ 7 * S := by ring
      _ ≤ 467856 * data.cLogDeriv * Real.log (x : ℝ) ^ 90 * S := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL7
            (mul_nonneg (by norm_num) hcLog0)) hSnn
  have hB3 : (8 * Real.exp 1 * (x : ℝ) *
        (x : ℝ) ^ ((-1 : ℝ) / 10) * Real.log (x : ℝ) ^ 2 *
        Pα * a ^ 4) * Real.pi ≤
      288 * Real.log (x : ℝ) ^ 90 * S := by
    calc
      (8 * Real.exp 1 * (x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) *
          Real.log (x : ℝ) ^ 2 * Pα * a ^ 4) * Real.pi
          = (8 * Real.exp 1 *
              ((x : ℝ) * (x : ℝ) ^ ((-1 : ℝ) / 10) * Pα) *
              Real.log (x : ℝ) ^ 2 * a ^ 4) * Real.pi := by ring
      _ ≤ (8 * 3 * (3 * S) * Real.log (x : ℝ) ^ 2 *
              Real.log (x : ℝ) ^ 5) * 4 := by gcongr
      _ = 288 * Real.log (x : ℝ) ^ 7 * S := by ring
      _ ≤ 288 * Real.log (x : ℝ) ^ 90 * S := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL7 (by norm_num)) hSnn
  have hnorm : ‖∫ ν : ℝ,
        eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ ≤
      (623808 * data.cLogDeriv + 288) *
        Real.log (x : ℝ) ^ 90 * S := by
    calc
      ‖∫ ν : ℝ,
          eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖
          ≤ 4 * T * ((x : ℝ) ^ γ * Pγ * M) +
              4 * Real.exp 1 * (x : ℝ) *
                (x : ℝ) ^ ((-1 : ℝ) / 10) * Pγ * M * a ^ 4 +
              (8 * Real.exp 1 * (x : ℝ) *
                (x : ℝ) ^ ((-1 : ℝ) / 10) * Real.log (x : ℝ) ^ 2 *
                Pα * a ^ 4) * Real.pi := hfinite'
      _ ≤ 155952 * data.cLogDeriv * Real.log (x : ℝ) ^ 90 * S +
          467856 * data.cLogDeriv * Real.log (x : ℝ) ^ 90 * S +
          288 * Real.log (x : ℝ) ^ 90 * S := by linarith
      _ = (623808 * data.cLogDeriv + 288) *
          Real.log (x : ℝ) ^ 90 * S := by ring
  have hscalar : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith [Real.pi_gt_three]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ ν : ℝ,
          eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖
        ≤ ‖∫ ν : ℝ,
          eq21LogDerivIntegrand x m χ (lemma6AlphaPoint x ν)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hscalar
    _ ≤ (623808 * data.cLogDeriv + 288) *
        Real.log (x : ℝ) ^ 90 * S := hnorm
    _ ≤ 1000000 * (data.cLogDeriv + 1) *
        Real.log (x : ℝ) ^ 90 * S := by
      gcongr
      linarith [data.cLogDeriv_pos]

end Chen
