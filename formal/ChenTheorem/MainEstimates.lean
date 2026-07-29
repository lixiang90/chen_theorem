/-
The main estimates: Lemmas 5–9 of Chen's paper.

* Lemma 5 : `Ω ≤ (M₁+M₂)/(1-ε) + O(x/(log x)^{2.01})`.
* Lemma 6 : `M₂ ≪ x/(log x)^{2.01}`.  Its finite-sum definition is in
  `Defs.lean`; the equivalent contour representation involving `L'/L` will be
  introduced when Lemma 6 is proved.
* Lemmas 5 & 6 (combined) : the retained downstream interface
  `Ω ≤ M₁/(1-ε) + O(x/(log x)^{2.01})`.
* Lemma 7 : the upper bound for `M₁` in terms of `x C_x / log x`.
* Lemma 8 : the numerical bound `Ω ≤ 3.9404 x C_x / (log x)²`.
* Lemma 9 : the lower bound
  `P_x(x, x^{1/10}) - (1/2) ∑_{x^{1/10} < p ≤ x^{1/3}} P_x(x, p, x^{1/10})
     ≥ 2.6408 x C_x / (log x)²`,
  proved in the paper via Bombieri's theorem and Richert's weighted sieve [11].

The remaining analytic estimates are explicitly isolated as
`sorry`-placeholders.  The final statement of Lemma 5 is assembled from those
estimates by proved finite and algebraic reductions in `Lemma5/Core.lean`.
-/
import ChenTheorem.Lemma5.Boundary.Analytic

-- This file is still an explicitly documented collection of formalization targets.
set_option warn.sorry false

open Filter Real
open scoped Classical

namespace Chen

/-! ### Positivity of the singular series -/

/-- The twin-prime constant is positive. -/
theorem twinConst_pos : 0 < twinConst := by
  sorry

/-- `C_x ≥ ∏_{p>2} (1 - 1/(p-1)²)`, since the finite product over `p ∣ x` has all
factors `≥ 1`. -/
theorem twinConst_le_chenConst (x : ℕ) : twinConst ≤ chenConst x := by
  sorry

/-! ### Lemma 5 -/

/-- Elementary power-saving estimate for the small-third-prime tail.  The
paper obtains this by summing
`(x/(p₁p₂))^(1-ε)` over the admissible prime pairs. -/
theorem sieveMSmallTail_power_bound
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (sieveMSmallTail x ε : ℝ) ≤
        C * (x : ℝ) ^ (1 - ε / 12) := by
  exact ⟨2, by norm_num,
    eventually_sieveMSmallTail_le_rpow hε
      (hε'.trans (by norm_num))⟩

/-- The small-third-prime tail in the elementary reduction `Ω → M` is
negligible.  A fixed power saving absorbs `(log x)^2.01`. -/
theorem sieveMSmallTail_le
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (sieveMSmallTail x ε : ℝ) ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C, hC, htail⟩ :=
    sieveMSmallTail_power_bound ε hε hε'
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := ε / 12) (r := (2.01 : ℝ)) (by positivity)] with x hx hpower
  exact hx.trans (by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hpower hC.le))

/-- The sole remaining two-dimensional upper-sieve input in formula (5).
Here the base prime of `n` is larger than `x^(1/100)`, so both `n` and
`x-p₁p₂n` avoid all primes up to `x^(1/100)`. -/
theorem smoothingBoundaryLargeBaseMass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      smoothingBoundaryLargeBaseMass x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  exact eventually_smoothingBoundaryLargeBaseMass_le

/-- The full transition mass combines the fixed-power small-base part with
the two-dimensional upper-sieve estimate. -/
theorem smoothingBoundaryMass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      smoothingBoundaryMass x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_large, hC_large, hlarge⟩ :=
    smoothingBoundaryLargeBaseMass_le
  let C_small : ℝ := 18 * ((Real.log 2)⁻¹ + 1)
  let C : ℝ := C_small + C_large
  have hC_small : 0 < C_small := by
    dsimp only [C_small]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨C, add_pos hC_small hC_large, ?_⟩
  filter_upwards
      [eventually_smoothingBoundarySmallBaseMass_le, hlarge] with
      x hsmall hlarge
  intro hxeven
  rw [smoothingBoundaryMass_eq_small_add_large]
  calc
    smoothingBoundarySmallBaseMass x +
        smoothingBoundaryLargeBaseMass x ≤
      C_small * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) +
        C_large * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) :=
      add_le_add (by simpa only [C_small] using hsmall)
        (hlarge hxeven)
    _ = C * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      ring

/-- The complete smoothing loss in formula (5).  Lemma 1 controls the
interior by `x⁻⁰·¹ M`; only `smoothingBoundaryMass_le` is needed for the
transition interval. -/
theorem sieveMSmoothingError_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      sieveMSmoothingError x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_boundary, hC_boundary, hboundary⟩ :=
    smoothingBoundaryMass_le
  let C : ℝ := 19 + C_boundary
  refine ⟨C, add_pos (by norm_num) hC_boundary, ?_⟩
  have hxlogReal :
      ∀ᶠ y : ℝ in atTop, (10 : ℝ) ^ 4 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop ((10 : ℝ) ^ 4))
  have hxlog :
      ∀ᶠ x : ℕ in atTop, (10 : ℝ) ^ 4 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hxlogReal
  filter_upwards [hboundary, eventually_smoothingInterior_le,
    hxlog, eventually_gt_atTop 1] with
      x hboundary hinterior hxlog hx1
  intro hxeven
  calc
    sieveMSmoothingError x ≤
        (x : ℝ) ^ (-(0.1 : ℝ)) * sieveM x +
          smoothingBoundaryMass x :=
      sieveMSmoothingError_le_interior_add_boundary hx1 hxlog
    _ ≤ 19 * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) +
        C_boundary * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) :=
      add_le_add hinterior (hboundary hxeven)
    _ = C * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      ring

/-- Logarithmic-error form of equations (5)–(11).  Formula (5) contributes
`sieveMSmoothingError`; equations (6)–(11) contribute the fixed power saving
proved in `smoothedSieveExpansion_power_bound`. -/
theorem sieveM_le_mOne_add_mTwo
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      sieveM x ≤ mOne x ε + mTwo x ε +
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_smooth, hC_smooth, hsmoothing⟩ :=
    sieveMSmoothingError_le
  obtain ⟨C_power, hC_power, hexpansion⟩ :=
    smoothedSieveExpansion_power_bound ε hε hε'
  let C : ℝ := C_smooth + C_power
  refine ⟨C, add_pos hC_smooth hC_power, ?_⟩
  filter_upwards [hsmoothing, hexpansion,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := ε / 3) (r := (2.01 : ℝ)) (by positivity),
    eventually_gt_atTop 1] with
      x hsmoothing hexpansion hpower hx1
  intro hxEven
  have hformula :=
    sieveM_le_smoothedSieveExpansion_add_smoothingError
      (ε := ε) hx1 hε.le (hε'.le.trans (by norm_num))
  have hpower' :
      C_power * (x : ℝ) ^ (1 - ε / 3) ≤
        C_power * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hpower hC_power.le)
  calc
    sieveM x ≤
        smoothedSieveExpansion x ε +
          sieveMSmoothingError x := hformula
    _ ≤ (mOne x ε + mTwo x ε +
          C_power * (x : ℝ) ^ (1 - ε / 3)) +
        C_smooth * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
      gcongr
      · exact hexpansion hxEven
      · exact hsmoothing hxEven
    _ ≤ (mOne x ε + mTwo x ε +
          C_power * (x : ℝ) /
            (Real.log x) ^ (2.01 : ℝ)) +
        C_smooth * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
      gcongr
    _ = mOne x ε + mTwo x ε +
        C * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      ring

/-- **Lemma 5**: for even `x`,
`Ω ≤ (M₁ + M₂)/(1-ε) + O(x/(log x)^{2.01})`. -/
theorem sieveOmega_le_mOne_add_mTwo
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      (sieveOmega x : ℝ) ≤
        (mOne x ε + mTwo x ε) / (1 - ε) +
          C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C_M, hC_M, hM⟩ :=
    sieveM_le_mOne_add_mTwo ε hε hε'
  obtain ⟨C_tail, hC_tail, htail⟩ :=
    sieveMSmallTail_le ε hε hε'
  let C := (C_M + C_tail) / (1 - ε)
  have hε1 : ε < 1 := hε'.trans (by norm_num)
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  refine ⟨C, div_pos (add_pos hC_M hC_tail) hden, ?_⟩
  filter_upwards [hM, htail] with x hxM hxtail
  intro hxEven
  have h :=
    sieveOmega_le_of_sieveM_le hε.le hε1
      (hxM hxEven) hxtail
  calc
    (sieveOmega x : ℝ) ≤
        (mOne x ε + mTwo x ε +
            C_M * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) +
            C_tail * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ)) /
          (1 - ε) := h
    _ = (mOne x ε + mTwo x ε) / (1 - ε) +
          C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      field_simp
      ring

/-! ### Lemma 6 -/

/-- **Lemma 6**: the primitive-character remainder satisfies
`M₂ ≪ x/(log x)^{2.01}`. -/
theorem mTwo_le
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      mTwo x ε ≤ C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  sorry

/-! ### Combined consequence of Lemmas 5 and 6 -/

/-- **Lemmas 5 & 6 (combined)**: for even `x`,
`Ω ≤ M₁/(1-ε) + O(x/(log x)^{2.01})`.

This statement is retained as the interface used by Lemmas 7 and 8. -/
theorem sieveOmega_le_mOne (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      (sieveOmega x : ℝ) ≤
        mOne x ε / (1 - ε) + C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  sorry

/-! ### Lemma 7 -/

/-- **Lemma 7**: for large even `x`,
`M₁ ≤ ((8 + 24ε) x C_x / log x) · ∑_{(p₁,p₂)} 1/(p₁ p₂ log (x/p₁p₂))`. -/
theorem mOne_le (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, Even x →
      mOne x ε ≤
        (8 + 24 * ε) * (x : ℝ) * chenConst x / Real.log x *
          ∑ q ∈ chenPairs x,
            ((q.1 : ℝ) * (q.2 : ℝ) * Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
  sorry

/-! ### Lemma 8 -/

/-- **Lemma 8**: for large even `x`, `Ω ≤ 3.9404 x C_x / (log x)²`.
(The numerical constant comes from the integral estimate (24):
`∫_{1/10}^{1/3} log(2-3α)/(α(1-α)) dα ≤ 0.49254`.) -/
theorem sieveOmega_le :
    ∀ᶠ x : ℕ in atTop, Even x →
      (sieveOmega x : ℝ) ≤ 3.9404 * (x : ℝ) * chenConst x / (Real.log x) ^ 2 := by
  sorry

/-! ### Lemma 9 -/

/-- **Lemma 9**: for large even `x`,
`P_x(x, x^{1/10}) - (1/2) ∑_{x^{1/10} < p' ≤ x^{1/3}} P_x(x, p', x^{1/10})
   ≥ 2.6408 x C_x / (log x)²`.
(Proved in the paper from Richert's weighted sieve [11] and Bombieri's
theorem [9]; the numerical constant comes from
`8 (log 4 - (log 8)/2 - 0.0164725) ≥ 8 · 0.3301 = 2.6408`.) -/
theorem sieved_lower_bound :
    ∀ᶠ x : ℕ in atTop, Even x →
      2.6408 * (x : ℝ) * chenConst x / (Real.log x) ^ 2 ≤
        (sievedPrimeCount x : ℝ) -
          (1 / 2) * ∑ p' ∈ midPrimes x, (sievedPrimeCountAt x p' : ℝ) := by
  sorry

end Chen
