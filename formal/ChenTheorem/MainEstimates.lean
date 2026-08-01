/-
The main estimates: Lemmas 5–9 of Chen's paper.

* Lemma 5 : `Ω ≤ (M₁+M₂)/(1-ε) + O(x/(log x)^{2.01})`.
* Lemma 6 : `M₂ ≪ x/(log x)^{2.01}`. Its conductor reduction, the exact
  `N_m` interface, and the Lemma-3-dependent dyadic estimates are organized
  under `Lemma6/`.
* Lemmas 5 & 6 (combined) : the retained downstream interface
  `Ω ≤ M₁/(1-ε) + O(x/(log x)^{2.01})`.
* Lemma 7 : the upper bound for `M₁` in terms of `x C_x / log x`.
* Lemma 8 : the numerical bound `Ω ≤ 3.9404 x C_x / (log x)²`.
* Lemma 9 : the lower bound
  `P_x(x, x^{1/10}) - (1/2) ∑_{x^{1/10} < p ≤ x^{1/3}} P_x(x, p, x^{1/10})
     ≥ 2.6408 x C_x / (log x)²`,
  proved in the paper via Bombieri's theorem and Richert's weighted sieve [11].

The remaining analytic estimates are explicitly isolated as
`sorry`-placeholders. The final statements of Lemmas 5 and 6 are assembled
from those estimates by proved finite and algebraic reductions in their
respective modules.
-/
import ChenTheorem.Lemma6.Core
import ChenTheorem.Main.NumericalBounds

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

/-! ### Lemma 6

The proof is organized in `Lemma6/Core.lean`; `mTwo_le` is imported from
there. -/

/-! ### Combined consequence of Lemmas 5 and 6 -/

/-- **Lemmas 5 & 6 (combined)**: for even `x`,
`Ω ≤ M₁/(1-ε) + O(x/(log x)^{2.01})`.

This statement is retained as the interface used by Lemmas 7 and 8. -/
theorem sieveOmega_le_mOne (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      (sieveOmega x : ℝ) ≤
        mOne x ε / (1 - ε) + C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C₅, hC₅, hlemma5⟩ :=
    sieveOmega_le_mOne_add_mTwo ε hε hε'
  obtain ⟨C₆, hC₆, hlemma6⟩ :=
    mTwo_le ε hε hε'
  have hε1 : ε < 1 := hε'.trans (by norm_num)
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  let C : ℝ := C₅ + C₆ / (1 - ε)
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos hC₅ (div_pos hC₆ hden)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlemma5, hlemma6] with x h5 h6
  intro hxEven
  have h6' :
      mTwo x ε / (1 - ε) ≤
        (C₆ * (x : ℝ) /
          (Real.log x) ^ (2.01 : ℝ)) / (1 - ε) :=
    (div_le_div_iff_of_pos_right hden).2 (h6 hxEven)
  calc
    (sieveOmega x : ℝ) ≤
        (mOne x ε + mTwo x ε) / (1 - ε) +
          C₅ * (x : ℝ) /
            (Real.log x) ^ (2.01 : ℝ) := h5 hxEven
    _ = mOne x ε / (1 - ε) +
          mTwo x ε / (1 - ε) +
            C₅ * (x : ℝ) /
              (Real.log x) ^ (2.01 : ℝ) := by ring
    _ ≤ mOne x ε / (1 - ε) +
          (C₆ * (x : ℝ) /
            (Real.log x) ^ (2.01 : ℝ)) / (1 - ε) +
              C₅ * (x : ℝ) /
                (Real.log x) ^ (2.01 : ℝ) := by
      gcongr
    _ = mOne x ε / (1 - ε) +
          C * (x : ℝ) /
            (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C]
      field_simp
      ring

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

/-- The prime-pair kernel after the two applications of partial summation in
(23).  This is the prime-distribution input to equation (24); the numerical
integral estimate itself is proved independently in `Main.NumericalBounds`. -/
theorem chenPairs_kernel_le_integral
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      ∑ q ∈ chenPairs x,
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
        (equation24Integral + δ) / Real.log x := by
  sorry

/-- The numerical form of (23)--(24).  The extra `0.000001` absorbs the
limiting error in the two partial-summation steps. -/
theorem chenPairs_kernel_le :
    ∀ᶠ x : ℕ in atTop,
      ∑ q ∈ chenPairs x,
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
        0.492541 / Real.log x := by
  let δ : ℝ := 0.000001
  filter_upwards [chenPairs_kernel_le_integral δ (by norm_num [δ]),
      eventually_gt_atTop 1] with x hkernel hx
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  calc
    ∑ q ∈ chenPairs x,
        ((q.1 : ℝ) * (q.2 : ℝ) *
          Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
      (equation24Integral + δ) / Real.log x := hkernel
    _ ≤ 0.492541 / Real.log x := by
      apply (div_le_div_iff_of_pos_right hlogpos).2
      dsimp only [δ]
      linarith [equation24_integral_bound]

/-- A logarithmic error of order `x/(log x)^2.01` is eventually absorbed by
any positive multiple of `x C_x/(log x)^2`. -/
theorem eventually_log_error_le_singular
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) ≤
        δ * (x : ℝ) * chenConst x / (Real.log x) ^ 2 := by
  let T : ℝ := C / (δ * twinConst)
  have hden : 0 < δ * twinConst :=
    mul_pos hδ twinConst_pos
  have hT : 0 < T := div_pos hC hden
  have htendsto :
      Tendsto (fun y : ℝ =>
          (Real.log y) ^ (0.01 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.01)).comp
      Real.tendsto_log_atTop
  have hlargeReal :
      ∀ᶠ y : ℝ in atTop,
        T ≤ (Real.log y) ^ (0.01 : ℝ) :=
    htendsto.eventually (eventually_ge_atTop T)
  have hlarge :=
    tendsto_natCast_atTop_atTop.eventually hlargeReal
  filter_upwards [hlarge, eventually_gt_atTop 1] with
      x hlarge hx
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hlogSmallPos :
      0 < (Real.log x) ^ (0.01 : ℝ) :=
    Real.rpow_pos_of_pos hlogpos _
  have hfactor :
      C ≤ δ * chenConst x *
          (Real.log x) ^ (0.01 : ℝ) := by
    calc
      C = δ * twinConst * T := by
        dsimp only [T]
        field_simp [twinConst_pos.ne']
      _ ≤ δ * twinConst *
          (Real.log x) ^ (0.01 : ℝ) := by gcongr
      _ ≤ δ * chenConst x *
          (Real.log x) ^ (0.01 : ℝ) := by
        gcongr
        exact twinConst_le_chenConst x
  have hlogSplit :
      (Real.log x) ^ (2.01 : ℝ) =
        (Real.log x) ^ 2 *
          (Real.log x) ^ (0.01 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hlogpos]
    norm_num
  rw [hlogSplit]
  calc
    C * (x : ℝ) /
        ((Real.log x) ^ 2 *
          (Real.log x) ^ (0.01 : ℝ)) =
      (C / (Real.log x) ^ (0.01 : ℝ)) *
        ((x : ℝ) / (Real.log x) ^ 2) := by
          field_simp
    _ ≤ (δ * chenConst x) *
        ((x : ℝ) / (Real.log x) ^ 2) := by
      gcongr
      exact (div_le_iff₀ hlogSmallPos).2 hfactor
    _ = δ * (x : ℝ) * chenConst x /
        (Real.log x) ^ 2 := by ring

/-- **Lemma 8**: for large even `x`, `Ω ≤ 3.9404 x C_x / (log x)²`.
(The numerical constant comes from the integral estimate (24):
`∫_{1/10}^{1/3} log(2-3α)/(α(1-α)) dα ≤ 0.49254`.) -/
theorem sieveOmega_le :
    ∀ᶠ x : ℕ in atTop, Even x →
      (sieveOmega x : ℝ) ≤ 3.9404 * (x : ℝ) * chenConst x / (Real.log x) ^ 2 := by
  let ε : ℝ := 0.000001
  have hε : 0 < ε := by norm_num [ε]
  have hε' : ε < 1 / 100 := by norm_num [ε]
  obtain ⟨C, hC, hOmega⟩ :=
    sieveOmega_le_mOne ε hε hε'
  have hmOne := mOne_le ε hε hε'
  have herror :=
    eventually_log_error_le_singular C 0.00005 hC (by norm_num)
  filter_upwards [hOmega, hmOne, chenPairs_kernel_le,
      herror, eventually_gt_atTop 1] with
      x hOmega hmOne hkernel herror hx
  intro hxEven
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hconst :
      0 < chenConst x :=
    twinConst_pos.trans_le (twinConst_le_chenConst x)
  let A : ℝ :=
    (x : ℝ) * chenConst x / (Real.log x) ^ 2
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 1 - ε := sub_pos.mpr (hε'.trans (by norm_num))
  have hmOne' := hmOne hxEven
  have hmain :
      mOne x ε / (1 - ε) ≤
        ((8 + 24 * ε) * 0.492541 / (1 - ε)) * A := by
    calc
      mOne x ε / (1 - ε) ≤
          ((8 + 24 * ε) * (x : ℝ) * chenConst x /
              Real.log x *
            ∑ q ∈ chenPairs x,
              ((q.1 : ℝ) * (q.2 : ℝ) *
                Real.log ((x : ℝ) /
                  ((q.1 : ℝ) * q.2)))⁻¹) /
            (1 - ε) :=
        (div_le_div_iff_of_pos_right hden).2 hmOne'
      _ ≤ (((8 + 24 * ε) * (x : ℝ) * chenConst x /
              Real.log x) *
            (0.492541 / Real.log x)) /
            (1 - ε) := by
        gcongr
      _ = ((8 + 24 * ε) * 0.492541 / (1 - ε)) * A := by
        dsimp only [A]
        field_simp
  have hOmega' := hOmega hxEven
  have herror' :
      C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) ≤
        0.00005 * A := by
    dsimp only [A]
    convert herror using 1
    ring
  have hnumeric :
      (8 + 24 * ε) * 0.492541 / (1 - ε) +
          0.00005 ≤ 3.9404 := by
    norm_num [ε]
  calc
    (sieveOmega x : ℝ) ≤
        mOne x ε / (1 - ε) +
          C * (x : ℝ) /
            (Real.log x) ^ (2.01 : ℝ) := hOmega'
    _ ≤ ((8 + 24 * ε) * 0.492541 / (1 - ε)) * A +
          0.00005 * A := add_le_add hmain herror'
    _ = (((8 + 24 * ε) * 0.492541 / (1 - ε)) +
          0.00005) * A := by ring
    _ ≤ 3.9404 * A := by gcongr
    _ = 3.9404 * (x : ℝ) * chenConst x /
          (Real.log x) ^ 2 := by
      dsimp only [A]
      ring

/-! ### Lemma 9 -/

/-- The analytic output of Richert's weighted sieve (Theorem A of [11]), after
the two applications in (26) and the averaged progression estimate supplied
by Bombieri--Vinogradov, but before the elementary comparison (27).

The paper first obtains the coefficient `8 - 50 * sqrt ε`, with `ε > 0`
arbitrarily small.  Equivalently, every fixed positive loss `δ` may be used
for all sufficiently large `x`. -/
theorem richert_weighted_sieve_estimate
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) * ((x : ℝ) * chenConst x / (Real.log x) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 + equation27Integral) ≤
        (sievedPrimeCount x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (sievedPrimeCountAt x p' : ℝ) := by
  sorry

/-- Richert--Bombieri with equation (27) inserted.  Keeping `δ` explicit is
important: the paper does not prove the stronger estimate with the limiting
coefficient `8` itself. -/
theorem richert_weighted_sieve_final_estimate
    (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ < 8) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) * ((x : ℝ) * chenConst x / (Real.log x) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 - 0.0164725) ≤
        (sievedPrimeCount x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (sievedPrimeCountAt x p' : ℝ) := by
  filter_upwards [richert_weighted_sieve_estimate δ hδ,
      eventually_gt_atTop 1] with x hrichert hx
  intro hxEven
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hconst :
      0 < chenConst x :=
    twinConst_pos.trans_le (twinConst_le_chenConst x)
  have hscale :
      0 ≤ (8 - δ) *
        ((x : ℝ) * chenConst x / (Real.log x) ^ 2) := by
    positivity
  have hbracket :
      Real.log 4 - Real.log 8 / 2 - 0.0164725 ≤
        Real.log 4 - Real.log 8 / 2 + equation27Integral := by
    linarith [equation27_integral_bound]
  calc
    (8 - δ) * ((x : ℝ) * chenConst x / (Real.log x) ^ 2) *
        (Real.log 4 - Real.log 8 / 2 - 0.0164725) ≤
      (8 - δ) * ((x : ℝ) * chenConst x / (Real.log x) ^ 2) *
        (Real.log 4 - Real.log 8 / 2 + equation27Integral) := by
      exact mul_le_mul_of_nonneg_left hbracket hscale
    _ ≤ (sievedPrimeCount x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (sievedPrimeCountAt x p' : ℝ) :=
      hrichert hxEven

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
  let δ : ℝ := 0.000001
  have hδ : 0 < δ := by norm_num [δ]
  filter_upwards [richert_weighted_sieve_final_estimate δ hδ
      (by norm_num [δ]),
      eventually_gt_atTop 1] with x hrichert hx
  intro hxEven
  have hlog4 :
      Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog8 :
      Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hcoefficient :
      (2.6408 : ℝ) ≤ (8 - δ) *
        (Real.log 4 - Real.log 8 / 2 - 0.0164725) := by
    rw [hlog4, hlog8]
    dsimp only [δ]
    nlinarith [Real.log_two_gt_d9]
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hconst :
      0 < chenConst x :=
    twinConst_pos.trans_le (twinConst_le_chenConst x)
  have hmainNonneg :
      0 ≤ (x : ℝ) * chenConst x /
        (Real.log x) ^ 2 := by positivity
  have hrichert' := hrichert hxEven
  calc
    2.6408 * (x : ℝ) * chenConst x /
        (Real.log x) ^ 2 ≤
      ((8 - δ) *
        (Real.log 4 - Real.log 8 / 2 - 0.0164725)) *
          ((x : ℝ) * chenConst x /
            (Real.log x) ^ 2) := by
      calc
        2.6408 * (x : ℝ) * chenConst x /
            (Real.log x) ^ 2 =
          2.6408 * ((x : ℝ) * chenConst x /
            (Real.log x) ^ 2) := by ring
        _ ≤ ((8 - δ) *
            (Real.log 4 - Real.log 8 / 2 - 0.0164725)) *
              ((x : ℝ) * chenConst x /
                (Real.log x) ^ 2) := by gcongr
    _ ≤ (sievedPrimeCount x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (sievedPrimeCountAt x p' : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrichert'

end Chen
