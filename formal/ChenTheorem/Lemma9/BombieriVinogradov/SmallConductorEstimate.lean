import ChenTheorem.Lemma9.BombieriVinogradov.SmallConductorLogDeriv
import ChenTheorem.Lemma9.BombieriVinogradov.Characters

open Filter Real
open scoped Classical Interval

namespace Chen.BombieriVinogradov

/-!
# The small-conductor character estimate

This file absorbs the explicit errors obtained from the finite classical
zero-free contour.  Its endpoint is the Siegel--Walfisz estimate required
for the small primitive-conductor part of Bombieri--Vinogradov.
-/

/-- Moving to `1 - 1/sqrt(log x)` produces exactly the exponential saving
`exp (-sqrt(log x))`. -/
theorem natCast_rpow_one_sub_inv_sqrt_log_eq
    {x : ℕ} (hx : 2 ≤ x) :
    (x : ℝ) ^ (1 - 1 / Real.sqrt (Real.log (x : ℝ))) =
      (x : ℝ) / Real.exp (Real.sqrt (Real.log (x : ℝ))) := by
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 hlog
  have hquot : Real.log (x : ℝ) *
      (1 / Real.sqrt (Real.log (x : ℝ))) =
        Real.sqrt (Real.log (x : ℝ)) := by
    rw [mul_one_div, div_eq_iff hsqrt.ne']
    simpa only [pow_two] using (Real.sq_sqrt hlog.le).symm
  rw [Real.rpow_sub hxpos, Real.rpow_one,
    Real.rpow_def_of_pos hxpos, hquot]

/-- Exponential decay in `sqrt(log x)` absorbs an arbitrary fixed power of
`log x`, with an arbitrary fixed leading constant. -/
theorem eventually_const_mul_log_pow_le_exp_sqrt_log
    (C : ℝ) (P : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      C * Real.log (x : ℝ) ^ P ≤
        Real.exp (Real.sqrt (Real.log (x : ℝ))) := by
  have hsqrt : Tendsto
      (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hratioReal : ∀ᶠ y : ℝ in atTop,
      C ≤ Real.exp y / y ^ ((2 * P : ℕ) : ℝ) := by
    have hraw := (tendsto_exp_mul_div_rpow_atTop
      (((2 * P : ℕ) : ℝ)) 1 (by norm_num)).eventually
        (eventually_ge_atTop C)
    simpa only [one_mul] using hraw
  have hratio := hsqrt.eventually hratioReal
  have hypos := hsqrt.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hratio, hypos] with x hx hypos
  let L : ℝ := Real.log (x : ℝ)
  let y : ℝ := Real.sqrt L
  have hL0 : 0 ≤ L := by
    dsimp only [y, L] at hypos ⊢
    exact (Real.sqrt_pos.1 hypos).le
  have hpowpos : 0 < y ^ ((2 * P : ℕ) : ℝ) :=
    Real.rpow_pos_of_pos hypos _
  have hmain : C * y ^ ((2 * P : ℕ) : ℝ) ≤ Real.exp y :=
    (le_div_iff₀ hpowpos).mp (by simpa only [y, L] using hx)
  have hLpow : L ^ P = y ^ (2 * P) := by
    rw [show L = y ^ 2 by
      dsimp only [y]
      exact (Real.sq_sqrt hL0).symm]
    rw [← pow_mul]
  calc
    C * Real.log (x : ℝ) ^ P = C * L ^ P := by rfl
    _ = C * y ^ (2 * P) := by rw [hLpow]
    _ = C * y ^ ((2 * P : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ Real.exp y := hmain
    _ = Real.exp (Real.sqrt (Real.log (x : ℝ))) := by rfl

/-- A convenient quotient form of the preceding absorption lemma. -/
theorem eventually_const_mul_shifted_rpow_mul_log_pow_le
    (C : ℝ) (P K : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      C * (x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
          Real.log (x : ℝ) ^ P ≤
        (x : ℝ) / Real.log (x : ℝ) ^ K := by
  have habsorb := eventually_const_mul_log_pow_le_exp_sqrt_log
    C (P + K)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, habsorb,
      hlogT.eventually (eventually_gt_atTop 0)] with x hx habsorb hlog
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hexp : 0 < Real.exp (Real.sqrt (Real.log (x : ℝ))) :=
    Real.exp_pos _
  have hKpos : 0 < Real.log (x : ℝ) ^ K := pow_pos hlog _
  rw [natCast_rpow_one_sub_inv_sqrt_log_eq hx]
  rw [le_div_iff₀ hKpos]
  have hscale := mul_le_mul_of_nonneg_left habsorb
    (div_nonneg hx0 hexp.le)
  calc
    C * ((x : ℝ) / Real.exp (Real.sqrt (Real.log (x : ℝ)))) *
          Real.log (x : ℝ) ^ P * Real.log (x : ℝ) ^ K =
        ((x : ℝ) / Real.exp (Real.sqrt (Real.log (x : ℝ)))) *
          (C * Real.log (x : ℝ) ^ (P + K)) := by
      rw [pow_add]
      ring
    _ ≤ ((x : ℝ) /
          Real.exp (Real.sqrt (Real.log (x : ℝ)))) *
        Real.exp (Real.sqrt (Real.log (x : ℝ))) := hscale
    _ = (x : ℝ) := by field_simp [hexp.ne']

/-- If `p + k ≤ n`, an inverse `n`-th power dominates the requested
inverse `k`-th power after paying a numerator power `p`. -/
theorem mul_pow_mul_inv_pow_le_div_pow
    {X L : ℝ} (hX : 0 ≤ X) (hL : 1 ≤ L)
    {p n k : ℕ} (hpn : p + k ≤ n) :
    X * L ^ p * (L ^ n)⁻¹ ≤ X / L ^ k := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hpow : L ^ (p + k) ≤ L ^ n :=
    pow_le_pow_right₀ hL hpn
  have hinv : (L ^ n)⁻¹ ≤ (L ^ (p + k))⁻¹ :=
    (inv_le_inv₀ (pow_pos hLpos _) (pow_pos hLpos _)).mpr hpow
  calc
    X * L ^ p * (L ^ n)⁻¹ ≤
        X * L ^ p * (L ^ (p + k))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg hX (pow_nonneg hLpos.le _))
    _ = X * (L ^ k)⁻¹ := by
      rw [pow_add]
      field_simp [hLpos.ne']
    _ = X / L ^ k := by rw [div_eq_mul_inv]

/-- The complete logarithmic-derivative integral for one primitive small
conductor has an arbitrary logarithmic saving.  This is where the
exponential gain from the shifted vertical side absorbs its growing
polylogarithmic height. -/
theorem norm_integral_bvSmoothedLogDeriv_smallConductor_bound
    (data : Chen.PrimitiveZeroFreeRegionData) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ 100 →
          χ.IsPrimitive →
          ‖∫ t : ℝ,
              bvSmoothedLogDerivIntegrand K x χ
                (Chen.lemma6AlphaPoint x t)‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  let N : ℕ := 22 * (K + 1)
  let D : ℝ := (((N + 104 : ℕ) : ℝ) ^ 2) * data.cLogDeriv
  let C : ℝ := 1 + 4 * Real.exp 1 * D + 4 * Real.exp 1 * Real.pi
  have hDpos : 0 < D := by
    dsimp only [D, N]
    exact mul_pos (by positivity) data.cLogDeriv_pos
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwidthAll :=
    eventually_two_div_sqrt_log_lt_primitiveZeroFreeWidth_bvHeight data K
  have habsorb := eventually_const_mul_shifted_rpow_mul_log_pow_le
    (4 * D) (N + 2) K
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [eventually_ge_atTop 2,
      hlogT.eventually (eventually_ge_atTop 10), hwidthAll, habsorb] with
      x hx hLten hwidthAll habsorb
  intro q _ χ hq hq100 hχ
  let L : ℝ := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
    have hfirst : (10 : ℝ) ^ 4 ≤ L ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hLten 4
    have hsecond : L ^ 4 ≤ L ^ (10 * (K + 1)) :=
      pow_le_pow_right₀ hLone (by omega)
    simpa only [L] using hfirst.trans hsecond
  have hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)) := by
    have hsqrt : (2 : ℝ) ≤ Real.sqrt L := by
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← hsqrt4]
      exact Real.sqrt_le_sqrt (by linarith)
    have hinv : 1 / Real.sqrt L ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hsqrt
    dsimp only [L] at hinv ⊢
    linarith
  have hwidth : ∀ t : ℝ, |t| ≤ bvSmoothingContourHeight K x →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidth data.cHeight data.cSiegel q t :=
    hwidthAll q hq hq100
  have hfinite :=
    norm_integral_bvSmoothedLogDeriv_alpha_le_finite_classical
      data K hq hx hlarge hγpos hχ hwidth
  have hheight : bvSmoothingContourHeight K x = L ^ N := by
    dsimp only [bvSmoothingContourHeight, L, N]
    rw [← pow_mul]
    congr 1
    omega
  have hM : Chen.eq21ClassicalLogDerivMajorant data q
        (bvSmoothingContourHeight K x) ≤ D * L ^ 2 := by
    have hm := eq21ClassicalLogDerivMajorant_bvHeight_le
      data K (by simpa only [L] using (show (4 : ℝ) ≤ L by linarith))
        hq hq100
    simpa only [D, N, L] using hm
  have hM0 := Chen.eq21ClassicalLogDerivMajorant_nonneg data q
    (bvSmoothingContourHeight K x)
  have hwidthOne :
      |(1 + 1 / Real.log (x : ℝ)) -
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| ≤ 1 := by
    have hinvlog : 0 ≤ 1 / L := by positivity
    have hinvsqrt : 0 ≤ 1 / Real.sqrt L := by positivity
    have hsqrt : 1 / Real.sqrt L ≤ 1 / 2 := by
      linarith [hγpos]
    have hloginv : 1 / L ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    dsimp only [L] at hinvlog hinvsqrt hsqrt hloginv ⊢
    rw [abs_of_nonneg (by linarith)]
    linarith
  let Y : ℝ := (x : ℝ) / L ^ K
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hB1 :
      4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            Chen.eq21ClassicalLogDerivMajorant data q
              (bvSmoothingContourHeight K x)) ≤ Y := by
    calc
      4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            Chen.eq21ClassicalLogDerivMajorant data q
              (bvSmoothingContourHeight K x)) ≤
        4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            (D * L ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg hx0 _))
            (mul_nonneg (by norm_num)
              (bvSmoothingContourHeight_nonneg K x))
      _ = 4 * L ^ N *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            (D * L ^ 2)) := by rw [hheight]
      _ = (4 * D) * (x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            L ^ (N + 2) := by
        rw [pow_add]
        ring
      _ ≤ Y := by simpa only [L, N, Y] using habsorb
  have hX2 : 0 ≤ 4 * Real.exp 1 * D * (x : ℝ) := by positivity
  have hpow2 := mul_pow_mul_inv_pow_le_div_pow hX2 hLone
    (p := 2) (n := 44 * (K + 1)) (k := K) (by omega)
  have hB2 :
      2 * (((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))|) ≤
        (4 * Real.exp 1 * D) * Y := by
    have hinv0 : 0 ≤
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ := by positivity
    have hcoef0 : 0 ≤ 2 * Real.exp 1 * (x : ℝ) := by positivity
    have hZ0 : 0 ≤
        (2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ :=
      mul_nonneg (mul_nonneg hcoef0 hM0) hinv0
    have hZM :
        (2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
            (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ ≤
          (2 * Real.exp 1 * (x : ℝ) * (D * L ^ 2)) *
            (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM hcoef0) hinv0
    calc
      2 * (((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))|) ≤
        2 * (((2 * Real.exp 1 * (x : ℝ) *
          Chen.eq21ClassicalLogDerivMajorant data q
            (bvSmoothingContourHeight K x)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hwidthOne hZ0) (by norm_num)
      _ ≤ 2 * (((2 * Real.exp 1 * (x : ℝ) * (D * L ^ 2)) *
          (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hZM (by norm_num)) (by norm_num)
      _ =
        (4 * Real.exp 1 * D * (x : ℝ)) * L ^ 2 *
          (L ^ (44 * (K + 1)))⁻¹ := by
        dsimp only [L]
        ring
      _ ≤ (4 * Real.exp 1 * D * (x : ℝ)) / L ^ K := hpow2
      _ = (4 * Real.exp 1 * D) * Y := by
        dsimp only [Y]
        ring
  have hX3 : 0 ≤ 4 * Real.exp 1 * Real.pi * (x : ℝ) := by positivity
  have hpow3 := mul_pow_mul_inv_pow_le_div_pow hX3 hLone
    (p := 2) (n := 11 * (K + 1)) (k := K) (by omega)
  have hB3 :
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
          ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) ≤
        (4 * Real.exp 1 * Real.pi) * Y := by
    calc
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
          ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) =
        (4 * Real.exp 1 * Real.pi * (x : ℝ)) * L ^ 2 *
          (L ^ (11 * (K + 1)))⁻¹ := by
        dsimp only [L]
        ring
      _ ≤ (4 * Real.exp 1 * Real.pi * (x : ℝ)) / L ^ K := hpow3
      _ = (4 * Real.exp 1 * Real.pi) * Y := by
        dsimp only [Y]
        ring
  apply hfinite.trans
  calc
    4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            Chen.eq21ClassicalLogDerivMajorant data q
              (bvSmoothingContourHeight K x)) +
        2 * (((2 * Real.exp 1 * (x : ℝ) *
            Chen.eq21ClassicalLogDerivMajorant data q
              (bvSmoothingContourHeight K x)) *
            (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
          |(1 + 1 / Real.log (x : ℝ)) -
            (1 - 1 / Real.sqrt (Real.log (x : ℝ)))|) +
        (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
          ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) ≤
      Y + (4 * Real.exp 1 * D) * Y +
        (4 * Real.exp 1 * Real.pi) * Y := by
      exact add_le_add (add_le_add hB1 hB2) hB3
    _ = C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
      dsimp only [C, Y, L]
      ring

/-- The adjustable smoothed twisted von-Mangoldt sum inherits the same
arbitrary logarithmic saving from its Perron representation. -/
theorem norm_bvSmoothedTwistedPsi_smallConductor_bound
    (data : Chen.PrimitiveZeroFreeRegionData) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ 100 →
          χ.IsPrimitive →
          ‖bvSmoothedTwistedPsi K x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨C, hC, hbound⟩ :=
    norm_integral_bvSmoothedLogDeriv_smallConductor_bound data K
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hbound,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 10)] with x hx hbound hlog
  intro q _ χ hq hq100 hχ
  change 10 ≤ Real.log (x : ℝ) at hlog
  have hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
    have hLone : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
    exact (pow_le_pow_left₀ (by norm_num) hlog 4).trans
      (pow_le_pow_right₀ hLone (by omega))
  have hint := hbound q χ hq hq100 hχ
  rw [bvSmoothedTwistedPsi_eq_logDerivPerron K hx hlarge χ]
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  have hnormalize :
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          (Complex.I * ∫ t : ℝ,
            bvSmoothedLogDerivIntegrand K x χ
              (((1 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) +
                (t : ℂ) * Complex.I)) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6AlphaPoint x t) := by
    have hconst :
        (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
          ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
      calc
        (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
            1 / (2 * (Real.pi : ℂ)) := by
          field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
        _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by norm_cast
    unfold Chen.lemma6AlphaPoint
    rw [← mul_assoc, hconst]
  rw [hnormalize, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  have hscalar : 1 / (2 * Real.pi) ≤ (1 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith [Real.pi_gt_three]
  exact (mul_le_of_le_one_left (norm_nonneg _) hscalar).trans hint

/-- The adjustable smoothing parameter is so large that its residual
`R^(-1/10)` error beats any prescribed inverse logarithmic power. -/
theorem eventually_bvSmoothingParameter_neg_tenth_le_log_inv_pow
    (K : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) ≤
        (Real.log (x : ℝ) ^ K)⁻¹ := by
  have habsorb := Chen.eventually_const_mul_log_pow_le_rpow
    1 K (by norm_num : (0 : ℝ) < 0.1)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, habsorb,
      hlogT.eventually (eventually_ge_atTop 1)] with x hx habsorb hlog
  let L : ℝ := Real.log (x : ℝ)
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by simpa only [L] using hlog
  have hRpos : 0 < bvSmoothingParameter K x := by
    unfold bvSmoothingParameter
    exact Real.exp_pos _
  have hExp : (x : ℝ) ^ (0.1 : ℝ) ≤
      bvSmoothingParameter K x ^ (0.1 : ℝ) := by
    rw [Real.rpow_def_of_pos hxpos,
      Real.rpow_def_of_pos hRpos, log_bvSmoothingParameter]
    apply Real.exp_le_exp.mpr
    have hpow : L ≤ L ^ (10 * (K + 1)) := by
      calc
        L = L ^ 1 := by ring
        _ ≤ L ^ (10 * (K + 1)) :=
          pow_le_pow_right₀ hLone (by omega)
    dsimp only [L] at hpow ⊢
    nlinarith
  have hlogpow : Real.log (x : ℝ) ^ K ≤
      (x : ℝ) ^ (0.1 : ℝ) := by
    simpa only [one_mul] using habsorb
  have htotal : Real.log (x : ℝ) ^ K ≤
      bvSmoothingParameter K x ^ (0.1 : ℝ) := hlogpow.trans hExp
  rw [show bvSmoothingParameter K x ^ (-(0.1 : ℝ)) =
      (bvSmoothingParameter K x ^ (0.1 : ℝ))⁻¹ by
    simpa only using Real.rpow_neg hRpos.le (0.1 : ℝ)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hRpos _)
    (pow_pos hLpos K)).mpr htotal

/-- The difference between the sharp and adjustable smoothed sums also has
an arbitrary logarithmic saving, uniformly in the character and modulus. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_smallConductor_bound
    (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
          C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  let C : ℝ := Real.log 4 + 7
  have hCpos : 0 < C := by
    dsimp only [C]
    have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hRerr := eventually_bvSmoothingParameter_neg_tenth_le_log_inv_pow K
  have hlogabsorb := Chen.eventually_const_mul_log_pow_le_rpow
    1 (K + 1) (by norm_num : (0 : ℝ) < 1)
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hRerr, hlogabsorb,
      hlogT.eventually (eventually_ge_atTop 10)] with
      x hx hRerr hlogabsorb hLten
  intro q χ
  let L : ℝ := Real.log (x : ℝ)
  let Y : ℝ := (x : ℝ) / L ^ K
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
    have hfirst : (10 : ℝ) ^ 4 ≤ L ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hLten 4
    have hsecond : L ^ 4 ≤ L ^ (10 * (K + 1)) :=
      pow_le_pow_right₀ hLone (by omega)
    simpa only [L] using hfirst.trans hsecond
  have hpsi : Chebyshev.psi x ≤ (Real.log 4 + 4) * (x : ℝ) :=
    Chebyshev.psi_le_const_mul_self hx0
  have hpsi0 : 0 ≤ Chebyshev.psi x := by positivity
  have hdeep : bvSmoothingParameter K x ^ (-(0.1 : ℝ)) *
      Chebyshev.psi x ≤ (Real.log 4 + 4) * Y := by
    calc
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) *
          Chebyshev.psi x ≤
        (L ^ K)⁻¹ * Chebyshev.psi x :=
          mul_le_mul_of_nonneg_right
            (by simpa only [L] using hRerr) hpsi0
      _ ≤ (L ^ K)⁻¹ * ((Real.log 4 + 4) * (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hpsi (by positivity)
      _ = (Real.log 4 + 4) * Y := by
        dsimp only [Y]
        rw [div_eq_mul_inv]
        ring
  have hrpowBoundary : L ^ (-(K + 1 : ℝ)) * L = (L ^ K)⁻¹ := by
    calc
      L ^ (-(K + 1 : ℝ)) * L =
          L ^ (-(K + 1 : ℝ)) * L ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = L ^ (-(K + 1 : ℝ) + 1) := by
        rw [Real.rpow_add hLpos]
      _ = L ^ (-(K : ℝ)) := by
        congr 1
        ring
      _ = (L ^ (K : ℝ))⁻¹ := Real.rpow_neg hLpos.le _
      _ = (L ^ K)⁻¹ := by rw [Real.rpow_natCast]
  have hlogpow : L ^ (K + 1) ≤ (x : ℝ) := by
    simpa only [one_mul, Real.rpow_one, L] using hlogabsorb
  have hLY : L ≤ Y := by
    rw [show Y = (x : ℝ) / L ^ K by rfl,
      le_div_iff₀ (pow_pos hLpos K)]
    calc
      L * L ^ K = L ^ (K + 1) := by rw [pow_succ']
      _ ≤ (x : ℝ) := hlogpow
  have hboundary :
      (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) ≤ 3 * Y := by
    calc
      (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) =
        2 * (x : ℝ) * (L ^ K)⁻¹ + L := by
          dsimp only [L]
          calc
            (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
                Real.log (x : ℝ) =
              2 * (x : ℝ) *
                  (Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) *
                    Real.log (x : ℝ)) + Real.log (x : ℝ) := by ring
            _ = 2 * (x : ℝ) * (Real.log (x : ℝ) ^ K)⁻¹ +
                Real.log (x : ℝ) := by rw [hrpowBoundary]
      _ = 2 * Y + L := by
        dsimp only [Y]
        rw [div_eq_mul_inv]
        ring
      _ ≤ 2 * Y + Y := by linarith
      _ = 3 * Y := by ring
  have hraw := norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_explicit
    K hx hlarge χ
  apply hraw.trans
  calc
    bvSmoothingParameter K x ^ (-(0.1 : ℝ)) * Chebyshev.psi x +
        (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) ≤
      (Real.log 4 + 4) * Y + 3 * Y := add_le_add hdeep hboundary
    _ = C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
      dsimp only [C, Y, L]
      ring

/-- **Siegel--Walfisz for the primitive characters needed by
Bombieri--Vinogradov.**  Every fixed inverse logarithmic power is available,
uniformly for conductors `q ≤ (log x)^100`. -/
theorem norm_twistedPsi_smallConductor_bound
    (hzf : Chen.PrimitiveZeroFreeRegion) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ 100 →
          χ.IsPrimitive →
          ‖twistedPsi x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨data⟩ := hzf
  obtain ⟨C₁, hC₁, hsmooth⟩ :=
    norm_bvSmoothedTwistedPsi_smallConductor_bound data K
  obtain ⟨C₂, hC₂, herr⟩ :=
    norm_twistedPsi_sub_bvSmoothedTwistedPsi_smallConductor_bound K
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  filter_upwards [hsmooth, herr,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop 0)] with x hsmooth herr hlog
  intro q _ χ hq hq100 hχ
  have hS := hsmooth q χ hq hq100 hχ
  have hE := herr q χ
  have hY0 : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ K := by positivity
  calc
    ‖twistedPsi x χ‖ =
        ‖(twistedPsi x χ - bvSmoothedTwistedPsi K x χ) +
          bvSmoothedTwistedPsi K x χ‖ := by ring_nf
    _ ≤ ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ +
        ‖bvSmoothedTwistedPsi K x χ‖ := norm_add_le _ _
    _ ≤ C₂ * (x : ℝ) / Real.log (x : ℝ) ^ K +
        C₁ * (x : ℝ) / Real.log (x : ℝ) ^ K :=
      add_le_add hE hS
    _ = (C₁ + C₂) * (x : ℝ) /
        Real.log (x : ℝ) ^ K := by ring

/-- For primitive moduli at least two, the principal correction vanishes,
so the same small-conductor estimate holds for `adjustedTwistedPsi`. -/
theorem norm_adjustedTwistedPsi_smallConductor_bound
    (hzf : Chen.PrimitiveZeroFreeRegion) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        2 ≤ q → (q : ℝ) ≤ Real.log (x : ℝ) ^ 100 →
          χ.IsPrimitive →
          ‖adjustedTwistedPsi x χ‖ ≤
            C * (x : ℝ) / Real.log (x : ℝ) ^ K := by
  obtain ⟨C, hC, hbound⟩ := norm_twistedPsi_smallConductor_bound hzf K
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with x hbound
  intro q _ χ hq hq100 hχ
  rw [adjustedTwistedPsi, if_neg (Chen.primitiveCharacter_ne_one hq hχ),
    sub_zero]
  exact hbound q χ hq hq100 hχ

end Chen.BombieriVinogradov
