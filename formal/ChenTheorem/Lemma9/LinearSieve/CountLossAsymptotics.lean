import ChenTheorem.Lemma9.LinearSieve.CountCutoff
import ChenTheorem.Lemma9.LinearSieve.PowerSieveCutoff

open Filter
open scoped Classical

namespace Chen.LinearSieve

theorem log_pow_div_nat_tendsto (k : ℕ) :
    Tendsto (fun x : ℕ => Real.log x ^ k / (x : ℝ)) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using h

theorem inv_log_pow_tendsto (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun x : ℕ => (Real.log x ^ k)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    ((tendsto_pow_atTop hk).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/-- The integer rounding in the small-prime cutoff remains negligible
on the ordinary-count scale `x / log² x`. -/
theorem ceil_countCutoff_normalized_tendsto :
    Tendsto (fun x : ℕ => (⌈countCutoff x⌉₊ : ℝ) * Real.log x ^ 2 / x)
      atTop (nhds 0) := by
  have hu := (inv_log_pow_tendsto 2 (by norm_num)).add (log_pow_div_nat_tendsto 2)
  simp only [zero_add] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun x => by positivity)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hl : Real.log (x : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
    calc
      _ ≤ ((x : ℝ) / Real.log x ^ 4 + 1) * Real.log x ^ 2 / x := by
        gcongr
        exact ceil_countCutoff_le (by omega)
      _ = _ := by field_simp

/-- The loss from non-reduced residue classes is negligible uniformly in
the varying residue `x`, rather than just for a fixed set of divisors. -/
theorem primeFactors_card_count_normalized_tendsto :
    Tendsto (fun x : ℕ => (x.primeFactors.card : ℝ) * Real.log x ^ 2 / x)
      atTop (nhds 0) := by
  have hu := (log_pow_div_nat_tendsto 3).const_mul (Real.log 2)⁻¹
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun x => by positivity)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc : (x.primeFactors.card : ℝ) ≤ Real.log x / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr (primeFactors_card_mul_log_two_le_log (by omega))
    calc
      _ ≤ (Real.log x / Real.log 2) * Real.log x ^ 2 / x := by gcongr
      _ = _ := by ring

/-- The deterministic upper bound for all count-conversion losses after
using the BV estimate with exponent three. -/
noncomputable def countConversionLossBound (C : ℝ) (x : ℕ) : ℝ :=
  2 * C * x / Real.log x ^ 4 + 5 * (⌈countCutoff x⌉₊ : ℝ) +
    (3 / 2) * x.primeFactors.card

theorem countConversionLossBound_normalized_tendsto (C : ℝ) :
    Tendsto (fun x : ℕ => countConversionLossBound C x * Real.log x ^ 2 / x)
      atTop (nhds 0) := by
  have h := ((inv_log_pow_tendsto 2 (by norm_num)).const_mul (2 * C)).add
    ((ceil_countCutoff_normalized_tendsto.const_mul 5).add
      (primeFactors_card_count_normalized_tendsto.const_mul (3 / 2)))
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hl : Real.log (x : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  dsimp only [countConversionLossBound]
  field_simp
  ring

/-- Uniform lower boundedness of the singular series transfers a
normalized error limit into the exact scale used in equation (26). -/
theorem eventually_le_chen_scale_of_normalized_tendsto
    (f : ℕ → ℝ) (hf : Tendsto (fun x : ℕ => f x * Real.log x ^ 2 / x) atTop (nhds 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, f x ≤ δ * ((x : ℝ) * chenConst x / Real.log x ^ 2) := by
  have h := hf.eventually (eventually_lt_nhds (mul_pos hδ twinConst_pos))
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with x hx hx2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hb : f x ≤ δ * ((x : ℝ) * twinConst / Real.log x ^ 2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hlpos)).mpr
    have hmul := (div_lt_iff₀ hxpos).mp hx
    nlinarith
  exact hb.trans (by gcongr; exact twinConst_le_chenConst x)

theorem eventually_countConversionLossBound_le (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      countConversionLossBound C x ≤ δ * ((x : ℝ) * chenConst x / Real.log x ^ 2) :=
  eventually_le_chen_scale_of_normalized_tendsto _
    (countConversionLossBound_normalized_tendsto C) δ hδ

/-- A BV remainder of size `C x / log³ x`, divided by the two different
logarithms in the count conversion, fits the deterministic loss bound. -/
theorem count_conversion_error_le (x : ℕ) (hx : 1 < x)
    (C : ℝ) (hC : 0 ≤ C) (E : ℝ) (hE : E ≤ C * x / Real.log x ^ 3)
    (hT : (1 / 2) * Real.log x ≤ Real.log (countCutoff x)) :
    E / Real.log x + (1 / 2) * (E / Real.log (countCutoff x)) +
      5 * (⌈countCutoff x⌉₊ : ℝ) + (3 / 2) * x.primeFactors.card ≤
        countConversionLossBound C x := by
  have hlpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hlhalf : 0 < (1 / 2 : ℝ) * Real.log x := by positivity
  have hTpos : 0 < Real.log (countCutoff x) := hlhalf.trans_le hT
  have hmain : E / Real.log x ≤ C * x / Real.log x ^ 4 := by
    calc
      _ ≤ (C * x / Real.log x ^ 3) / Real.log x :=
        div_le_div_of_nonneg_right hE hlpos.le
      _ = _ := by ring
  have hcorr : (1 / 2) * (E / Real.log (countCutoff x)) ≤ C * x / Real.log x ^ 4 := by
    calc
      _ ≤ (1 / 2) * ((C * x / Real.log x ^ 3) / Real.log (countCutoff x)) := by
        gcongr
      _ ≤ (1 / 2) * ((C * x / Real.log x ^ 3) / ((1 / 2) * Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_left (by positivity) hlhalf hT
      _ = _ := by ring
  unfold countConversionLossBound
  calc
    _ ≤ (C * x / Real.log x ^ 4 + C * x / Real.log x ^ 4) +
        5 * (⌈countCutoff x⌉₊ : ℝ) + (3 / 2) * x.primeFactors.card := by
      linarith only [hmain, hcorr]
    _ = _ := by ring

theorem eventually_count_conversion_error_le (C : ℝ) (hC : 0 ≤ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, 1 < countCutoff x ∧
      ∀ E : ℝ, E ≤ C * x / Real.log x ^ 3 →
        E / Real.log x + (1 / 2) * (E / Real.log (countCutoff x)) +
          5 * (⌈countCutoff x⌉₊ : ℝ) + (3 / 2) * x.primeFactors.card ≤
            δ * ((x : ℝ) * chenConst x / Real.log x ^ 2) := by
  filter_upwards [eventually_countConversionLossBound_le C δ hδ,
    eventually_log_countCutoff (1 / 2) (by norm_num) (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with x hloss hT hx
  refine ⟨hT.1, fun E hE => ?_⟩
  have hT' : (1 / 2) * Real.log x ≤ Real.log (countCutoff x) := by
    have ht := hT.2
    norm_num at ht ⊢
    exact ht
  exact (count_conversion_error_le x (by omega) C hC E hE hT').trans hloss

end Chen.LinearSieve
