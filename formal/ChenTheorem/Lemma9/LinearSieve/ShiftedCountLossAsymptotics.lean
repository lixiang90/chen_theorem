import ChenTheorem.Lemma9.LinearSieve.CountLossAsymptotics

open Filter
open scoped Classical

namespace Chen.LinearSieve

theorem eventually_countCutoff_add_shift_le (h : ℕ) :
    ∀ᶠ x : ℕ in atTop, countCutoff x + h ≤ x := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop (2 * h)] with x hlog hx
  have hl : 2 ≤ Real.log (x : ℝ) := hlog
  have hden : 2 ≤ Real.log x ^ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := by gcongr
  have hcut : countCutoff x ≤ (x : ℝ) / 2 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg x) (by norm_num) hden
  have hh : 2 * (h : ℝ) ≤ x := by exact_mod_cast hx
  linarith

noncomputable def shiftedCountConversionLossBound (h : ℕ) (C : ℝ) (x : ℕ) : ℝ :=
  2 * C * x / Real.log x ^ 4 + 5 * (⌈countCutoff x⌉₊ : ℝ) +
    (3 / 2) * h.primeFactors.card

theorem shiftedCountConversionLossBound_normalized_tendsto (h : ℕ) (C : ℝ) :
    Tendsto (fun x : ℕ => shiftedCountConversionLossBound h C x * Real.log x ^ 2 / x)
      atTop (nhds 0) := by
  have hp := ((inv_log_pow_tendsto 2 (by norm_num)).const_mul (2 * C)).add
    ((ceil_countCutoff_normalized_tendsto.const_mul 5).add
      ((log_pow_div_nat_tendsto 2).const_mul ((3 / 2) * (h.primeFactors.card : ℝ))))
  simp only [mul_zero, zero_add] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hl : Real.log (x : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  dsimp only [shiftedCountConversionLossBound]
  field_simp
  ring

theorem eventually_le_fixed_chen_scale_of_normalized_tendsto
    (h : ℕ) (f : ℕ → ℝ)
    (hf : Tendsto (fun x : ℕ => f x * Real.log x ^ 2 / x) atTop (nhds 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, f x ≤ δ * ((x : ℝ) * chenConst h / Real.log x ^ 2) := by
  have hC : 0 < chenConst h := twinConst_pos.trans_le (twinConst_le_chenConst h)
  have hp := hf.eventually (eventually_lt_nhds (mul_pos hδ hC))
  filter_upwards [hp, eventually_ge_atTop (2 : ℕ)] with x hx hx2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hlpos)).mpr
  have hmul := (div_lt_iff₀ hxpos).mp hx
  nlinarith

/-- All shifted count-conversion errors are negligible on the exact
fixed-shift singular-series scale. The cutoff also satisfies the range
condition required by the small-prime multiplicity bound. -/
theorem eventually_shifted_count_conversion_error_le (h : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, 1 < countCutoff x ∧ countCutoff x + h ≤ x ∧
      ∀ E : ℝ, E ≤ C * x / Real.log x ^ 3 →
        E / Real.log x + (1 / 2) * (E / Real.log (countCutoff x)) +
          5 * (⌈countCutoff x⌉₊ : ℝ) + (3 / 2) * h.primeFactors.card ≤
            δ * ((x : ℝ) * chenConst h / Real.log x ^ 2) := by
  have hloss := eventually_le_fixed_chen_scale_of_normalized_tendsto h _
    (shiftedCountConversionLossBound_normalized_tendsto h C) δ hδ
  filter_upwards [hloss, eventually_countCutoff_add_shift_le h,
    eventually_log_countCutoff (1 / 2) (by norm_num) (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with x hloss hTx hT hx
  refine ⟨hT.1, hTx, fun E hE => ?_⟩
  have hT' : (1 / 2) * Real.log x ≤ Real.log (countCutoff x) := by
    have ht := hT.2
    norm_num at ht ⊢
    exact ht
  have hb := count_conversion_error_le x (by omega) C hC E hE hT'
  unfold countConversionLossBound at hb
  unfold shiftedCountConversionLossBound at hloss
  linarith

end Chen.LinearSieve
