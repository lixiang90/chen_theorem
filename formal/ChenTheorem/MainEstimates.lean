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
estimates by proved finite and algebraic reductions in `Lemma5.lean`.
-/
import ChenTheorem.Lemma5

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

/-- Equations (5)–(11): after the principal-character contribution `M₁`,
the nonprincipal contribution is bounded by `M₂`; the `M₃` and `M₅`
remainders have a fixed power saving. -/
theorem sieveM_le_mOne_add_mTwo_power_bound
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      sieveM x ≤ mOne x ε + mTwo x ε +
        C * (x : ℝ) ^ (1 - ε / 3) := by
  sorry

/-- Logarithmic-error form of equations (5)–(11). -/
theorem sieveM_le_mOne_add_mTwo
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      sieveM x ≤ mOne x ε + mTwo x ε +
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C, hC, hM⟩ :=
    sieveM_le_mOne_add_mTwo_power_bound ε hε hε'
  refine ⟨C, hC, ?_⟩
  filter_upwards [hM,
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := ε / 3) (r := (2.01 : ℝ)) (by positivity)] with x hx hpower
  intro hxEven
  have hmul :
      C * (x : ℝ) ^ (1 - ε / 3) ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hpower hC.le)
  linarith [hx hxEven]

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
