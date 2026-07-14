/-
The main estimates: Lemmas 5–9 of Chen's paper.

* Lemmas 5 & 6 (combined) : `Ω ≤ M₁/(1-ε) + O(x/(log x)^{2.01})`.
  (The paper splits this into Lemma 5, the decomposition `Ω ≤ (M₁+M₂)/(1-ε) + …`,
  and Lemma 6, the bound `M₂ ≪ x/(log x)^{2.01}` proved with the toolbox of
  Lemmas 1–4 — the large sieve, the `L`-function fourth moment and the
  zero-free region.  `M₂` involves a contour integral of `L'/L` which we do not
  reproduce here; we state the combined outcome.)
* Lemma 7 : the upper bound for `M₁` in terms of `x C_x / log x`.
* Lemma 8 : the numerical bound `Ω ≤ 3.9404 x C_x / (log x)²`.
* Lemma 9 : the lower bound
  `P_x(x, x^{1/10}) - (1/2) ∑_{x^{1/10} < p ≤ x^{1/3}} P_x(x, p, x^{1/10})
     ≥ 2.6408 x C_x / (log x)²`,
  proved in the paper via Bombieri's theorem and Richert's weighted sieve [11].

All proofs are `sorry`-placeholders; the statements are the formalization targets.
-/
import ChenTheorem.SieveLemmas

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

/-! ### Lemmas 5 and 6 -/

/-- **Lemmas 5 & 6 (combined)**: for even `x`,
`Ω ≤ M₁/(1-ε) + O(x/(log x)^{2.01})`. -/
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
