import ChenTheorem.Main.ShiftedLemma8

open Filter Real
open scoped Classical

namespace Chen

/-! # Fixed-shift analogue of Lemma 9

As in the original Lemma 9, the only non-elementary input is the combined
specialization of Richert's weighted sieve and Bombieri--Vinogradov.  The
fixed residue `-h` changes the progression but not the sieve calculation.
The external specialization is isolated below; equation (27), loss
management, and the numerical constant are checked in Lean.
-/

/-- Fixed-shift specialization of Richert's weighted sieve and the
Bombieri--Vinogradov averaged progression estimate, corresponding to equations
(25)--(26). -/
axiom eventually_shifted_richert_bombieri_equation26
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) *
          ((x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 + equation27Integral) ≤
        (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ)

/-- The named fixed-shift Richert--Bombieri interface. -/
theorem shifted_richert_weighted_sieve_estimate
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) *
          ((x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 + equation27Integral) ≤
        (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) := by
  exact eventually_shifted_richert_bombieri_equation26
    h hh0 hhEven δ hδ

/-- Fixed-shift Richert--Bombieri estimate after inserting equation (27). -/
theorem shifted_richert_weighted_sieve_final_estimate
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ < 8) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) *
          ((x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 - 0.0164725) ≤
        (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) := by
  filter_upwards [
      shifted_richert_weighted_sieve_estimate h hh0 hhEven δ hδ,
      eventually_gt_atTop 1] with x hrichert hx
  intro hxEven
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hconst : 0 < chenConst h :=
    twinConst_pos.trans_le (twinConst_le_chenConst h)
  have hscale :
      0 ≤ (8 - δ) *
        ((x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2) := by
    positivity
  have hbracket :
      Real.log 4 - Real.log 8 / 2 - 0.0164725 ≤
        Real.log 4 - Real.log 8 / 2 + equation27Integral := by
    linarith [equation27_integral_bound]
  calc
    (8 - δ) *
        ((x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2) *
        (Real.log 4 - Real.log 8 / 2 - 0.0164725) ≤
      (8 - δ) *
        ((x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2) *
        (Real.log 4 - Real.log 8 / 2 + equation27Integral) := by
      exact mul_le_mul_of_nonneg_left hbracket hscale
    _ ≤ (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) :=
      hrichert hxEven

/-- **Shifted Lemma 9**: the lower-bound sieve has the same numerical
coefficient as in the original lemma, with singular series `C_h`. -/
theorem shiftedSieved_lower_bound
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h) :
    ∀ᶠ x : ℕ in atTop, Even x →
      2.6408 * (x : ℝ) * chenConst h /
          Real.log (x : ℝ) ^ 2 ≤
        (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) := by
  let δ : ℝ := 0.000001
  have hδ : 0 < δ := by norm_num [δ]
  filter_upwards [
      shifted_richert_weighted_sieve_final_estimate
        h hh0 hhEven δ hδ (by norm_num [δ]),
      eventually_gt_atTop 1] with x hrichert hx
  intro hxEven
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
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
  have hconst : 0 < chenConst h :=
    twinConst_pos.trans_le (twinConst_le_chenConst h)
  have hmainNonneg :
      0 ≤ (x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2 := by
    positivity
  have hrichert' := hrichert hxEven
  calc
    2.6408 * (x : ℝ) * chenConst h /
        Real.log (x : ℝ) ^ 2 ≤
      ((8 - δ) *
        (Real.log 4 - Real.log 8 / 2 - 0.0164725)) *
          ((x : ℝ) * chenConst h /
            Real.log (x : ℝ) ^ 2) := by
      calc
        2.6408 * (x : ℝ) * chenConst h /
            Real.log (x : ℝ) ^ 2 =
          2.6408 * ((x : ℝ) * chenConst h /
            Real.log (x : ℝ) ^ 2) := by ring
        _ ≤ ((8 - δ) *
            (Real.log 4 - Real.log 8 / 2 - 0.0164725)) *
              ((x : ℝ) * chenConst h /
                Real.log (x : ℝ) ^ 2) := by
          gcongr
    _ ≤ (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrichert'

end Chen
