/-
The elementary logarithmic-derivative bound suppressed between equations
(16) and (17) in Chen's proof of Lemma 6.

For `Re s = 1 + δ`, the untwisted von Mangoldt series majorizing `L'/L`
is at most `4 / δ²`.  The proof uses `Λ(n) ≤ log n`, the inequality
`log n ≤ n^(δ/2)/(δ/2)`, and the integral test for the remaining p-series.
-/
import ChenTheorem.Lemma6.AnalyticDecomposition
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real Set MeasureTheory
open scoped Classical

namespace Chen

set_option maxHeartbeats 800000 in
/-- If `Re s = 1 + δ`, the von Mangoldt majorant is `O(δ⁻²)`. -/
theorem lemma6LogDerivMajorant_le
    {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsre : s.re = 1 + δ) :
    lemma6LogDerivMajorant s ≤ 4 / δ ^ 2 := by
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let a : ℝ := δ / 2
  let p : ℝ := 1 + δ / 2
  have hone : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
  have ha : 0 < a := by dsimp only [a]; linarith
  have hp : 1 < p := by dsimp only [p]; linarith
  have hs : 1 < s.re := by rw [hsre]; linarith
  have hΛ : LSeriesSummable Λ s := by
    simpa only [Λ] using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hΛnorm : Summable (fun n => ‖LSeries.term Λ s n‖) := by
    rw [summable_norm_iff]
    exact hΛ
  have hsplit := hΛnorm.sum_add_tsum_nat_add 2
  have hmajorEq : lemma6LogDerivMajorant s =
      ∑' n : ℕ, ‖LSeries.term Λ s (n + 2)‖ := by
    unfold lemma6LogDerivMajorant
    change (∑' n : ℕ, ‖LSeries.term Λ s n‖) = _
    rw [← hsplit]
    norm_num [Finset.sum_range_succ, Λ, LSeries.norm_term_eq,
      ArithmeticFunction.vonMangoldt_apply]
  have hlog (n : ℕ) (hn : 2 ≤ n) :
      Real.log (n : ℝ) ≤ (n : ℝ) ^ a / a := by
    have hnpos : 0 < (n : ℝ) := by positivity
    have hpowpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos _
    have hbasic := Real.log_le_sub_one_of_pos hpowpos
    rw [Real.log_rpow hnpos] at hbasic
    rw [le_div_iff₀ ha]
    nlinarith
  have hterm (n : ℕ) :
      ‖LSeries.term Λ s (n + 2)‖ ≤
        (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
    have hn : 2 ≤ n + 2 := by omega
    have hn0 : n + 2 ≠ 0 := by omega
    have hnpos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [LSeries.norm_term_eq]
    simp only [hn0, if_false]
    have hΛlog : ‖Λ (n + 2)‖ ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
      simpa only [Λ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
          (ArithmeticFunction.vonMangoldt_le_log (n := n + 2))
    calc
      ‖Λ (n + 2)‖ / ((n + 2 : ℕ) : ℝ) ^ s.re ≤
          Real.log ((n + 2 : ℕ) : ℝ) /
            ((n + 2 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right hΛlog (Real.rpow_pos_of_pos hnpos _).le
      _ ≤ ((((n + 2 : ℕ) : ℝ) ^ a) / a) /
            ((n + 2 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right (hlog (n + 2) hn)
          (Real.rpow_pos_of_pos hnpos _).le
      _ = (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
        calc
          ((((n + 2 : ℕ) : ℝ) ^ a) / a) /
              ((n + 2 : ℕ) : ℝ) ^ s.re =
            (1 / a) * ((((n + 2 : ℕ) : ℝ) ^ a) /
              ((n + 2 : ℕ) : ℝ) ^ s.re) := by ring
          _ = (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (a - s.re) := by
            rw [Real.rpow_sub hnpos]
          _ = (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
            rw [hsre]
            dsimp only [a, p]
            ring_nf
  have hpowSummable :
      Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-p)) := by
    exact (summable_nat_add_iff 2).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hscaledSummable :
      Summable (fun n : ℕ => (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p)) :=
    hpowSummable.mul_left _
  have hcompare :
      (∑' n : ℕ, ‖LSeries.term Λ s (n + 2)‖) ≤
        ∑' n : ℕ, (1 / a) * ((n + 2 : ℕ) : ℝ) ^ (-p) := by
    have htailNorm :
        Summable (fun n : ℕ => ‖LSeries.term Λ s (n + 2)‖) :=
      (summable_nat_add_iff 2).mpr hΛnorm
    exact htailNorm.tsum_le_tsum hterm hscaledSummable
  let f : ℝ → ℝ := fun t => t ^ (-p)
  have hanti : AntitoneOn f (Set.Ici ((1 : ℕ) : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show -p ≤ 0 by linarith)).mono
    intro t ht
    change 0 < t
    rw [Set.mem_Ici] at ht
    exact hone.trans_le ht
  have hint : IntegrableOn f (Set.Ioi ((1 : ℕ) : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hone
  have hnonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ f t := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    exact Real.rpow_nonneg (hone.trans ht).le _
  have htail := AntitoneOn.tsum_comp_add_le_integral
    (f := f) (1 : ℕ) hanti hint hnonneg
  have hintegral :
      (∫ t in Set.Ioi ((1 : ℕ) : ℝ), f t) = 1 / (p - 1) := by
    dsimp only [f]
    rw [integral_Ioi_rpow_of_lt (by linarith) hone]
    norm_num only [Nat.cast_one, one_rpow]
    field_simp
    ring
  have htail' :
      (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p)) ≤ 1 / (p - 1) := by
    rw [hintegral] at htail
    have hadd :
        (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-p)) =
          (fun n : ℕ => f ((n + 1 + 1 : ℕ) : ℝ)) := by
      funext n
      dsimp only [f]
    rw [hadd]
    exact htail
  rw [hmajorEq]
  apply hcompare.trans
  rw [tsum_mul_left]
  calc
    (1 / a) * (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-p)) ≤
        (1 / a) * (1 / (p - 1)) := by
      gcongr
    _ = 4 / δ ^ 2 := by
      dsimp only [a, p]
      field_simp [hδ.ne']
      ring

/-- On Chen's line `α = 1 + 1/log x`, the majorant costs at most
`4 (log x)²`. -/
theorem lemma6LogDerivMajorant_alpha_le
    {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    lemma6LogDerivMajorant (lemma6AlphaPoint x ν) ≤
      4 * Real.log (x : ℝ) ^ 2 := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hδ : 0 < (1 : ℝ) / Real.log (x : ℝ) :=
    div_pos zero_lt_one hlog
  calc
    lemma6LogDerivMajorant (lemma6AlphaPoint x ν) ≤
        4 / ((1 : ℝ) / Real.log (x : ℝ)) ^ 2 :=
      lemma6LogDerivMajorant_le hδ (lemma6AlphaPoint_re x ν)
    _ = 4 * Real.log (x : ℝ) ^ 2 := by
      field_simp [hlog.ne']

end Chen
