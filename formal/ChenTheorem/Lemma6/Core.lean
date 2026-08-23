/-
Lemma 6 of Chen's paper: reduction of the primitive-character remainder to
dyadic character blocks and the final logarithmic-power deduction.

The finite `lemma6Nm` below is the Mellin-inverted form of Chen's `N_m`.
Equation (12) is isolated from the estimates (13), (19), (20), and (21), so
the remaining analytic work has the same boundaries as the paper.
-/
import ChenTheorem.Lemma6.Coefficients
import ChenTheorem.Lemma6.Integration
import ChenTheorem.Lemma6.Parameters
import ChenTheorem.Lemma6.SmoothingMellin
import ChenTheorem.Lemma6.ContourShift
import ChenTheorem.Lemma6.BIntegrability
import ChenTheorem.Lemma6.Equation20
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option warn.sorry false

open Filter Real MeasureTheory ENNReal
open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- The primitive-character block of conductor `l` occurring in `N_m`.
Here `m` is the original (possibly imprimitive) modulus, which remains in the
coprimality condition after regrouping characters by conductor. -/
noncomputable def lemma6PrimitiveBlock (x m l : ℕ) : ℂ :=
  primComplexSum l (fun χ =>
    starRingEnd ℂ (χ (x : ZMod l)) *
      ∑ q ∈ (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) m),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))

/-- The `k`-th prime-pair piece of a primitive conductor block. -/
noncomputable def lemma6PrimitivePairBlock
    (x m l k : ℕ) : ℂ :=
  primComplexSum l (fun χ =>
    starRingEnd ℂ (χ (x : ZMod l)) *
      ∑ q ∈ (lemma6AdmissiblePairs x m).filter
          (fun q => q ∈ lemma6PairBlock x k),
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))

/-- Mellin inversion inserted directly into one nonzero smoothed
von-Mangoldt summand.  This is the termwise bridge from the finite model
in `lemma6PrimitivePairBlock` to Chen's `α`-line contour integral. -/
theorem lemma6_smoothedMKernel_eq_verticalIntegral
    {x n : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime) (hn : 0 < n) :
    (smoothedMKernel x q n : ℂ) =
      (((Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ ν : ℝ,
            (((x : ℝ) / ((q.1 : ℝ) * q.2 * n) : ℝ) : ℂ) ^
                (lemma6AlphaPoint x ν) *
              lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)) := by
  have hxreal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlog _
  have horder : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    exact hxlog
  have hσ : 0 < 1 + 1 / Real.log (x : ℝ) := by positivity
  have hy : 0 < (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by
    have hxpos : 0 < (x : ℝ) := by positivity
    have hq₁pos : 0 < (q.1 : ℝ) := by exact_mod_cast hq₁.pos
    have hq₂pos : 0 < (q.2 : ℝ) := by exact_mod_cast hq₂.pos
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    exact div_pos hxpos (mul_pos (mul_pos hq₁pos hq₂pos) hnpos)
  have hphi := chenPhi_eq_smoothing_verticalIntegral
    hxreal ha horder hσ hy
  have hpoint (ν : ℝ) :
      (((1 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) +
        (ν : ℂ) * Complex.I) = lemma6AlphaPoint x ν := by
    unfold lemma6AlphaPoint
    push_cast
    ring
  simp_rw [hpoint] at hphi
  unfold smoothedMKernel
  push_cast
  rw [hphi]
  push_cast
  rfl

/-- The exact finite Mellin integrand attached to one `(p₁,p₂,n)` term
and one Dirichlet character.  At this stage the finite cutoff is retained;
identification with the full logarithmic derivative is a separate, genuinely
infinite interchange. -/
noncomputable def lemma6FiniteMellinSummand
    {l : ℕ} (x : ℕ) (q : ℕ × ℕ) (n : ℕ)
    (χ : DirichletCharacter ℂ l) (ν : ℝ) : ℂ :=
  (((Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    ((((x : ℝ) / ((q.1 : ℝ) * q.2 * n) : ℝ) : ℂ) ^
        lemma6AlphaPoint x ν *
      lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)) *
    χ (q.1 * q.2 * n : ZMod l)

/-- A positive-real quotient to a complex power splits into the natural
number factors used by an L-series term. -/
theorem lemma6_nat_quotient_cpow_factor
    (x n : ℕ) (q : ℕ × ℕ) (s : ℂ) :
    (((x : ℝ) / ((q.1 : ℝ) * q.2 * n) : ℝ) : ℂ) ^ s =
      (x : ℂ) ^ s /
        (((q.1 * q.2 : ℕ) : ℂ) ^ s * (n : ℂ) ^ s) := by
  have hcast : (((x : ℝ) / ((q.1 : ℝ) * q.2 * n) : ℝ) : ℂ) =
      (x : ℂ) * (((q.1 * q.2 * n : ℕ) : ℂ)⁻¹) := by
    push_cast
    field_simp
  rw [hcast]
  have hnatcast : (((q.1 * q.2 * n : ℕ) : ℂ)) =
      ((((q.1 * q.2 * n : ℕ) : ℝ) : ℂ)) := by norm_cast
  have hxcast : (x : ℂ) = (((x : ℝ) : ℂ)) := by norm_cast
  rw [hnatcast, hxcast, ← Complex.ofReal_inv]
  rw [Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg x)
      (inv_nonneg.mpr (Nat.cast_nonneg (q.1 * q.2 * n))) s,
    Complex.ofReal_inv, Complex.inv_cpow]
  · rw [← hnatcast]
    rw [show ((q.1 * q.2 * n : ℕ) : ℂ) =
      ((q.1 * q.2 : ℕ) : ℂ) * (n : ℂ) by norm_cast]
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  · rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
    exact Real.pi_ne_zero.symm

/-- One contour summand factors as a fixed prime-pair factor times the
corresponding twisted von Mangoldt L-series term. -/
theorem lemma6FiniteMellinSummand_eq_pairFactor_mul_LSeriesTerm
    {x n l : ℕ} {q : ℕ × ℕ} (χ : DirichletCharacter ℂ l) (ν : ℝ) :
    lemma6FiniteMellinSummand x q n χ ν =
      (((x : ℂ) ^ lemma6AlphaPoint x ν) *
          lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x ν)) *
        (χ (q.1 * q.2 : ZMod l) /
          ((((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x ν) *
            (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ))) *
        LSeries.term
          (fun r : ℕ => χ r *
            (ArithmeticFunction.vonMangoldt r : ℂ))
          (lemma6AlphaPoint x ν) n := by
  by_cases hn0 : n = 0
  · subst n
    simp [lemma6FiniteMellinSummand, ArithmeticFunction.map_zero]
  · have hχmul :
        χ (q.1 * q.2 * n : ZMod l) =
          χ (q.1 * q.2 : ZMod l) * χ (n : ZMod l) := by
      simpa only [Nat.cast_mul] using
        map_mul χ (q.1 * q.2 : ZMod l) (n : ZMod l)
    unfold lemma6FiniteMellinSummand
    rw [lemma6_nat_quotient_cpow_factor,
      LSeries.term_of_ne_zero hn0, hχmul]
    push_cast
    simp only [div_eq_mul_inv]
    ring

/-- Summing the factored terms recovers the twisted von Mangoldt L-series. -/
theorem tsum_lemma6FiniteMellinSummand_eq_pairFactor_mul_LSeries
    {x l : ℕ} {q : ℕ × ℕ} (χ : DirichletCharacter ℂ l) (ν : ℝ) :
    (∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν) =
      (((x : ℂ) ^ lemma6AlphaPoint x ν) *
          lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x ν)) *
        (χ (q.1 * q.2 : ZMod l) /
          ((((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x ν) *
            (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ))) *
        LSeries
          (fun r : ℕ => χ r *
            (ArithmeticFunction.vonMangoldt r : ℂ))
          (lemma6AlphaPoint x ν) := by
  let C : ℂ :=
    (((x : ℂ) ^ lemma6AlphaPoint x ν) *
        lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x ν)) *
      (χ (q.1 * q.2 : ZMod l) /
        ((((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x ν) *
          (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ)))
  calc
    (∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν) =
        ∑' n : ℕ, C * LSeries.term
          (fun r : ℕ => χ r *
            (ArithmeticFunction.vonMangoldt r : ℂ))
          (lemma6AlphaPoint x ν) n := by
      apply tsum_congr
      intro n
      exact lemma6FiniteMellinSummand_eq_pairFactor_mul_LSeriesTerm χ ν
    _ = C * ∑' n : ℕ, LSeries.term
          (fun r : ℕ => χ r *
            (ArithmeticFunction.vonMangoldt r : ℂ))
          (lemma6AlphaPoint x ν) n := tsum_mul_left
    _ = _ := rfl

/-- The full twisted von Mangoldt L-series on the `α`-line is the negative
logarithmic derivative of the Dirichlet L-function. -/
theorem lemma6_LSeries_twist_vonMangoldt_eq_neg_logDeriv_at_alpha
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (χ : DirichletCharacter ℂ l) (ν : ℝ) :
    LSeries
        (fun r : ℕ => χ r *
          (ArithmeticFunction.vonMangoldt r : ℂ))
        (lemma6AlphaPoint x ν) =
      -(deriv (DirichletCharacter.LFunction χ)
          (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν)) := by
  have hs := one_lt_lemma6AlphaPoint_re hx ν
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hseq :
      (fun r : ℕ => χ r) *
          (fun r : ℕ => (ArithmeticFunction.vonMangoldt r : ℂ)) =
        (fun r : ℕ => χ r *
          (ArithmeticFunction.vonMangoldt r : ℂ)) := by
    funext r
    rfl
  rw [hseq] at h
  have h' :
      LSeries
          (fun r : ℕ => χ r *
            (ArithmeticFunction.vonMangoldt r : ℂ))
          (lemma6AlphaPoint x ν) =
        -deriv (LSeries (fun r : ℕ => χ r))
            (lemma6AlphaPoint x ν) /
          LSeries (fun r : ℕ => χ r) (lemma6AlphaPoint x ν) := by
    exact h
  exact h'.trans (by
    rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      ← DirichletCharacter.LFunction_eq_LSeries χ hs]
    ring)

/-- Pointwise identification of the full `n`-series with the prime-pair
factor times `-L'/L`. -/
theorem tsum_lemma6FiniteMellinSummand_eq_neg_pairFactor_mul_logDeriv
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x) {q : ℕ × ℕ}
    (χ : DirichletCharacter ℂ l) (ν : ℝ) :
    (∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν) =
      -((((x : ℂ) ^ lemma6AlphaPoint x ν) *
          lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x ν)) *
        (χ (q.1 * q.2 : ZMod l) /
          ((((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x ν) *
            (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ))) *
        (deriv (DirichletCharacter.LFunction χ)
            (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))) := by
  rw [tsum_lemma6FiniteMellinSummand_eq_pairFactor_mul_LSeries,
    lemma6_LSeries_twist_vonMangoldt_eq_neg_logDeriv_at_alpha hx χ ν]
  ring

/-- Every nonzero finite Mellin summand is integrable on Chen's `α`-line. -/
theorem integrable_lemma6FiniteMellinSummand_of_pos
    {x n l : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime) (hn : 0 < n)
    (χ : DirichletCharacter ℂ l) :
    Integrable (lemma6FiniteMellinSummand x q n χ) := by
  have hxreal : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlog _
  have horder : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    exact hxlog
  have hσ : 0 < 1 + 1 / Real.log (x : ℝ) := by positivity
  have hy : 0 < (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by
    have hq₁pos : 0 < (q.1 : ℝ) := by exact_mod_cast hq₁.pos
    have hq₂pos : 0 < (q.2 : ℝ) := by exact_mod_cast hq₂.pos
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hbase := integrable_cpow_mul_lemma6SmoothingMellinKernel
    hy ha horder hσ
  have hpoint (ν : ℝ) :
      (((1 + 1 / Real.log (x : ℝ) : ℝ) : ℂ) +
        (ν : ℂ) * Complex.I) = lemma6AlphaPoint x ν := by
    unfold lemma6AlphaPoint
    push_cast
    ring
  simp_rw [hpoint] at hbase
  exact (hbase.const_mul
    (((Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
      ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)).mul_const
        (χ (q.1 * q.2 * n : ZMod l))

/-- The `n = 0` summand is identically zero and hence integrable. -/
theorem integrable_lemma6FiniteMellinSummand_zero
    {x l : ℕ} (q : ℕ × ℕ) (χ : DirichletCharacter ℂ l) :
    Integrable (lemma6FiniteMellinSummand x q 0 χ) := by
  have hzero : lemma6FiniteMellinSummand x q 0 χ = 0 := by
    funext ν
    unfold lemma6FiniteMellinSummand
    rw [ArithmeticFunction.map_zero]
    norm_num
  rw [hzero]
  exact integrable_zero ℝ ℂ volume

/-- Uniform finite-summand integrability, including the harmless zero
index. -/
theorem integrable_lemma6FiniteMellinSummand
    {x n l : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    Integrable (lemma6FiniteMellinSummand x q n χ) := by
  by_cases hn0 : n = 0
  · subst n
    exact integrable_lemma6FiniteMellinSummand_zero q χ
  · exact integrable_lemma6FiniteMellinSummand_of_pos hx hxlog hq₁ hq₂
      (Nat.pos_of_ne_zero hn0) χ

/-- Outside the finite set `smoothedMIndices`, the smoothing argument is at
most one and the corresponding kernel vanishes.  This is the arithmetic
support fact needed to extend the finite sum only after integration. -/
theorem smoothedMKernel_eq_zero_of_not_mem
    {x n : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime)
    (hnmem : n ∉ smoothedMIndices x q) :
    smoothedMKernel x q n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    unfold smoothedMKernel
    rw [ArithmeticFunction.map_zero]
    ring
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hq₁pos : 0 < (q.1 : ℝ) := by exact_mod_cast hq₁.pos
  have hq₂pos : 0 < (q.2 : ℝ) := by exact_mod_cast hq₂.pos
  have hqprod : 0 < (q.1 : ℝ) * q.2 := mul_pos hq₁pos hq₂pos
  have hden : 0 < (q.1 : ℝ) * q.2 * n := by positivity
  have hnoutside := hnmem
  simp only [smoothedMIndices, Finset.mem_filter,
    Finset.mem_range, not_and_or] at hnoutside
  have hxprod : (x : ℝ) ≤ (q.1 : ℝ) * q.2 * n := by
    rcases hnoutside with hnrange | hnineq
    · have hxn : (x : ℝ) < n := by
        exact_mod_cast (show x < n by omega)
      have hqone : (1 : ℝ) ≤ (q.1 : ℝ) * q.2 := by
        have hq₁one : (1 : ℝ) ≤ q.1 := by exact_mod_cast hq₁.one_le
        have hq₂one : (1 : ℝ) ≤ q.2 := by exact_mod_cast hq₂.one_le
        nlinarith [mul_nonneg (sub_nonneg.mpr hq₁one)
          (sub_nonneg.mpr hq₂one)]
      calc
        (x : ℝ) ≤ n := hxn.le
        _ ≤ (q.1 : ℝ) * q.2 * n := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hqone)
            (Nat.cast_nonneg n)]
    · have hlt : (x : ℝ) < (n : ℝ) * ((q.1 : ℝ) * q.2) :=
        (div_lt_iff₀ hqprod).mp (lt_of_not_ge hnineq)
      nlinarith
  have hy0 : 0 ≤ (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
  have hy1 : (x : ℝ) / ((q.1 : ℝ) * q.2 * n) ≤ 1 :=
    (div_le_one hden).2 hxprod
  have hxreal : (1 : ℝ) < x := by
    exact_mod_cast (show 1 < x by omega)
  unfold smoothedMKernel
  rw [chenPhi_eq_zero hxreal hy0 hy1]
  ring

/-- Mellin inversion after multiplying by the character value.  This form
is designed for direct finite summation and records the zero-index case
explicitly. -/
theorem lemma6_smoothedMKernel_mul_char_eq_verticalIntegral
    {x n l : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    (smoothedMKernel x q n : ℂ) *
        χ (q.1 * q.2 * n : ZMod l) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ, lemma6FiniteMellinSummand x q n χ ν := by
  by_cases hn0 : n = 0
  · subst n
    simp [smoothedMKernel, lemma6FiniteMellinSummand]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let c : ℂ :=
      ((Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        ArithmeticFunction.vonMangoldt n : ℝ)
    let f : ℝ → ℂ := fun ν =>
      (((x : ℝ) / ((q.1 : ℝ) * q.2 * n) : ℝ) : ℂ) ^
          lemma6AlphaPoint x ν *
        lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)
    let z : ℂ := χ (q.1 * q.2 * n : ZMod l)
    have h := congrArg
      (fun w : ℂ => w * z)
      (lemma6_smoothedMKernel_eq_verticalIntegral hx hxlog hq₁ hq₂ hn)
    change (smoothedMKernel x q n : ℂ) * z =
      (c * ((1 / (2 * Real.pi) : ℝ) • ∫ ν : ℝ, f ν)) * z at h
    change (smoothedMKernel x q n : ℂ) * z =
      (1 / (2 * Real.pi) : ℝ) • ∫ ν : ℝ, c * f ν * z
    have hint : (∫ ν : ℝ, c * f ν * z) =
        c * (∫ ν : ℝ, f ν) * z := by
      calc
        (∫ ν : ℝ, c * f ν * z) =
            ∫ ν : ℝ, c * (f ν * z) := by
              apply integral_congr_ae
              filter_upwards with ν
              ring
        _ = c * ∫ ν : ℝ, f ν * z :=
          MeasureTheory.integral_const_mul c _
        _ = c * ((∫ ν : ℝ, f ν) * z) := by
          rw [MeasureTheory.integral_mul_const]
        _ = c * (∫ ν : ℝ, f ν) * z := by ring
    rw [hint]
    calc
      (smoothedMKernel x q n : ℂ) * z =
          (c * ((1 / (2 * Real.pi) : ℝ) •
            ∫ ν : ℝ, f ν)) * z := h
      _ = (1 / (2 * Real.pi) : ℝ) •
          (c * (∫ ν : ℝ, f ν) * z) := by
        simp only [RCLike.real_smul_eq_coe_mul]
        ring

/-- Every integrated term outside the finite cutoff is zero.  Notice that
the pointwise contour integrand itself need not vanish; this theorem is why
the finite-to-infinite extension must occur after integration. -/
theorem integral_lemma6FiniteMellinSummand_eq_zero_of_not_mem
    {x n l : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime)
    (χ : DirichletCharacter ℂ l)
    (hnmem : n ∉ smoothedMIndices x q) :
    (∫ ν : ℝ, lemma6FiniteMellinSummand x q n χ ν) = 0 := by
  have hterm := lemma6_smoothedMKernel_mul_char_eq_verticalIntegral
    hx hxlog hq₁ hq₂ (n := n) χ
  rw [smoothedMKernel_eq_zero_of_not_mem hx hq₁ hq₂ hnmem,
    Complex.ofReal_zero, zero_mul] at hterm
  have hscalar : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
  exact (smul_eq_zero.mp hterm.symm).resolve_left hscalar

/-- The integrated norms of the full `n`-family are summable on the
`α`-line.  This is the absolute-convergence input for the infinite
sum/integral interchange; its summable majorant is the untwisted von
Mangoldt L-series at `Re α > 1`. -/
theorem summable_integral_norm_lemma6FiniteMellinSummand
    {x l : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    Summable (fun n : ℕ =>
      ∫ ν : ℝ, ‖lemma6FiniteMellinSummand x q n χ ν‖) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  let a : ℝ := lemma6SmoothingScale (x : ℝ)
  let b : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let K : ℝ := ∫ ν : ℝ,
    ‖lemma6SmoothingMellinKernel (x : ℝ)
      ((σ : ℂ) + (ν : ℂ) * Complex.I)‖
  have hxreal : (1 : ℝ) < x := by
    exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσone : (1 : ℝ) < σ := by
    dsimp only [σ]
    have hinv : 0 < (1 : ℝ) / Real.log (x : ℝ) :=
      div_pos zero_lt_one hlog
    linarith
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hlog _
  have horder : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    exact hxlog
  have hqprod : 0 < (q.1 : ℝ) * q.2 := by
    exact mul_pos (by exact_mod_cast hq₁.pos) (by exact_mod_cast hq₂.pos)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hk : Integrable (fun ν : ℝ =>
      lemma6SmoothingMellinKernel (x : ℝ)
        ((σ : ℂ) + (ν : ℂ) * Complex.I)) := by
    have := verticalIntegrable_lemma6SmoothingMellinKernel ha horder hσ
    simpa only [Complex.VerticalIntegrable] using this
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    exact integral_nonneg fun _ => norm_nonneg _
  have hΛsum : Summable (fun n : ℕ =>
      ‖LSeries.term Λ (σ : ℂ) n‖) := by
    rw [summable_norm_iff]
    simpa only [Λ, LSeriesSummable] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt
        (s := (σ : ℂ)) (by simpa using hσone))
  let D : ℝ :=
    |(Real.log b)⁻¹| * b ^ σ * K
  have hmajor : Summable (fun n : ℕ =>
      D * ‖LSeries.term Λ (σ : ℂ) n‖) :=
    hΛsum.mul_left D
  apply hmajor.of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  by_cases hn0 : n = 0
  · subst n
    have hfunzero : lemma6FiniteMellinSummand x q 0 χ = 0 := by
      funext ν
      unfold lemma6FiniteMellinSummand
      rw [ArithmeticFunction.map_zero]
      norm_num
    simp only [hfunzero, Pi.zero_apply, norm_zero, integral_zero,
      LSeries.term_zero, mul_zero]
    exact le_rfl
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hy : 0 < (x : ℝ) / ((q.1 : ℝ) * q.2 * n) := by positivity
    have hpoint (ν : ℝ) :
        lemma6AlphaPoint x ν =
          (σ : ℂ) + (ν : ℂ) * Complex.I := by
      unfold lemma6AlphaPoint
      dsimp only [σ]
    have hnormfun : (fun ν : ℝ =>
        ‖lemma6FiniteMellinSummand x q n χ ν‖) =
      fun ν : ℝ =>
        (|(Real.log b)⁻¹| * ArithmeticFunction.vonMangoldt n *
            (((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) ^ σ) *
            ‖χ (q.1 * q.2 * n : ZMod l)‖) *
          ‖lemma6SmoothingMellinKernel (x : ℝ)
            ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ := by
      funext ν
      unfold lemma6FiniteMellinSummand
      simp only [norm_mul]
      rw [
        Complex.norm_cpow_eq_rpow_re_of_pos hy,
        lemma6AlphaPoint_re]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, hpoint]
      dsimp only [b, σ]
      ring
    rw [hnormfun, MeasureTheory.integral_const_mul]
    have hyfactor :
        ((x : ℝ) / ((q.1 : ℝ) * q.2 * n)) ^ σ =
          b ^ σ / (n : ℝ) ^ σ := by
      rw [show (x : ℝ) / ((q.1 : ℝ) * q.2 * n) = b / n by
        dsimp only [b]
        field_simp]
      exact Real.div_rpow hb.le hnreal.le σ
    have htermnorm :
        ‖LSeries.term Λ (σ : ℂ) n‖ =
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
      rw [LSeries.norm_term_eq]
      simp only [hn0, if_false, Λ, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.ofReal_re]
    rw [hyfactor, htermnorm]
    dsimp only [D]
    have hχnorm := χ.norm_le_one (q.1 * q.2 * n)
    have hΛnonneg := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hnpow : 0 < (n : ℝ) ^ σ :=
      Real.rpow_pos_of_pos hnreal σ
    let A : ℝ := |(Real.log b)⁻¹| * ArithmeticFunction.vonMangoldt n *
      (b ^ σ / (n : ℝ) ^ σ)
    have hA : 0 ≤ A := by
      dsimp only [A]
      positivity
    calc
      (|(Real.log b)⁻¹| * ArithmeticFunction.vonMangoldt n *
            (b ^ σ / (n : ℝ) ^ σ) *
            ‖χ (q.1 * q.2 * n : ZMod l)‖) * K =
          (A * K) * ‖χ (q.1 * q.2 * n : ZMod l)‖ := by
        dsimp only [A]
        ring
      _ ≤ (A * K) * 1 :=
        mul_le_mul_of_nonneg_left hχnorm (mul_nonneg hA hKnonneg)
      _ = (|(Real.log b)⁻¹| * ArithmeticFunction.vonMangoldt n *
            (b ^ σ / (n : ℝ) ^ σ)) * K := by
        dsimp only [A]
        ring
      _ = (|(Real.log b)⁻¹| * b ^ σ * K) *
          (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) := by ring

/-- A Bochner-series integrability criterion in the exact form needed
below.  Mathlib's `integral_tsum_of_summable_integral_norm` identifies the
integral, while this companion records that the pointwise sum itself is
integrable. -/
theorem integrable_tsum_of_summable_integral_norm_complex
    {F : ℕ → ℝ → ℂ}
    (hF_int : ∀ n, Integrable (F n))
    (hF_sum : Summable (fun n => ∫ a, ‖F n a‖)) :
    Integrable (fun a => ∑' n, F n a) := by
  refine ⟨MeasureTheory.AEStronglyMeasurable.tsum
    (fun n => (hF_int n).aestronglyMeasurable), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hlin (n : ℕ) :
      ∫⁻ a : ℝ, ‖F n a‖ₑ =
        ‖∫ a : ℝ, ‖F n a‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int n).norm,
      coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F n a)))]
    simp only [coe_nnnorm]
  have hsum_enorm :
      ∑' n : ℕ, ∫⁻ a : ℝ, ‖F n a‖ₑ ≠ ⊤ := by
    rw [funext hlin]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_coe.1 hF_sum.abs)
  calc
    ∫⁻ a : ℝ, ‖∑' n, F n a‖ₑ ≤
        ∫⁻ a : ℝ, ∑' n, ‖F n a‖ₑ :=
      lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' n : ℕ, ∫⁻ a : ℝ, ‖F n a‖ₑ :=
      lintegral_tsum (fun n => (hF_int n).aestronglyMeasurable.enorm)
    _ < ⊤ := lt_top_iff_ne_top.mpr hsum_enorm

/-- For a finite set of prime pairs, the full von Mangoldt series
aggregates pointwise to the prime-pair Dirichlet polynomial times
`-L'/L`.  Keeping the pair sum inside the polynomial is essential for the
subsequent pair large-sieve estimate. -/
theorem sum_tsum_lemma6FiniteMellinSummand_eq_pairPolynomial_logDeriv
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ))
    (χ : DirichletCharacter ℂ l) (ν : ℝ) :
    (∑ q ∈ pairs,
        ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν) =
      -(((x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x ν)) *
        lemma6PairDirichletPolynomial x pairs
          (lemma6AlphaPoint x ν) χ *
        (deriv (DirichletCharacter.LFunction χ)
            (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ
            (lemma6AlphaPoint x ν))) := by
  simp_rw [tsum_lemma6FiniteMellinSummand_eq_neg_pairFactor_mul_logDeriv
    hx χ ν]
  unfold lemma6PairDirichletPolynomial
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib]
  simp only [Nat.cast_mul]

/-- For one fixed prime pair, the finite cutoff may be replaced by the full
von Mangoldt series inside the contour integral.  Absolute convergence is
used for the sum/integral interchange, while vanishing of the inverse
Mellin integrals outside `smoothedMIndices` identifies the resulting tsum
of integrals with the original finite sum. -/
theorem integral_finset_lemma6FiniteMellinSummand_eq_integral_tsum
    {x l : ℕ} {q : ℕ × ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (hq₁ : q.1.Prime) (hq₂ : q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    (∫ ν : ℝ,
        ∑ n ∈ smoothedMIndices x q,
          lemma6FiniteMellinSummand x q n χ ν) =
      ∫ ν : ℝ,
        ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν := by
  have hint (n : ℕ) :
      Integrable (lemma6FiniteMellinSummand x q n χ) :=
    integrable_lemma6FiniteMellinSummand hx hxlog hq₁ hq₂ χ
  have hsum := summable_integral_norm_lemma6FiniteMellinSummand
    hx hxlog hq₁ hq₂ χ
  calc
    (∫ ν : ℝ,
        ∑ n ∈ smoothedMIndices x q,
          lemma6FiniteMellinSummand x q n χ ν) =
        ∑ n ∈ smoothedMIndices x q,
          ∫ ν : ℝ, lemma6FiniteMellinSummand x q n χ ν :=
      MeasureTheory.integral_finsetSum (smoothedMIndices x q)
        (fun n _ => hint n)
    _ = ∑' n : ℕ,
        ∫ ν : ℝ, lemma6FiniteMellinSummand x q n χ ν :=
      (tsum_eq_sum (s := smoothedMIndices x q) (fun n hn =>
        integral_lemma6FiniteMellinSummand_eq_zero_of_not_mem
          hx hxlog hq₁ hq₂ χ hn)).symm
    _ = ∫ ν : ℝ,
        ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν :=
      MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum

/-- After summing a finite prime-pair block, the exact finite Mellin
integral is the single `α`-line integral containing the pair Dirichlet
polynomial and `-L'/L`. -/
theorem integral_sum_finset_lemma6FiniteMellinSummand_eq_logDeriv
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ q ∈ pairs, q.1.Prime ∧ q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    (∫ ν : ℝ,
        ∑ q ∈ pairs,
          ∑ n ∈ smoothedMIndices x q,
            lemma6FiniteMellinSummand x q n χ ν) =
      ∫ ν : ℝ,
        -(((x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)) *
          lemma6PairDirichletPolynomial x pairs
            (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ)
              (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ
              (lemma6AlphaPoint x ν))) := by
  have hfinite (q : ℕ × ℕ) (hq : q ∈ pairs) :
      Integrable (fun ν : ℝ =>
        ∑ n ∈ smoothedMIndices x q,
          lemma6FiniteMellinSummand x q n χ ν) :=
    MeasureTheory.integrable_finsetSum (smoothedMIndices x q)
      (fun n _ => integrable_lemma6FiniteMellinSummand hx hxlog
        (hpairs q hq).1 (hpairs q hq).2 χ)
  have hfull (q : ℕ × ℕ) (hq : q ∈ pairs) :
      Integrable (fun ν : ℝ =>
        ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν) :=
    integrable_tsum_of_summable_integral_norm_complex
      (fun n => integrable_lemma6FiniteMellinSummand hx hxlog
        (hpairs q hq).1 (hpairs q hq).2 χ)
      (summable_integral_norm_lemma6FiniteMellinSummand
        hx hxlog (hpairs q hq).1 (hpairs q hq).2 χ)
  calc
    (∫ ν : ℝ,
        ∑ q ∈ pairs,
          ∑ n ∈ smoothedMIndices x q,
            lemma6FiniteMellinSummand x q n χ ν) =
        ∑ q ∈ pairs,
          ∫ ν : ℝ,
            ∑ n ∈ smoothedMIndices x q,
              lemma6FiniteMellinSummand x q n χ ν :=
      MeasureTheory.integral_finsetSum pairs hfinite
    _ = ∑ q ∈ pairs,
          ∫ ν : ℝ,
            ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν := by
      apply Finset.sum_congr rfl
      intro q hq
      exact integral_finset_lemma6FiniteMellinSummand_eq_integral_tsum
        hx hxlog (hpairs q hq).1 (hpairs q hq).2 χ
    _ = ∫ ν : ℝ,
          ∑ q ∈ pairs,
            ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν :=
      (MeasureTheory.integral_finsetSum pairs hfull).symm
    _ = ∫ ν : ℝ,
        -(((x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)) *
          lemma6PairDirichletPolynomial x pairs
            (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ)
              (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ
              (lemma6AlphaPoint x ν))) := by
      apply integral_congr_ae
      filter_upwards with ν
      exact sum_tsum_lemma6FiniteMellinSummand_eq_pairPolynomial_logDeriv
        hx pairs χ ν

/-- Exact finite `(p₁,p₂,n)` block after moving both finite sums through
the Mellin integral.  No full Dirichlet series, tail extension, or
logarithmic derivative is used in this theorem. -/
theorem lemma6_finiteMellin_sum_eq_verticalIntegral
    {x l : ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ q ∈ pairs, q.1.Prime ∧ q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    (∑ q ∈ pairs,
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l)) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          ∑ q ∈ pairs,
            ∑ n ∈ smoothedMIndices x q,
              lemma6FiniteMellinSummand x q n χ ν := by
  have hterm (q : ℕ × ℕ) (hq : q ∈ pairs) (n : ℕ)
      (_hn : n ∈ smoothedMIndices x q) :
      Integrable (lemma6FiniteMellinSummand x q n χ) :=
    integrable_lemma6FiniteMellinSummand hx hxlog
      (hpairs q hq).1 (hpairs q hq).2 χ
  have hinner (q : ℕ × ℕ) (hq : q ∈ pairs) :
      Integrable (fun ν : ℝ =>
        ∑ n ∈ smoothedMIndices x q,
          lemma6FiniteMellinSummand x q n χ ν) :=
    MeasureTheory.integrable_finsetSum (smoothedMIndices x q) (hterm q hq)
  have hsumint :
      (∫ ν : ℝ,
          ∑ q ∈ pairs,
            ∑ n ∈ smoothedMIndices x q,
              lemma6FiniteMellinSummand x q n χ ν) =
        ∑ q ∈ pairs,
          ∑ n ∈ smoothedMIndices x q,
            ∫ ν : ℝ, lemma6FiniteMellinSummand x q n χ ν := by
    rw [MeasureTheory.integral_finsetSum pairs hinner]
    apply Finset.sum_congr rfl
    intro q hq
    exact MeasureTheory.integral_finsetSum
      (smoothedMIndices x q) (hterm q hq)
  calc
    (∑ q ∈ pairs,
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l)) =
        ∑ q ∈ pairs,
          ∑ n ∈ smoothedMIndices x q,
            (1 / (2 * Real.pi) : ℝ) •
              ∫ ν : ℝ, lemma6FiniteMellinSummand x q n χ ν := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro n hn
      exact lemma6_smoothedMKernel_mul_char_eq_verticalIntegral
        hx hxlog (hpairs q hq).1 (hpairs q hq).2 χ
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∑ q ∈ pairs,
          ∑ n ∈ smoothedMIndices x q,
            ∫ ν : ℝ, lemma6FiniteMellinSummand x q n χ ν := by
      simp only [Finset.smul_sum]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          ∑ q ∈ pairs,
            ∑ n ∈ smoothedMIndices x q,
              lemma6FiniteMellinSummand x q n χ ν := by
      rw [hsumint]

/-- Exact contour formula for a finite prime-pair block after identifying
the full von Mangoldt series with `-L'/L`. -/
theorem lemma6_finiteMellin_sum_eq_logDeriv_verticalIntegral
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ q ∈ pairs, q.1.Prime ∧ q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    (∑ q ∈ pairs,
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l)) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          -(((x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)) *
            lemma6PairDirichletPolynomial x pairs
              (lemma6AlphaPoint x ν) χ *
            (deriv (DirichletCharacter.LFunction χ)
                (lemma6AlphaPoint x ν) /
              DirichletCharacter.LFunction χ
                (lemma6AlphaPoint x ν))) := by
  rw [lemma6_finiteMellin_sum_eq_verticalIntegral
    hx hxlog pairs hpairs χ]
  rw [integral_sum_finset_lemma6FiniteMellinSummand_eq_logDeriv
    hx hxlog pairs hpairs χ]

/-- The exact finite contour formula specialized to Chen's actual
`(k,m)` prime-pair block. -/
theorem lemma6_pairBlock_finiteMellin_sum_eq_verticalIntegral
    {x l : ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ)
    (χ : DirichletCharacter ℂ l) :
    (∑ q ∈ lemma6AdmissiblePairBlock x m k,
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l)) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          ∑ q ∈ lemma6AdmissiblePairBlock x m k,
            ∑ n ∈ smoothedMIndices x q,
              lemma6FiniteMellinSummand x q n χ ν := by
  exact lemma6_finiteMellin_sum_eq_verticalIntegral hx hxlog
    (lemma6AdmissiblePairBlock x m k)
    (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ

/-- Complete finite-level bridge from `lemma6PrimitivePairBlock` to its
exact `α`-line contour representation, before the infinite-series
identification with `L'/L`. -/
theorem lemma6PrimitivePairBlock_eq_finiteMellin_verticalIntegral
    {x l : ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ) :
    lemma6PrimitivePairBlock x m l k =
      primComplexSum l (fun χ =>
        starRingEnd ℂ (χ (x : ZMod l)) *
          ((1 / (2 * Real.pi) : ℝ) •
            ∫ ν : ℝ,
              ∑ q ∈ lemma6AdmissiblePairBlock x m k,
                ∑ n ∈ smoothedMIndices x q,
                  lemma6FiniteMellinSummand x q n χ ν)) := by
  unfold lemma6PrimitivePairBlock
  apply congrArg (primComplexSum l)
  funext χ
  rw [show
    (lemma6AdmissiblePairs x m).filter
        (fun q => q ∈ lemma6PairBlock x k) =
      lemma6AdmissiblePairBlock x m k by rfl]
  rw [lemma6_pairBlock_finiteMellin_sum_eq_verticalIntegral
    hx hxlog m k χ]

/-- Complete bridge from one primitive pair block to Chen's unsplit
logarithmic-derivative integral on the `α`-line. -/
theorem lemma6PrimitivePairBlock_eq_logDeriv_verticalIntegral
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ) :
    lemma6PrimitivePairBlock x m l k =
      primComplexSum l (fun χ =>
        starRingEnd ℂ (χ (x : ZMod l)) *
          ((1 / (2 * Real.pi) : ℝ) •
            ∫ ν : ℝ,
              -(((x : ℂ) ^ lemma6AlphaPoint x ν *
                  lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6AlphaPoint x ν)) *
                lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))))) := by
  unfold lemma6PrimitivePairBlock
  apply congrArg (primComplexSum l)
  funext χ
  rw [show
    (lemma6AdmissiblePairs x m).filter
        (fun q => q ∈ lemma6PairBlock x k) =
      lemma6AdmissiblePairBlock x m k by rfl]
  rw [lemma6_finiteMellin_sum_eq_logDeriv_verticalIntegral
    hx hxlog (lemma6AdmissiblePairBlock x m k)
      (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ]
  rfl

/-- The explicit pair-polynomial logarithmic-derivative integrand is
integrable on the `α`-line.  This is inherited from the absolutely
convergent von Mangoldt series, rather than asserted from a meromorphic
formula. -/
theorem integrable_lemma6PairLogDerivIntegrand
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ))
    (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ q ∈ pairs, q.1.Prime ∧ q.2.Prime)
    (χ : DirichletCharacter ℂ l) :
    Integrable (fun ν : ℝ =>
      -(((x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x ν)) *
        lemma6PairDirichletPolynomial x pairs
          (lemma6AlphaPoint x ν) χ *
        (deriv (DirichletCharacter.LFunction χ)
            (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ
            (lemma6AlphaPoint x ν)))) := by
  have hfull (q : ℕ × ℕ) (hq : q ∈ pairs) :
      Integrable (fun ν : ℝ =>
        ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν) :=
    integrable_tsum_of_summable_integral_norm_complex
      (fun n => integrable_lemma6FiniteMellinSummand hx hxlog
        (hpairs q hq).1 (hpairs q hq).2 χ)
      (summable_integral_norm_lemma6FiniteMellinSummand
        hx hxlog (hpairs q hq).1 (hpairs q hq).2 χ)
  have hsum : Integrable (fun ν : ℝ =>
      ∑ q ∈ pairs,
        ∑' n : ℕ, lemma6FiniteMellinSummand x q n χ ν) :=
    MeasureTheory.integrable_finsetSum pairs hfull
  exact hsum.congr (ae_of_all _ fun ν =>
    sum_tsum_lemma6FiniteMellinSummand_eq_pairPolynomial_logDeriv
      hx pairs χ ν)

/-- On `α`, integrability of the `B` summand and of the original Mellin
integrand implies integrability of the exact complex `A` summand. -/
theorem integrable_lemma6AContourIntegrand_alpha_of_B
    {x d : ℕ} [NeZero d] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (χ : DirichletCharacter ℂ d)
    (hB : Integrable (fun ν : ℝ =>
      lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν))) :
    Integrable (fun ν : ℝ =>
      lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) := by
  let U : ℝ → ℂ := fun ν =>
    lemma6LogDerivContourIntegrand x m k χ (lemma6AlphaPoint x ν)
  let A : ℝ → ℂ := fun ν =>
    lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
  let B : ℝ → ℂ := fun ν =>
    lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
  have hU : Integrable U := by
    simpa only [U, lemma6LogDerivContourIntegrand,
      lemma6PairBlockPolynomial] using
      integrable_lemma6PairLogDerivIntegrand hx hxlog
        (lemma6AdmissiblePairBlock x m k)
        (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ
  have hBe : Integrable B := by simpa only [B] using hB
  have hAeq : A = fun ν => U ν - B ν := by
    funext ν
    have hpoint := lemma6LogDerivContourIntegrand_alpha_eq_A_add_B
      hx m k H χ ν
    change U ν = A ν + B ν at hpoint
    rw [hpoint]
    abel
  change Integrable A
  rw [hAeq]
  exact hU.sub hBe

/-- The `B` integrand is automatically integrable on Chen's original
`alpha`-line.  This uses only absolute convergence in `Re s > 1`: the
pair polynomial and mollifier have height-independent finite bounds, while
`L'` is bounded by the differentiated untwisted Dirichlet series. -/
theorem integrable_lemma6BContourIntegrand_alpha
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (chi : DirichletCharacter ℂ d) (hchi : chi.IsPrimitive) :
    Integrable (fun nu : ℝ =>
      lemma6BContourIntegrand x m k H chi (lemma6AlphaPoint x nu)) := by
  let sigma : ℝ := 1 + 1 / Real.log (x : ℝ)
  let Cpair : ℝ :=
    ∑ q ∈ lemma6AdmissiblePairBlock x m k,
      ‖chi (q.1 * q.2 : ZMod d) /
        (((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x 0 *
          (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖
  let C : ℝ := Cpair * lemma6LDerivMajorant sigma * (harmonic H : ℝ)
  have hxreal : (1 : ℝ) < x := by
    exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    positivity
  have hsigmaOne : (1 : ℝ) < sigma := by
    dsimp only [sigma]
    have : 0 < (1 : ℝ) / Real.log (x : ℝ) := by positivity
    linarith
  have ha : 0 < lemma6SmoothingScale (x : ℝ) := by
    unfold lemma6SmoothingScale
    exact Real.rpow_pos_of_pos hlog _
  have horder : 1 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    rw [Nat.one_le_floor_iff]
    exact hxlog
  have hpoint (nu : ℝ) :
      lemma6AlphaPoint x nu =
        (sigma : ℂ) + (nu : ℂ) * Complex.I := by
    unfold lemma6AlphaPoint
    dsimp only [sigma]
  have hbase : Integrable (fun nu : ℝ =>
      (x : ℂ) ^ lemma6AlphaPoint x nu *
        lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x nu)) := by
    have h := integrable_cpow_mul_lemma6SmoothingMellinKernel
      (x := (x : ℝ)) (y := (x : ℝ))
      (by positivity) ha horder hsigma
    rw [show ((x : ℝ) : ℂ) = (x : ℂ) by norm_cast] at h
    simpa only [hpoint] using h
  have hpair (nu : ℝ) :
      ‖lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x nu) chi‖ ≤
        Cpair := by
    unfold lemma6PairBlockPolynomial lemma6PairDirichletPolynomial Cpair
    calc
      ‖∑ q ∈ lemma6AdmissiblePairBlock x m k,
          chi (q.1 * q.2 : ZMod d) /
            (((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x nu *
              (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ ≤
          ∑ q ∈ lemma6AdmissiblePairBlock x m k,
            ‖chi (q.1 * q.2 : ZMod d) /
              (((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x nu *
                (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ :=
        norm_sum_le _ _
      _ = ∑ q ∈ lemma6AdmissiblePairBlock x m k,
            ‖chi (q.1 * q.2 : ZMod d) /
              (((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x 0 *
                (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ := by
        apply Finset.sum_congr rfl
        intro q hq
        obtain ⟨hq1, hq2⟩ := primes_of_mem_lemma6AdmissiblePairBlock hq
        have hqpos : 0 < q.1 * q.2 := Nat.mul_pos hq1.pos hq2.pos
        simp only [norm_div, norm_mul]
        rw [Complex.norm_natCast_cpow_of_pos hqpos,
          Complex.norm_natCast_cpow_of_pos hqpos,
          lemma6AlphaPoint_re, lemma6AlphaPoint_re]
      _ ≤ ∑ q ∈ lemma6AdmissiblePairBlock x m k,
            ‖chi (q.1 * q.2 : ZMod d) /
              (((q.1 * q.2 : ℕ) : ℂ) ^ lemma6AlphaPoint x 0 *
                (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))‖ := le_rfl
  have hL (nu : ℝ) :
      ‖deriv (DirichletCharacter.LFunction chi) (lemma6AlphaPoint x nu)‖ ≤
        lemma6LDerivMajorant sigma := by
    have h := lemma6_norm_deriv_LFunction_le_majorant chi
      (one_lt_lemma6AlphaPoint_re hx nu)
    simpa only [lemma6AlphaPoint_re, sigma] using h
  have hM (nu : ℝ) :
      ‖lemma6MollifierAt H (lemma6AlphaPoint x nu) chi‖ ≤
        (harmonic H : ℝ) := by
    apply norm_lemma6MollifierAt_le_harmonic
    rw [lemma6AlphaPoint_re]
    linarith [hsigmaOne]
  have hCpair : 0 ≤ Cpair := by
    dsimp only [Cpair]
    positivity
  have hLnonneg : 0 ≤ lemma6LDerivMajorant sigma := by
    unfold lemma6LDerivMajorant
    exact tsum_nonneg fun _ => norm_nonneg _
  have hHnonneg : 0 ≤ (harmonic H : ℝ) := by
    rw [← lemma6_sum_Icc_inv_eq_harmonic]
    positivity
  have hmajor : Integrable (fun nu : ℝ =>
      C * ‖(x : ℂ) ^ lemma6AlphaPoint x nu *
        lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x nu)‖) := by
    exact hbase.norm.const_mul C
  have hmeas : AEStronglyMeasurable (fun nu : ℝ =>
      lemma6BContourIntegrand x m k H chi (lemma6AlphaPoint x nu)) := by
    have halpha : Continuous (lemma6AlphaPoint x) := by
      unfold lemma6AlphaPoint
      fun_prop
    have hrange : ∀ nu : ℝ, lemma6AlphaPoint x nu ∈
        {s : ℂ | 0 < s.re} := by
      intro nu
      exact one_lt_lemma6AlphaPoint_re hx nu |>.trans' zero_lt_one
    have hcontOn :=
      (differentiableOn_lemma6BContourIntegrand hd hx m k H hchi).continuousOn
    exact (hcontOn.comp_continuous halpha hrange).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with nu
  unfold lemma6BContourIntegrand
  simp only [norm_neg, norm_mul]
  dsimp only [C]
  have hp := hpair nu
  have hl := hL nu
  have hmoll := hM nu
  let B0 : ℝ := ‖(x : ℂ) ^ lemma6AlphaPoint x nu‖ *
    ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x nu)‖
  change B0 *
      ‖lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x nu) chi‖ *
      ‖deriv (DirichletCharacter.LFunction chi) (lemma6AlphaPoint x nu)‖ *
      ‖lemma6MollifierAt H (lemma6AlphaPoint x nu) chi‖ ≤
    Cpair * lemma6LDerivMajorant sigma * (harmonic H : ℝ) * B0
  calc
    B0 * ‖lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x nu) chi‖ *
        ‖deriv (DirichletCharacter.LFunction chi) (lemma6AlphaPoint x nu)‖ *
        ‖lemma6MollifierAt H (lemma6AlphaPoint x nu) chi‖ ≤
      B0 * Cpair * lemma6LDerivMajorant sigma * (harmonic H : ℝ) := by
        gcongr
    _ = Cpair * lemma6LDerivMajorant sigma * (harmonic H : ℝ) * B0 := by ring

/-- Exact equation-(17) contour decomposition for one primitive-conductor
pair block.  The original logarithmic-derivative integral is replaced by an
`A` integral on `α` plus a `B` integral on `β`, before taking norms or
summing moment majorants.  Absolute convergence supplies the original-line
integrability automatically; only horizontal decay and shifted-line
integrability remain as analytic limit hypotheses. -/
theorem lemma6PrimitivePairBlock_eq_A_alpha_add_B_beta
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (hhor : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Lemma6BHorizontalEdgesVanish x m k H χ)
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    lemma6PrimitivePairBlock x m d k =
      primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (x : ZMod d)) *
          ((1 / (2 * Real.pi) : ℝ) •
            ((∫ ν : ℝ,
                lemma6AContourIntegrand x m k H χ
                  (lemma6AlphaPoint x ν)) +
              ∫ ν : ℝ,
                lemma6BContourIntegrand x m k H χ
                  (lemma6BetaPoint x ν)))) := by
  have hrepr := lemma6PrimitivePairBlock_eq_logDeriv_verticalIntegral
    (x := x) (l := d) hx (by linarith) m k
  rw [hrepr]
  unfold primComplexSum
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    let U : ℝ → ℂ := fun ν =>
      lemma6LogDerivContourIntegrand x m k χ (lemma6AlphaPoint x ν)
    let A : ℝ → ℂ := fun ν =>
      lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
    let Ba : ℝ → ℂ := fun ν =>
      lemma6BContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
    let Bb : ℝ → ℂ := fun ν =>
      lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)
    have hU : Integrable U := by
      simpa only [U, lemma6LogDerivContourIntegrand,
        lemma6PairBlockPolynomial] using
        integrable_lemma6PairLogDerivIntegrand hx (by linarith)
          (lemma6AdmissiblePairBlock x m k)
          (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ
    have hBa : Integrable Ba := by
      simpa only [Ba] using
        integrable_lemma6BContourIntegrand_alpha
          hd hx (by linarith) m k H χ hp
    have hpoint : ∀ ν : ℝ, U ν = A ν + Ba ν := by
      intro ν
      exact lemma6LogDerivContourIntegrand_alpha_eq_A_add_B
        hx m k H χ ν
    have hAeq : A = fun ν => U ν - Ba ν := by
      funext ν
      rw [hpoint ν]
      abel
    have hA : Integrable A := by
      rw [hAeq]
      exact hU.sub hBa
    have hshift : (∫ ν : ℝ, Ba ν) = ∫ ν : ℝ, Bb ν := by
      simpa only [Ba, Bb] using
        lemma6BContour_verticalIntegral_eq hd hx hxlog m k H hp
          (hhor χ hp) hBa (hβ χ hp)
    have hint : (∫ ν : ℝ, U ν) =
        (∫ ν : ℝ, A ν) + ∫ ν : ℝ, Bb ν := by
      calc
        (∫ ν : ℝ, U ν) = ∫ ν : ℝ, A ν + Ba ν := by
          apply integral_congr_ae
          exact ae_of_all _ hpoint
        _ = (∫ ν : ℝ, A ν) + ∫ ν : ℝ, Ba ν :=
          MeasureTheory.integral_add hA hBa
        _ = (∫ ν : ℝ, A ν) + ∫ ν : ℝ, Bb ν := by rw [hshift]
    change starRingEnd ℂ (χ (x : ZMod d)) *
        ((1 / (2 * Real.pi) : ℝ) • ∫ ν : ℝ, U ν) =
      starRingEnd ℂ (χ (x : ZMod d)) *
        ((1 / (2 * Real.pi) : ℝ) •
          ((∫ ν : ℝ, A ν) + ∫ ν : ℝ, Bb ν))
    rw [hint]
  · simp [hp]

/-- The horizontal factor on Chen's `α`-line has constant modulus
`e x`, independently of the height. -/
theorem norm_nat_cpow_lemma6AlphaPoint
    {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    ‖(x : ℂ) ^ lemma6AlphaPoint x ν‖ =
      Real.exp 1 * (x : ℝ) := by
  have hxpos : (0 : ℝ) < x := by positivity
  have hxne : (x : ℝ) ≠ 1 := by
    exact_mod_cast (show x ≠ 1 by omega)
  change ‖((x : ℝ) : ℂ) ^ lemma6AlphaPoint x ν‖ =
    Real.exp 1 * (x : ℝ)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
    lemma6AlphaPoint_re, Real.rpow_add hxpos]
  rw [Real.rpow_one]
  have hinv : (1 : ℝ) / Real.log (x : ℝ) =
      (Real.log (x : ℝ))⁻¹ := one_div _
  rw [hinv, Real.rpow_inv_log hxpos hxne]
  ring

/-- The exact smoothing kernel on Chen's `α`-line has a quartic tail with
the natural smoothing scale as numerator. -/
theorem norm_lemma6SmoothingMellinKernel_alpha_le_scale_four
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x ν)‖ ≤
      lemma6SmoothingScale (x : ℝ) ^ 4 / (1 + ν ^ 4) := by
  let L : ℝ := Real.log (x : ℝ)
  let a : ℝ := lemma6SmoothingScale (x : ℝ)
  let σ : ℝ := 1 + 1 / L
  have hL : 0 < L := by dsimp only [L]; linarith
  have ha : 0 < a := by
    dsimp only [a, lemma6SmoothingScale]
    exact Real.rpow_pos_of_pos hL _
  have ha1 : 1 ≤ a := by
    dsimp only [a, lemma6SmoothingScale, L]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hn : 3 ≤ lemma6SmoothingOrder (x : ℝ) := by
    unfold lemma6SmoothingOrder
    exact Nat.le_floor hxlog
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hpoint : lemma6AlphaPoint x ν =
      (σ : ℂ) + (ν : ℂ) * Complex.I := by
    unfold lemma6AlphaPoint
    dsimp only [σ, L]
  have hk := norm_lemma6SmoothingMellinKernel_le_quartic
    ha hn hσ ν
  rw [← hpoint] at hk
  apply hk.trans
  have hσinv : σ⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    dsimp only [σ]
    have : 0 ≤ (1 : ℝ) / L := by positivity
    linarith
  have hdenpos : 0 < (1 + (ν / a) ^ 2) ^ 2 := by positivity
  have htargetpos : 0 < 1 + ν ^ 4 := by positivity
  have hscale :
      ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤
        a ^ 4 / (1 + ν ^ 4) := by
    rw [le_div_iff₀ htargetpos]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hdenpos).2
    field_simp [ha.ne']
    nlinarith [sq_nonneg ν, sq_nonneg (ν ^ 2),
      sq_nonneg (a ^ 2 - 1)]
  calc
    σ⁻¹ * ((1 + (ν / a) ^ 2) ^ 2)⁻¹ ≤
        1 * ((1 + (ν / a) ^ 2) ^ 2)⁻¹ := by gcongr
    _ ≤ a ^ 4 / (1 + ν ^ 4) := by simpa using hscale

/-- A convenient integer-log version of the rigorous equation-(17)
kernel majorant. -/
theorem norm_lemma6SmoothingMellinKernel_alpha_le_log_five
    {x : ℕ} (hxlog : 3 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x ν)‖ ≤
      Real.log (x : ℝ) ^ 5 / (1 + ν ^ 4) := by
  exact (norm_lemma6SmoothingMellinKernel_alpha_le_scale_four hxlog ν).trans
    (div_le_div_of_nonneg_right
      (lemma6SmoothingScale_four_le_log_five (by linarith)) (by positivity))

/-- After the complex `B` contour has been shifted, the norm of the finite
primitive-character sum is bounded by the exact `β`-line block integrand.
The triangle inequality is applied only after the contour move. -/
theorem norm_primComplexSum_lemma6BContour_beta_integral_le
    {d x : ℕ} [NeZero d] (m k H : ℕ)
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    ‖primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (x : ZMod d)) *
          ∫ ν : ℝ,
            lemma6BContourIntegrand x m k H χ
              (lemma6BetaPoint x ν))‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν) := by
  let G : DirichletCharacter ℂ d → ℝ → ℂ := fun χ ν =>
    lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)
  let R : DirichletCharacter ℂ d → ℝ → ℝ := fun χ ν =>
    if χ.IsPrimitive then ‖G χ ν‖ else 0
  have hint (χ : DirichletCharacter ℂ d) : Integrable (R χ) := by
    by_cases hp : χ.IsPrimitive
    · simp only [R, hp, if_true]
      exact (hβ χ hp).norm
    · simp [R, hp]
  unfold primComplexSum
  simp only [tsum_fintype]
  calc
    ‖∑ χ : DirichletCharacter ℂ d,
        if χ.IsPrimitive then
          starRingEnd ℂ (χ (x : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ ≤
      ∑ χ : DirichletCharacter ℂ d,
        ‖if χ.IsPrimitive then
          starRingEnd ℂ (χ (x : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ d, ∫ ν : ℝ, R χ ν := by
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_mul, RCLike.norm_conj]
        calc
          ‖χ (x : ZMod d)‖ * ‖∫ ν : ℝ, G χ ν‖ ≤
              1 * ∫ ν : ℝ, ‖G χ ν‖ := by
            gcongr
            · exact χ.norm_le_one x
            · exact norm_integral_le_integral_norm _
          _ = ∫ ν : ℝ, R χ ν := by simp [R, hp]
      · simp [R, hp]
    _ = ∫ ν : ℝ,
        ∑ χ : DirichletCharacter ℂ d, R χ ν := by
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun χ _ => hint χ)]
    _ = ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν) := by
      apply integral_congr_ae
      filter_upwards with ν
      unfold R G lemma6BContourIntegrand lemma6BModulusTotal
      simp only [dif_neg (NeZero.ne d), lemma6BModulus,
        lemma6PairBlockPolynomial, primSum, tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_neg, norm_mul]
        ring
      · simp [hp]

/-- Companion estimate for the complex `A` term which stays on `α`. -/
theorem norm_primComplexSum_lemma6AContour_alpha_integral_le
    {d x : ℕ} [NeZero d] (m k H : ℕ)
    (hA : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν))) :
    ‖primComplexSum d (fun χ =>
        starRingEnd ℂ (χ (x : ZMod d)) *
          ∫ ν : ℝ,
            lemma6AContourIntegrand x m k H χ
              (lemma6AlphaPoint x ν))‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
  let G : DirichletCharacter ℂ d → ℝ → ℂ := fun χ ν =>
    lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)
  let R : DirichletCharacter ℂ d → ℝ → ℝ := fun χ ν =>
    if χ.IsPrimitive then ‖G χ ν‖ else 0
  have hint (χ : DirichletCharacter ℂ d) : Integrable (R χ) := by
    by_cases hp : χ.IsPrimitive
    · simp only [R, hp, if_true]
      exact (hA χ hp).norm
    · simp [R, hp]
  unfold primComplexSum
  simp only [tsum_fintype]
  calc
    ‖∑ χ : DirichletCharacter ℂ d,
        if χ.IsPrimitive then
          starRingEnd ℂ (χ (x : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ ≤
      ∑ χ : DirichletCharacter ℂ d,
        ‖if χ.IsPrimitive then
          starRingEnd ℂ (χ (x : ZMod d)) * ∫ ν : ℝ, G χ ν
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ d, ∫ ν : ℝ, R χ ν := by
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_mul, RCLike.norm_conj]
        calc
          ‖χ (x : ZMod d)‖ * ‖∫ ν : ℝ, G χ ν‖ ≤
              1 * ∫ ν : ℝ, ‖G χ ν‖ := by
            gcongr
            · exact χ.norm_le_one x
            · exact norm_integral_le_integral_norm _
          _ = ∫ ν : ℝ, R χ ν := by simp [R, hp]
      · simp [R, hp]
    _ = ∫ ν : ℝ,
        ∑ χ : DirichletCharacter ℂ d, R χ ν := by
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun χ _ => hint χ)]
    _ = ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
      apply integral_congr_ae
      filter_upwards with ν
      unfold R G lemma6AContourIntegrand lemma6RawAModulus
      simp only [lemma6PairBlockPolynomial, primSum, tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχmem
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_neg, norm_mul]
        ring
      · simp [hp]

/-- Norm form of the rigorously shifted equation (17) for one conductor.
The right side is now exactly the raw `A` moment on `α` plus the `B` moment
on `β`; no norm of the `B` term is taken before shifting. -/
theorem norm_lemma6PrimitivePairBlock_le_A_alpha_add_B_beta
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ)
    (hhor : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Lemma6BHorizontalEdgesVanish x m k H χ)
    (hβ : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))) :
    ‖lemma6PrimitivePairBlock x m d k‖ ≤
      (1 / (2 * Real.pi) : ℝ) *
        ((∫ ν : ℝ,
            ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
                lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6AlphaPoint x ν)‖ *
              lemma6RawAModulus (d := d) x H
                (lemma6AdmissiblePairBlock x m k)
                (lemma6AlphaPoint x ν)) +
          ∫ ν : ℝ,
            ‖(x : ℂ) ^ lemma6BetaPoint x ν *
                lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6BetaPoint x ν)‖ *
              lemma6BModulusTotal d x m k H
                (lemma6BetaPoint x ν)) := by
  let c : ℝ := 1 / (2 * Real.pi)
  let PA : ℂ := primComplexSum d (fun χ =>
    starRingEnd ℂ (χ (x : ZMod d)) *
      ∫ ν : ℝ,
        lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν))
  let PB : ℂ := primComplexSum d (fun χ =>
    starRingEnd ℂ (χ (x : ZMod d)) *
      ∫ ν : ℝ,
        lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν))
  have hAint : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      Integrable (fun ν : ℝ =>
        lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)) := by
    intro χ hp
    exact integrable_lemma6AContourIntegrand_alpha_of_B
      hx (by linarith) m k H χ
        (integrable_lemma6BContourIntegrand_alpha
          hd hx (by linarith) m k H χ hp)
  have hPA : ‖PA‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
    exact norm_primComplexSum_lemma6AContour_alpha_integral_le
      m k H hAint
  have hPB : ‖PB‖ ≤
      ∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H
            (lemma6BetaPoint x ν) := by
    exact norm_primComplexSum_lemma6BContour_beta_integral_le m k H hβ
  have hdecomp := lemma6PrimitivePairBlock_eq_A_alpha_add_B_beta
    hd hx hxlog m k H hhor hβ
  have hlinear : lemma6PrimitivePairBlock x m d k =
      (c : ℂ) * (PA + PB) := by
    rw [hdecomp]
    unfold PA PB primComplexSum
    simp only [tsum_fintype]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro χ hχmem
    by_cases hp : χ.IsPrimitive
    · simp only [hp, if_true, RCLike.real_smul_eq_coe_mul]
      dsimp only [c]
      simp only [mul_add, add_mul, mul_assoc, mul_comm]
      rfl
    · simp [hp]
  rw [hlinear, norm_mul]
  have hc : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    dsimp only [c]
    positivity
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by dsimp only [c]; positivity)
  exact (norm_add_le PA PB).trans (add_le_add hPA hPB)

/-- The norm of one primitive prime-pair block is controlled by the
unsplit equation-(16) logarithmic-derivative integral.  The character sum
is kept inside the integral, in precisely the form consumed by
`lemma6LogDerivModulusAtAlpha`. -/
theorem norm_lemma6PrimitivePairBlock_le_logDeriv_integral
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ) :
    ‖lemma6PrimitivePairBlock x m l k‖ ≤
      (1 / (2 * Real.pi) : ℝ) *
        ∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)‖ *
            primSum l (fun χ =>
              ‖lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))‖) := by
  let c : ℝ := 1 / (2 * Real.pi)
  let G : DirichletCharacter ℂ l → ℝ → ℂ := fun χ ν =>
    -(((x : ℂ) ^ lemma6AlphaPoint x ν *
        lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x ν)) *
      lemma6PairBlockPolynomial x m k
        (lemma6AlphaPoint x ν) χ *
      (deriv (DirichletCharacter.LFunction χ)
          (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ
          (lemma6AlphaPoint x ν)))
  let R : DirichletCharacter ℂ l → ℝ → ℝ := fun χ ν =>
    if χ.IsPrimitive then ‖G χ ν‖ else 0
  have hrepr := lemma6PrimitivePairBlock_eq_logDeriv_verticalIntegral
    (x := x) (l := l) hx hxlog m k
  change lemma6PrimitivePairBlock x m l k =
    primComplexSum l (fun χ =>
      starRingEnd ℂ (χ (x : ZMod l)) *
        (c • ∫ ν : ℝ, G χ ν)) at hrepr
  rw [hrepr]
  unfold primComplexSum
  simp only [tsum_fintype]
  have hint (χ : DirichletCharacter ℂ l) : Integrable (R χ) := by
    by_cases hp : χ.IsPrimitive
    · simp only [R, hp, if_true]
      exact (integrable_lemma6PairLogDerivIntegrand hx hxlog
        (lemma6AdmissiblePairBlock x m k)
        (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ).norm
    · simp [R, hp]
  calc
    ‖∑ χ : DirichletCharacter ℂ l,
        if χ.IsPrimitive then
          starRingEnd ℂ (χ (x : ZMod l)) *
            (c • ∫ ν : ℝ, G χ ν)
        else 0‖ ≤
      ∑ χ : DirichletCharacter ℂ l,
        ‖if χ.IsPrimitive then
          starRingEnd ℂ (χ (x : ZMod l)) *
            (c • ∫ ν : ℝ, G χ ν)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ l,
        c * ∫ ν : ℝ, R χ ν := by
      apply Finset.sum_le_sum
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_mul, norm_smul]
        have hc : ‖c‖ = c := Real.norm_of_nonneg (by
          dsimp only [c]
          positivity)
        rw [RCLike.norm_conj, hc]
        calc
          ‖χ (x : ZMod l)‖ * (c * ‖∫ ν : ℝ, G χ ν‖) ≤
              1 * (c * ∫ ν : ℝ, ‖G χ ν‖) := by
            gcongr
            · exact χ.norm_le_one x
            · exact norm_integral_le_integral_norm _
          _ = c * ∫ ν : ℝ, R χ ν := by simp [R, hp]
      · simp [R, hp]
    _ = c * ∫ ν : ℝ,
        ∑ χ : DirichletCharacter ℂ l, R χ ν := by
      rw [← Finset.mul_sum]
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun χ _ => hint χ)]
    _ = (1 / (2 * Real.pi) : ℝ) *
        ∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)‖ *
            primSum l (fun χ =>
              ‖lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))‖) := by
      dsimp only [c]
      congr 1
      apply integral_congr_ae
      filter_upwards with ν
      unfold R G primSum
      simp only [tsum_fintype]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp only [hp, if_true, norm_neg, norm_mul]
        ring
      · simp [hp]

/-- The preceding contour bound with the height-independent factor
`‖x^α‖ = e x` pulled outside the integral. -/
theorem norm_lemma6PrimitivePairBlock_le_exp_mul_x_mul_logDeriv_integral
    {x l : ℕ} [NeZero l] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ) :
    ‖lemma6PrimitivePairBlock x m l k‖ ≤
      (Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
        ∫ ν : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
            primSum l (fun χ =>
              ‖lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))‖) := by
  apply (norm_lemma6PrimitivePairBlock_le_logDeriv_integral
    hx hxlog m k).trans_eq
  have hint :
      (∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)‖ *
            primSum l (fun χ =>
              ‖lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))‖)) =
        (Real.exp 1 * (x : ℝ)) *
          ∫ ν : ℝ,
            ‖lemma6SmoothingMellinKernel (x : ℝ)
                (lemma6AlphaPoint x ν)‖ *
              primSum l (fun χ =>
                ‖lemma6PairBlockPolynomial x m k
                    (lemma6AlphaPoint x ν) χ *
                  (deriv (DirichletCharacter.LFunction χ)
                      (lemma6AlphaPoint x ν) /
                    DirichletCharacter.LFunction χ
                      (lemma6AlphaPoint x ν))‖) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ν
    rw [norm_mul, norm_nat_cpow_lemma6AlphaPoint hx ν]
    ring
  rw [hint]
  ring

/-- The scalar kernel times one totalized logarithmic-derivative modulus
is integrable.  This permits the conductor sum to be moved through the
`ν`-integral without adding a new analytic assumption. -/
theorem integrable_lemma6KernelNorm_mul_logDerivModulusAtAlpha
    {x d : ℕ} [NeZero d] (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m k : ℕ) :
    Integrable (fun ν : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x ν)‖ *
        lemma6LogDerivModulusAtAlpha d x m k ν) := by
  let G : DirichletCharacter ℂ d → ℝ → ℂ := fun χ ν =>
    -(((x : ℂ) ^ lemma6AlphaPoint x ν *
        lemma6SmoothingMellinKernel (x : ℝ)
          (lemma6AlphaPoint x ν)) *
      lemma6PairBlockPolynomial x m k
        (lemma6AlphaPoint x ν) χ *
      (deriv (DirichletCharacter.LFunction χ)
          (lemma6AlphaPoint x ν) /
        DirichletCharacter.LFunction χ
          (lemma6AlphaPoint x ν)))
  let R : DirichletCharacter ℂ d → ℝ → ℝ := fun χ ν =>
    if χ.IsPrimitive then ‖G χ ν‖ else 0
  have hint (χ : DirichletCharacter ℂ d) : Integrable (R χ) := by
    by_cases hp : χ.IsPrimitive
    · simp only [R, hp, if_true]
      exact (integrable_lemma6PairLogDerivIntegrand hx hxlog
        (lemma6AdmissiblePairBlock x m k)
        (fun q hq => primes_of_mem_lemma6AdmissiblePairBlock hq) χ).norm
    · simp [R, hp]
  have hsum : Integrable (fun ν : ℝ =>
      ∑ χ : DirichletCharacter ℂ d, R χ ν) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun χ _ => hint χ)
  have hAKS : Integrable (fun ν : ℝ =>
      ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ)
            (lemma6AlphaPoint x ν)‖ *
        primSum d (fun χ =>
          ‖lemma6PairBlockPolynomial x m k
              (lemma6AlphaPoint x ν) χ *
            (deriv (DirichletCharacter.LFunction χ)
                (lemma6AlphaPoint x ν) /
              DirichletCharacter.LFunction χ
                (lemma6AlphaPoint x ν))‖)) := by
    apply hsum.congr
    filter_upwards with ν
    unfold R G primSum
    simp only [tsum_fintype]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    by_cases hp : χ.IsPrimitive
    · simp only [hp, if_true, norm_neg, norm_mul]
      ring
    · simp [hp]
  have hcpos : 0 < Real.exp 1 * (x : ℝ) := by positivity
  have hscaled := hAKS.const_mul (Real.exp 1 * (x : ℝ))⁻¹
  apply hscaled.congr
  filter_upwards with ν
  simp only [lemma6LogDerivModulusAtAlpha,
    dif_neg (NeZero.ne d)]
  rw [norm_mul, norm_nat_cpow_lemma6AlphaPoint hx ν]
  field_simp

/-- Summing the exact contour bound over a dyadic conductor block gives
the unsplit logarithmic-derivative block under one integral. -/
theorem sum_modulusBlock_norm_pairBlock_le_logDerivBlock_integral
    {x : ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (m l k : ℕ) :
    (∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d *
          ‖lemma6PrimitivePairBlock x m d k‖) ≤
      (Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
        ∫ ν : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
            lemma6LogDerivBlockAtAlpha x m l k ν := by
  let Cx : ℝ := (Real.exp 1 / (2 * Real.pi)) * (x : ℝ)
  let F : ℕ → ℝ → ℝ := fun d ν =>
    ‖lemma6SmoothingMellinKernel (x : ℝ)
        (lemma6AlphaPoint x ν)‖ *
      (lemma6LinearWeight d *
        lemma6LogDerivModulusAtAlpha d x m k ν)
  have hd2 (d : ℕ) (hd : d ∈ lemma6ModulusBlock x l) : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hint (d : ℕ) (hd : d ∈ lemma6ModulusBlock x l) :
      Integrable (F d) := by
    letI : NeZero d := ⟨(show d ≠ 0 by
      have := hd2 d hd
      omega)⟩
    have hbase := integrable_lemma6KernelNorm_mul_logDerivModulusAtAlpha
      (d := d) hx hxlog m k
    have hmul := hbase.const_mul (lemma6LinearWeight d)
    apply hmul.congr
    filter_upwards with ν
    dsimp only [F]
    ring
  have hterm (d : ℕ) (hd : d ∈ lemma6ModulusBlock x l) :
      lemma6LinearWeight d * ‖lemma6PrimitivePairBlock x m d k‖ ≤
        Cx * ∫ ν : ℝ, F d ν := by
    letI : NeZero d := ⟨(show d ≠ 0 by
      have := hd2 d hd
      omega)⟩
    have hnorm :=
      norm_lemma6PrimitivePairBlock_le_exp_mul_x_mul_logDeriv_integral
        (l := d) hx hxlog m k
    have hw0 := lemma6LinearWeight_nonneg d
    calc
      lemma6LinearWeight d * ‖lemma6PrimitivePairBlock x m d k‖ ≤
          lemma6LinearWeight d *
            ((Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
              ∫ ν : ℝ,
                ‖lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6AlphaPoint x ν)‖ *
                  primSum d (fun χ =>
                    ‖lemma6PairBlockPolynomial x m k
                        (lemma6AlphaPoint x ν) χ *
                      (deriv (DirichletCharacter.LFunction χ)
                          (lemma6AlphaPoint x ν) /
                        DirichletCharacter.LFunction χ
                          (lemma6AlphaPoint x ν))‖)) :=
        mul_le_mul_of_nonneg_left hnorm hw0
      _ = Cx * ∫ ν : ℝ, F d ν := by
        dsimp only [Cx, F]
        simp only [lemma6LogDerivModulusAtAlpha,
          dif_neg (NeZero.ne d)]
        let J : ℝ → ℝ := fun ν =>
          ‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
            primSum d (fun χ =>
              ‖lemma6PairBlockPolynomial x m k
                  (lemma6AlphaPoint x ν) χ *
                (deriv (DirichletCharacter.LFunction χ)
                    (lemma6AlphaPoint x ν) /
                  DirichletCharacter.LFunction χ
                    (lemma6AlphaPoint x ν))‖)
        have hwmove : lemma6LinearWeight d * (∫ ν : ℝ, J ν) =
            ∫ ν : ℝ, lemma6LinearWeight d * J ν :=
          (MeasureTheory.integral_const_mul
            (lemma6LinearWeight d) J).symm
        calc
          lemma6LinearWeight d *
              ((Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
                ∫ ν : ℝ, J ν) =
            (Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
              (lemma6LinearWeight d * ∫ ν : ℝ, J ν) := by ring
          _ = (Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
              ∫ ν : ℝ, lemma6LinearWeight d * J ν := by rw [hwmove]
          _ = (Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
              ∫ ν : ℝ,
                ‖lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6AlphaPoint x ν)‖ *
                  (lemma6LinearWeight d *
                    primSum d (fun χ =>
                      ‖lemma6PairBlockPolynomial x m k
                          (lemma6AlphaPoint x ν) χ *
                        (deriv (DirichletCharacter.LFunction χ)
                            (lemma6AlphaPoint x ν) /
                          DirichletCharacter.LFunction χ
                            (lemma6AlphaPoint x ν))‖)) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with ν
            dsimp only [J]
            ring
  calc
    (∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d *
          ‖lemma6PrimitivePairBlock x m d k‖) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        Cx * ∫ ν : ℝ, F d ν := by
      apply Finset.sum_le_sum
      intro d hd
      exact hterm d hd
    _ = Cx * ∑ d ∈ lemma6ModulusBlock x l,
        ∫ ν : ℝ, F d ν := by rw [Finset.mul_sum]
    _ = Cx * ∫ ν : ℝ,
        ∑ d ∈ lemma6ModulusBlock x l, F d ν := by
      rw [MeasureTheory.integral_finsetSum
        (lemma6ModulusBlock x l) hint]
    _ = Cx * ∫ ν : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
            lemma6LogDerivBlockAtAlpha x m l k ν := by
      congr 1
      apply integral_congr_ae
      filter_upwards with ν
      unfold lemma6LogDerivBlockAtAlpha
      dsimp only [F]
      rw [Finset.mul_sum]
    _ = (Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
        ∫ ν : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
            lemma6LogDerivBlockAtAlpha x m l k ν := by rfl

/-- Exact prime-pair half of equation (13). -/
theorem lemma6PrimitiveBlock_eq_sum_pairBlocks
    {x m l : ℕ} (hx : 1 ≤ x) :
    lemma6PrimitiveBlock x m l =
      ∑ k ∈ lemma6PairBlockIndices x m,
        lemma6PrimitivePairBlock x m l k := by
  let P := lemma6AdmissiblePairs x m
  let K := lemma6PairBlockIndices x m
  let G : (ℕ × ℕ) → DirichletCharacter ℂ l → ℂ := fun q χ =>
    ∑ n ∈ smoothedMIndices x q,
      (smoothedMKernel x q n : ℂ) *
        χ (q.1 * q.2 * n : ZMod l)
  have hpair (χ : DirichletCharacter ℂ l) :
      ∑ q ∈ P, G q χ =
        ∑ k ∈ K,
          ∑ q ∈ P.filter (fun q => lemma6PairBlockIndex x q = k),
            G q χ := by
    have hfiber := Finset.sum_fiberwise_eq_sum_filter P K
      (lemma6PairBlockIndex x) (fun q => G q χ)
    rw [Finset.filter_eq_self.mpr] at hfiber
    · exact hfiber.symm
    · intro q hq
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hfibereq (k : ℕ) :
      P.filter (fun q => lemma6PairBlockIndex x q = k) =
        P.filter (fun q => q ∈ lemma6PairBlock x k) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hqP, hindex⟩
      have hqchen : q ∈ chenPairs x :=
        (Finset.mem_filter.mp hqP).1
      obtain ⟨j, hj⟩ := exists_mem_lemma6PairBlock hx hqchen
      have hcanonical := lemma6PairBlockIndex_mem ⟨j, hj⟩
      rw [hindex] at hcanonical
      exact ⟨hqP, hcanonical⟩
    · rintro ⟨hqP, hqblock⟩
      exact ⟨hqP, lemma6PairBlockIndex_eq hqblock⟩
  unfold lemma6PrimitiveBlock lemma6PrimitivePairBlock
  change primComplexSum l (fun χ =>
      starRingEnd ℂ (χ (x : ZMod l)) * ∑ q ∈ P, G q χ) =
      ∑ k ∈ K, primComplexSum l (fun χ =>
        starRingEnd ℂ (χ (x : ZMod l)) *
          ∑ q ∈ P.filter (fun q => q ∈ lemma6PairBlock x k), G q χ)
  simp_rw [← hfibereq]
  have hdecomp (χ : DirichletCharacter ℂ l) :
      starRingEnd ℂ (χ (x : ZMod l)) * ∑ q ∈ P, G q χ =
        ∑ k ∈ K, starRingEnd ℂ (χ (x : ZMod l)) *
          ∑ q ∈ P.filter (fun q => lemma6PairBlockIndex x q = k),
            G q χ := by
    rw [hpair, Finset.mul_sum]
  rw [show (fun χ : DirichletCharacter ℂ l =>
      starRingEnd ℂ (χ (x : ZMod l)) * ∑ q ∈ P, G q χ) =
      (fun χ => ∑ k ∈ K, starRingEnd ℂ (χ (x : ZMod l)) *
        ∑ q ∈ P.filter (fun q => lemma6PairBlockIndex x q = k), G q χ) by
    funext χ
    exact hdecomp χ]
  unfold primComplexSum
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
  · simp only [hp, if_false, Finset.sum_const_zero]

/-- Removing the conductor `l` from the original modulus does not change its
primitive block.  The newly admitted pairs with `(p₁p₂,l) ≠ 1` contribute
zero because every character modulo `l` vanishes there.  This is the implicit
zero-extension step in the first display of the proof of Lemma 6. -/
theorem lemma6PrimitiveBlock_mul_left
    (x l m : ℕ) (_hl : 0 < l) :
    lemma6PrimitiveBlock x (l * m) l = lemma6PrimitiveBlock x m l := by
  letI : NeZero l := ⟨_hl.ne'⟩
  unfold lemma6PrimitiveBlock primComplexSum
  apply tsum_congr
  intro χ
  by_cases hχ : χ.IsPrimitive
  · rw [if_pos hχ, if_pos hχ]
    let S := (chenPairs x).filter
      (fun q => Nat.Coprime (q.1 * q.2) m)
    let P := fun q : ℕ × ℕ => Nat.Coprime (q.1 * q.2) l
    have hfilter :
        (chenPairs x).filter
            (fun q => Nat.Coprime (q.1 * q.2) (l * m)) =
          S.filter P := by
      ext q
      simp only [S, P, Finset.mem_filter]
      rw [Nat.coprime_mul_iff_right]
      tauto
    rw [hfilter]
    have hzero :
        ∑ q ∈ S.filter (fun q => ¬P q),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                χ (q.1 * q.2 * n : ZMod l) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqnot : ¬Nat.Coprime (q.1 * q.2) l :=
        (Finset.mem_filter.mp hq).2
      apply Finset.sum_eq_zero
      intro n hn
      have hprodnot : ¬Nat.Coprime (q.1 * q.2 * n) l := by
        intro hprod
        exact hqnot (Nat.Coprime.of_dvd_left
          (by exact dvd_mul_right (q.1 * q.2) n) hprod)
      have hnonunit :
          ¬IsUnit ((q.1 * q.2 * n : ℕ) : ZMod l) := by
        intro hu
        exact hprodnot ((ZMod.isUnit_iff_coprime
          (q.1 * q.2 * n) l).1 hu)
      have hnonunit' :
          ¬IsUnit ((q.1 : ZMod l) * q.2 * n) := by
        simpa only [Nat.cast_mul] using hnonunit
      have hχzero : χ (q.1 * q.2 * n : ZMod l) = 0 :=
        MulChar.apply_eq_zero_iff.mpr hnonunit'
      rw [hχzero, mul_zero]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := S) (p := P)
      (f := fun q =>
        ∑ n ∈ smoothedMIndices x q,
          (smoothedMKernel x q n : ℂ) *
            χ (q.1 * q.2 * n : ZMod l))
    rw [hzero, add_zero] at hsplit
    simpa only [S] using congrArg
      (fun z : ℂ => starRingEnd ℂ (χ (x : ZMod l)) * z) hsplit
  · rw [if_neg hχ, if_neg hχ]

/-- Once the prime-pair range is above `2`, the cofactor conditions `m = 1`
and `m = 2` coincide.  This justifies the paper's use of a maximum over
`1 < m` even though a conductor can have cofactor one. -/
theorem lemma6PrimitiveBlock_one_eq_two
    {x : ℕ} (hroot : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10))
    (l : ℕ) :
    lemma6PrimitiveBlock x 1 l = lemma6PrimitiveBlock x 2 l := by
  have hfilterOne :
      (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) 1) = chenPairs x := by
    simp
  have hfilterTwo :
      (chenPairs x).filter
          (fun q => Nat.Coprime (q.1 * q.2) 2) = chenPairs x := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    have hqdata := (Finset.mem_filter.mp hq).2
    have hq₁gt : 2 < q.1 := by
      exact_mod_cast hroot.trans_lt hqdata.2.2.1
    have hq₁odd : Odd q.1 := hqdata.1.odd_of_ne_two (by omega)
    have hq₂gtq₁ : q.1 < q.2 := by
      exact_mod_cast hqdata.2.2.2.1.trans_lt hqdata.2.2.2.2.1
    have hq₂odd : Odd q.2 := hqdata.2.1.odd_of_ne_two (by omega)
    exact (hq₁odd.mul hq₂odd).coprime_two_right
  unfold lemma6PrimitiveBlock
  rw [hfilterOne, hfilterTwo]

/-- Split a squarefree original modulus into a conductor and its coprime
cofactor, both in the sieve coefficient and in the primitive block. -/
theorem lemma6_divisor_cofactor_data
    {x d l : ℕ} (hd : Squarefree d) (hl : l ∈ d.divisors) :
    lemma6TotientWeight d =
        lemma6TotientWeight l * lemma6TotientWeight (d / l) ∧
      lemma6PrimitiveBlock x d l = lemma6PrimitiveBlock x (d / l) l := by
  have hld : l ∣ d := Nat.dvd_of_mem_divisors hl
  have hd0 : d ≠ 0 := (Nat.mem_divisors.mp hl).2
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hld (Nat.pos_of_ne_zero hd0)
  have hquotpos : 0 < d / l := Nat.div_pos (Nat.le_of_dvd
    (Nat.pos_of_ne_zero hd0) hld) hlpos
  have hprod : l * (d / l) = d := Nat.mul_div_cancel' hld
  have hcop : l.Coprime (d / l) :=
    Nat.coprime_of_squarefree_mul (hprod.symm ▸ hd)
  constructor
  · calc
      lemma6TotientWeight d =
          lemma6TotientWeight (l * (d / l)) := congrArg _ hprod.symm
      _ = lemma6TotientWeight l * lemma6TotientWeight (d / l) :=
        lemma6TotientWeight_mul hlpos.ne' hquotpos.ne' hcop
  · calc
      lemma6PrimitiveBlock x d l =
          lemma6PrimitiveBlock x (l * (d / l)) l :=
        congrArg (fun m => lemma6PrimitiveBlock x m l) hprod.symm
      _ = lemma6PrimitiveBlock x (d / l) l :=
        lemma6PrimitiveBlock_mul_left x l (d / l) hlpos

/-- Partition the primitive-associate contribution at an original modulus `d`
by the conductor of the character.  This is the exact finite character
reindexing used before equation (12); no estimate is involved. -/
theorem primitiveCharacterContribution_eq_sum_primitive
    {x d : ℕ} (hd : 0 < d) :
    primitiveCharacterContribution x d =
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0
        else lemma6PrimitiveBlock x d k.1 := by
  letI : NeZero d := ⟨hd.ne'⟩
  unfold primitiveCharacterContribution nontrivialCharSum
  rw [dif_neg hd.ne']
  rw [sum_characters_eq_sum_primitiveLifts]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  letI : NeZero k.1 := ⟨by
    exact (Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors k.2) hd).ne'⟩
  by_cases hkone : k.1 = 1
  · rw [if_pos hkone]
    apply Finset.sum_eq_zero
    intro ψ hψ
    rw [if_pos]
    change
      DirichletCharacter.changeLevel
          (Nat.dvd_of_mem_divisors k.2) ψ.1 = 1
    rw [DirichletCharacter.changeLevel_eq_one_iff]
    apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
    exact ψ.2.trans hkone
  · rw [if_neg hkone]
    unfold lemma6PrimitiveBlock primComplexSum
    rw [← sum_primitive_subtype_eq_tsum]
    apply Finset.sum_congr rfl
    intro ψ hψ
    have hliftne : primitiveLift d ⟨k, ψ⟩ ≠ 1 := by
      change
        DirichletCharacter.changeLevel
            (Nat.dvd_of_mem_divisors k.2) ψ.1 ≠ 1
      intro hliftone
      have hliftiff :
          DirichletCharacter.changeLevel
              (Nat.dvd_of_mem_divisors k.2) ψ.1 = 1 ↔ ψ.1 = 1 := by
        rw [DirichletCharacter.changeLevel_eq_one_iff]
      have hψone : ψ.1 = 1 := hliftiff.mp hliftone
      apply hkone
      have hcond : ψ.1.conductor = 1 :=
        DirichletCharacter.eq_one_iff_conductor_eq_one.mp hψone
      exact ψ.2.symm.trans hcond
    rw [if_neg hliftne]
    change
      starRingEnd ℂ ((primitiveLift d ⟨k, ψ⟩).primitiveCharacter x) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                (primitiveLift d ⟨k, ψ⟩).primitiveCharacter
                  (q.1 * q.2 * n) =
        starRingEnd ℂ (ψ.1 x) *
          ∑ q ∈ (chenPairs x).filter
              (fun q => Nat.Coprime (q.1 * q.2) d),
            ∑ n ∈ smoothedMIndices x q,
              (smoothedMKernel x q n : ℂ) *
                ψ.1 (q.1 * q.2 * n)
    rw [primitiveLift_primitiveCharacter_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro n hn
    have happ := primitiveLift_primitiveCharacter_apply
      d ⟨k, ψ⟩ (q.1 * q.2 * n)
    simpa only [Nat.cast_mul] using congrArg
      (fun z : ℂ => (smoothedMKernel x q n : ℂ) * z) happ

/-- Triangle-inequality form of the exact conductor partition. -/
theorem primitiveCharacterContribution_norm_le_sum_primitive
    {x d : ℕ} (hd : 0 < d) :
    ‖primitiveCharacterContribution x d‖ ≤
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0 else ‖lemma6PrimitiveBlock x d k.1‖ := by
  rw [primitiveCharacterContribution_eq_sum_primitive hd]
  calc
    ‖∑ k : ↥d.divisors,
        if k.1 = 1 then 0 else lemma6PrimitiveBlock x d k.1‖ ≤
        ∑ k : ↥d.divisors,
          ‖if k.1 = 1 then 0 else lemma6PrimitiveBlock x d k.1‖ :=
      norm_sum_le _ _
    _ = ∑ k : ↥d.divisors,
        if k.1 = 1 then 0 else ‖lemma6PrimitiveBlock x d k.1‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkone : k.1 = 1 <;> simp [hkone]

/-- The exact positive majorant obtained from `mTwo` after conductor
partitioning and the triangle inequality. -/
noncomputable def lemma6ConductorMajorant (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    lemma6TotientWeight d *
      ∑ k : ↥d.divisors,
        if k.1 = 1 then 0 else ‖lemma6PrimitiveBlock x d k.1‖

theorem mTwo_le_lemma6ConductorMajorant (x : ℕ) (ε : ℝ) :
    mTwo x ε ≤ lemma6ConductorMajorant x ε := by
  unfold mTwo lemma6ConductorMajorant
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := by
    have hddata := (Finset.mem_filter.mp hd).2
    omega
  apply mul_le_mul_of_nonneg_left
    (primitiveCharacterContribution_norm_le_sum_primitive hdpos)
  exact lemma6TotientWeight_nonneg d

/-- The sieve-modulus range is closed under taking positive divisors. -/
theorem divisor_mem_sieveModuli {x l d : ℕ} {ε : ℝ}
    (hd : d ∈ sieveModuli x ε) (hlpos : 0 < l) (hld : l ∣ d) :
    l ∈ sieveModuli x ε := by
  rw [sieveModuli, Finset.mem_filter] at hd ⊢
  have hldle : l ≤ d := Nat.le_of_dvd (by omega) hld
  refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hldle
      (Finset.mem_range.mp hd.1)), ?_⟩
  refine ⟨hlpos, Nat.Coprime.of_dvd_left hld hd.2.2.1, ?_⟩
  exact (by exact_mod_cast hldle : (l : ℝ) ≤ d).trans hd.2.2.2

/-- The same majorant after writing every squarefree original modulus as
`conductor × cofactor`.  This is still an exact finite sum; enlarging it to
two independent modulus ranges is the next arithmetic step in equation (12). -/
noncomputable def lemma6SplitConductorMajorant (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ sieveModuli x ε,
    if _hd : Squarefree d then
      ∑ k ∈ d.divisors,
        if k = 1 then 0
        else lemma6TotientWeight (d / k) * lemma6TotientWeight k *
          ‖lemma6PrimitiveBlock x (d / k) k‖
    else 0

/-- Cofactor--conductor pairs produced by squarefree moduli in the sieve
range.  The two coordinates multiply back to the original modulus. -/
noncomputable def lemma6SplitPairRange (x : ℕ) (ε : ℝ) :
    Finset (ℕ × ℕ) :=
  ((sieveModuli x ε).filter Squarefree).biUnion
    Nat.divisorsAntidiagonal

noncomputable def lemma6SplitPairTerm (x : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.2 = 1 then 0
  else lemma6TotientWeight p.1 * lemma6TotientWeight p.2 *
    ‖lemma6PrimitiveBlock x p.1 p.2‖

theorem lemma6SplitPairTerm_nonneg (x : ℕ) (p : ℕ × ℕ) :
    0 ≤ lemma6SplitPairTerm x p := by
  unfold lemma6SplitPairTerm
  split_ifs
  · positivity
  · exact mul_nonneg
      (mul_nonneg (lemma6TotientWeight_nonneg p.1)
        (lemma6TotientWeight_nonneg p.2)) (norm_nonneg _)

theorem lemma6ConductorMajorant_eq_split (x : ℕ) (ε : ℝ) :
    lemma6ConductorMajorant x ε = lemma6SplitConductorMajorant x ε := by
  unfold lemma6ConductorMajorant lemma6SplitConductorMajorant
  apply Finset.sum_congr rfl
  intro d hdmem
  by_cases hdsq : Squarefree d
  · rw [dif_pos hdsq, Finset.mul_sum]
    rw [← d.divisors.sum_attach]
    simp only [Finset.attach_eq_univ]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkone : k.1 = 1
    · simp [hkone]
    · rw [if_neg hkone, if_neg hkone]
      have hdata := lemma6_divisor_cofactor_data
        (x := x) hdsq k.2
      rw [hdata.1, hdata.2]
      ring
  · rw [dif_neg hdsq]
    have hweight : lemma6TotientWeight d = 0 := by
      unfold lemma6TotientWeight
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
      norm_num
    rw [hweight, zero_mul]

theorem lemma6SplitConductorMajorant_eq_pairSum (x : ℕ) (ε : ℝ) :
    lemma6SplitConductorMajorant x ε =
      ∑ p ∈ lemma6SplitPairRange x ε, lemma6SplitPairTerm x p := by
  have hdisj : Set.PairwiseDisjoint
      ((sieveModuli x ε).filter Squarefree)
      Nat.divisorsAntidiagonal := by
    intro d₁ hd₁ d₂ hd₂ hdne
    apply Finset.disjoint_left.mpr
    intro p hp₁ hp₂
    have hprod₁ := (Nat.mem_divisorsAntidiagonal.mp hp₁).1
    have hprod₂ := (Nat.mem_divisorsAntidiagonal.mp hp₂).1
    exact hdne (hprod₁.symm.trans hprod₂)
  calc
    lemma6SplitConductorMajorant x ε =
        ∑ d ∈ (sieveModuli x ε).filter Squarefree,
          ∑ p ∈ d.divisorsAntidiagonal,
            lemma6SplitPairTerm x p := by
      unfold lemma6SplitConductorMajorant
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdsq : Squarefree d
      · rw [dif_pos hdsq, if_pos hdsq]
        rw [← Nat.sum_divisorsAntidiagonal'
          (f := fun m k =>
            if k = 1 then 0
            else lemma6TotientWeight m * lemma6TotientWeight k *
              ‖lemma6PrimitiveBlock x m k‖)]
        unfold lemma6SplitPairTerm
        rfl
      · rw [dif_neg hdsq, if_neg hdsq]
    _ = ∑ p ∈ lemma6SplitPairRange x ε,
          lemma6SplitPairTerm x p := by
      unfold lemma6SplitPairRange
      exact (Finset.sum_biUnion hdisj).symm

/-- Every cofactor--conductor pair lies in the product of the two independent
sieve-modulus ranges used in the second inequality preceding equation (12). -/
theorem lemma6SplitPairRange_subset (x : ℕ) (ε : ℝ) :
    lemma6SplitPairRange x ε ⊆ sieveModuli x ε ×ˢ sieveModuli x ε := by
  intro p hp
  rw [lemma6SplitPairRange, Finset.mem_biUnion] at hp
  obtain ⟨d, hd, hp⟩ := hp
  have hdmem : d ∈ sieveModuli x ε := (Finset.mem_filter.mp hd).1
  have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
  have hp₁pos : 0 < p.1 := Nat.pos_of_ne_zero
    (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
  have hp₂pos : 0 < p.2 := Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
  rw [Finset.mem_product]
  exact ⟨divisor_mem_sieveModuli hdmem hp₁pos
      (Nat.dvd_of_mem_divisors
        (Nat.fst_mem_divisors_of_mem_antidiagonal hp)),
    divisor_mem_sieveModuli hdmem hp₂pos
      (Nat.dvd_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal hp))⟩

/-- The independent double sum appearing in Chen's second inequality before
equation (12). -/
noncomputable def lemma6IndependentMajorant (x : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ sieveModuli x ε ×ˢ sieveModuli x ε,
    lemma6SplitPairTerm x p

theorem lemma6IndependentMajorant_eq_bisum (x : ℕ) (ε : ℝ) :
    lemma6IndependentMajorant x ε =
      ∑ m ∈ sieveModuli x ε,
        lemma6TotientWeight m *
          ∑ l ∈ sieveModuli x ε,
            if l = 1 then 0
            else lemma6TotientWeight l * ‖lemma6PrimitiveBlock x m l‖ := by
  unfold lemma6IndependentMajorant
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  unfold lemma6SplitPairTerm
  by_cases hlone : l = 1
  · simp [hlone]
  · simp only [hlone, ↓reduceIte]
    ring

theorem mTwo_le_lemma6IndependentMajorant (x : ℕ) (ε : ℝ) :
    mTwo x ε ≤ lemma6IndependentMajorant x ε := by
  calc
    mTwo x ε ≤ lemma6ConductorMajorant x ε :=
      mTwo_le_lemma6ConductorMajorant x ε
    _ = lemma6SplitConductorMajorant x ε :=
      lemma6ConductorMajorant_eq_split x ε
    _ = ∑ p ∈ lemma6SplitPairRange x ε,
        lemma6SplitPairTerm x p :=
      lemma6SplitConductorMajorant_eq_pairSum x ε
    _ ≤ lemma6IndependentMajorant x ε := by
      unfold lemma6IndependentMajorant
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (lemma6SplitPairRange_subset x ε)
      intro p hp hnot
      exact lemma6SplitPairTerm_nonneg x p

/-- The `l`-th summand in the finite von-Mangoldt form of `N_m`. -/
noncomputable def lemma6NmTerm (x : ℕ) (m l : ℕ) : ℝ :=
  lemma6LinearWeight l * ‖lemma6PrimitiveBlock x m l‖

theorem lemma6NmTerm_nonneg (x m l : ℕ) :
    0 ≤ lemma6NmTerm x m l := by
  unfold lemma6NmTerm
  exact mul_nonneg (lemma6LinearWeight_nonneg l) (norm_nonneg _)

/-- Finite von-Mangoldt form of the quantity `N_m` in equation (12).

The contour kernel `Φ(x/(p₁p₂), χ)` in the scan becomes the inner finite
sum after Mellin inversion. The modulus is now the primitive conductor `l`,
and the pair restriction is `(p₁p₂,m)=1`, exactly as in the paper. -/
noncomputable def lemma6Nm (x : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ (sieveModuli x ε).erase 1,
    lemma6NmTerm x m l

theorem lemma6Nm_one_eq_two
    {x : ℕ} (hroot : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10))
    (ε : ℝ) :
    lemma6Nm x ε 1 = lemma6Nm x ε 2 := by
  unfold lemma6Nm lemma6NmTerm
  apply Finset.sum_congr rfl
  intro l hl
  rw [lemma6PrimitiveBlock_one_eq_two hroot l]

theorem eventually_lemma6Nm_one_eq_two (ε : ℝ) :
    ∀ᶠ x : ℕ in atTop, lemma6Nm x ε 1 = lemma6Nm x ε 2 := by
  have hrootReal :
      ∀ᶠ y : ℝ in atTop, (2 : ℝ) ≤ y ^ ((1 : ℝ) / 10) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop 2)
  have hrootNat :
      ∀ᶠ x : ℕ in atTop,
        (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) :=
    tendsto_natCast_atTop_atTop.eventually hrootReal
  filter_upwards [hrootNat] with x hx
  exact lemma6Nm_one_eq_two hx ε

theorem lemma6NmTerm_le_lemma6Nm {x l m : ℕ} {ε : ℝ}
    (hl : l ∈ (sieveModuli x ε).erase 1) :
    lemma6NmTerm x m l ≤ lemma6Nm x ε m := by
  unfold lemma6Nm
  exact Finset.single_le_sum
    (fun l hl => lemma6NmTerm_nonneg x m l) hl

/-- The small-conductor part `l ≤ (log x)^100`, estimated by the zero-free
region in equation (21). -/
noncomputable def lemma6NmSmall (x : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ ((sieveModuli x ε).erase 1).filter
      (fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100),
    lemma6NmTerm x m l

/-- The positive-dyadic-conductor part `l > (log x)^100`, estimated in
equations (19) and (20). -/
noncomputable def lemma6LargeConductors (x : ℕ) (ε : ℝ) : Finset ℕ :=
  ((sieveModuli x ε).erase 1).filter
    (fun l : ℕ => ¬(l : ℝ) ≤ (Real.log x) ^ 100)

noncomputable def lemma6NmLarge (x : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ lemma6LargeConductors x ε,
    lemma6NmTerm x m l

/-- Only squarefree conductors contribute to the large-conductor sum. -/
noncomputable def lemma6LargeSquarefreeConductors
    (x : ℕ) (ε : ℝ) : Finset ℕ :=
  (lemma6LargeConductors x ε).filter Squarefree

theorem lemma6NmLarge_eq_squarefree_sum
    (x : ℕ) (ε : ℝ) (m : ℕ) :
    lemma6NmLarge x ε m =
      ∑ d ∈ lemma6LargeSquarefreeConductors x ε,
        lemma6NmTerm x m d := by
  unfold lemma6NmLarge lemma6LargeSquarefreeConductors
  have hzero :
      ∑ d ∈ (lemma6LargeConductors x ε).filter
          (fun d => ¬Squarefree d), lemma6NmTerm x m d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hdnsq := (Finset.mem_filter.mp hd).2
    unfold lemma6NmTerm lemma6LinearWeight
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdnsq]
    norm_num
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := lemma6LargeConductors x ε) (p := Squarefree)
    (f := lemma6NmTerm x m)
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-- The finite set of positive dyadic indices actually occupied by large
conductors. -/
noncomputable def lemma6LargeBlockIndices
    (x : ℕ) (ε : ℝ) : Finset ℕ :=
  (lemma6LargeSquarefreeConductors x ε).image
    (lemma6ModulusBlockIndex x)

theorem lemma6LargeSquarefreeConductor_exists_block
    {x d : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hd : d ∈ lemma6LargeSquarefreeConductors x ε) :
    ∃ l : ℕ, 1 ≤ l ∧ d ∈ lemma6ModulusBlock x l := by
  have hddata := hd
  rw [lemma6LargeSquarefreeConductors, Finset.mem_filter] at hddata
  have hdlarge := hddata.1
  rw [lemma6LargeConductors, Finset.mem_filter] at hdlarge
  have hdsieve : d ∈ sieveModuli x ε :=
    Finset.mem_of_mem_erase hdlarge.1
  have hsievedata := hdsieve
  rw [sieveModuli, Finset.mem_filter] at hsievedata
  have hdx : d ≤ x := by
    have := Finset.mem_range.mp hsievedata.1
    omega
  exact exists_mem_lemma6ModulusBlock hxlog
    (lt_of_not_ge hdlarge.2) hddata.2 hdx

/-- In the large-conductor range, a fiber of the canonical block index is
exactly intersection with the corresponding paper block. -/
theorem lemma6LargeConductor_fiber_eq_block
    {x l : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    (lemma6LargeSquarefreeConductors x ε).filter
        (fun d => lemma6ModulusBlockIndex x d = l) =
      (lemma6LargeSquarefreeConductors x ε).filter
        (fun d => d ∈ lemma6ModulusBlock x l) := by
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, hindex⟩
    obtain ⟨k, hk1, hk⟩ :=
      lemma6LargeSquarefreeConductor_exists_block hxlog hd
    have hcanonical := lemma6ModulusBlockIndex_mem ⟨k, hk⟩
    rw [hindex] at hcanonical
    exact ⟨hd, hcanonical⟩
  · rintro ⟨hd, hdblock⟩
    exact ⟨hd, lemma6ModulusBlockIndex_eq hdblock⟩

/-- Exact conductor half of equation (13): the large part of `N_m` is the
sum over its occupied positive dyadic blocks. -/
theorem lemma6NmLarge_eq_sum_blocks
    {x m : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6NmLarge x ε m =
      ∑ l ∈ lemma6LargeBlockIndices x ε,
        ∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
            (fun d => d ∈ lemma6ModulusBlock x l),
          lemma6NmTerm x m d := by
  rw [lemma6NmLarge_eq_squarefree_sum]
  simp_rw [← lemma6LargeConductor_fiber_eq_block hxlog]
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (lemma6LargeSquarefreeConductors x ε)
    (lemma6LargeBlockIndices x ε)
    (lemma6ModulusBlockIndex x) (lemma6NmTerm x m)
  rw [Finset.filter_eq_self.mpr] at hfiber
  · exact hfiber.symm
  · intro d hd
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- One `(l,k)` summand after both dyadic decompositions in equation (13). -/
noncomputable def lemma6NmPairTerm
    (x m d k : ℕ) : ℝ :=
  lemma6LinearWeight d * ‖lemma6PrimitivePairBlock x m d k‖

theorem lemma6NmPairTerm_nonneg (x m d k : ℕ) :
    0 ≤ lemma6NmPairTerm x m d k := by
  unfold lemma6NmPairTerm
  exact mul_nonneg (lemma6LinearWeight_nonneg d) (norm_nonneg _)

/-- The conductors actually occupied in one large block form a subset of
the full paper dyadic modulus block. -/
theorem sum_largeConductor_pairTerm_le_modulusBlock_sum
    (x : ℕ) (ε : ℝ) (m l k : ℕ) :
    (∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
          (fun d => d ∈ lemma6ModulusBlock x l),
        lemma6NmPairTerm x m d k) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        lemma6NmPairTerm x m d k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact (Finset.mem_filter.mp hd).2
  · intro d hd hnot
    exact lemma6NmPairTerm_nonneg x m d k

/-- The exact Mellin bridge specialized to the occupied conductors in one
`(l,k)` block. -/
theorem sum_largeConductor_pairTerm_le_logDerivBlock_integral
    {x : ℕ} (hx : 2 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) (ε : ℝ) (m l k : ℕ) :
    (∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
          (fun d => d ∈ lemma6ModulusBlock x l),
        lemma6NmPairTerm x m d k) ≤
      (Real.exp 1 / (2 * Real.pi)) * (x : ℝ) *
        ∫ ν : ℝ,
          ‖lemma6SmoothingMellinKernel (x : ℝ)
              (lemma6AlphaPoint x ν)‖ *
            lemma6LogDerivBlockAtAlpha x m l k ν := by
  apply (sum_largeConductor_pairTerm_le_modulusBlock_sum
    x ε m l k).trans
  simpa only [lemma6NmPairTerm] using
    sum_modulusBlock_norm_pairBlock_le_logDerivBlock_integral
      hx hxlog m l k

/-- Equation (13) in the finite model: the large-conductor part is bounded
by the sum over the occupied conductor and prime-pair dyadic blocks. -/
theorem lemma6NmLarge_le_sum_pairBlocks
    {x m : ℕ} {ε : ℝ} (hx : 1 ≤ x)
    (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6NmLarge x ε m ≤
      ∑ l ∈ lemma6LargeBlockIndices x ε,
        ∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
            (fun d => d ∈ lemma6ModulusBlock x l),
          ∑ k ∈ lemma6PairBlockIndices x m,
            lemma6NmPairTerm x m d k := by
  rw [lemma6NmLarge_eq_sum_blocks hxlog]
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro d hd
  unfold lemma6NmTerm
  rw [lemma6PrimitiveBlock_eq_sum_pairBlocks hx]
  calc
    lemma6LinearWeight d *
        ‖∑ k ∈ lemma6PairBlockIndices x m,
          lemma6PrimitivePairBlock x m d k‖ ≤
      lemma6LinearWeight d *
        ∑ k ∈ lemma6PairBlockIndices x m,
          ‖lemma6PrimitivePairBlock x m d k‖ := by
      apply mul_le_mul_of_nonneg_left
      · exact norm_sum_le _ _
      · exact lemma6LinearWeight_nonneg d
    _ = ∑ k ∈ lemma6PairBlockIndices x m,
        lemma6NmPairTerm x m d k := by
      unfold lemma6NmPairTerm
      rw [Finset.mul_sum]

/-- The occupied conductor-block indices are logarithmically bounded. -/
theorem lemma6LargeBlockIndices_subset_range
    {x : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6LargeBlockIndices x ε ⊆ Finset.range (Nat.log 2 x + 2) := by
  intro l hl
  rw [lemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, rfl⟩ := hl
  obtain ⟨k, hk1, hk⟩ :=
    lemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hcanonical := lemma6ModulusBlockIndex_mem ⟨k, hk⟩
  have hkdata := hcanonical
  rw [lemma6ModulusBlock, Finset.mem_filter] at hkdata
  have hlogpow : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 :=
    one_le_pow₀ hxlog
  have hpowltR : ((2 : ℕ) ^ (lemma6ModulusBlockIndex x d - 1) : ℝ) < d := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : ℝ) ^ (lemma6ModulusBlockIndex x d - 1) ≤
          (2 : ℝ) ^ (lemma6ModulusBlockIndex x d - 1) *
            Real.log (x : ℝ) ^ 100 := by
        exact le_mul_of_one_le_right (by positivity) hlogpow
      _ < d := hkdata.2.2.1
  have hpowlt : (2 : ℕ) ^ (lemma6ModulusBlockIndex x d - 1) < d := by
    exact_mod_cast hpowltR
  have hddata := hd
  rw [lemma6LargeSquarefreeConductors, Finset.mem_filter] at hddata
  have hdlarge := hddata.1
  rw [lemma6LargeConductors, Finset.mem_filter] at hdlarge
  have hdsieve : d ∈ sieveModuli x ε :=
    Finset.mem_of_mem_erase hdlarge.1
  have hsievedata := hdsieve
  rw [sieveModuli, Finset.mem_filter] at hsievedata
  have hdx : d ≤ x := by
    have := Finset.mem_range.mp hsievedata.1
    omega
  have hlogbound : lemma6ModulusBlockIndex x d - 1 ≤ Nat.log 2 x :=
    Nat.le_log_of_pow_le (by norm_num) (hpowlt.le.trans hdx)
  rw [Finset.mem_range]
  omega

theorem card_lemma6LargeBlockIndices_le
    {x : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    (lemma6LargeBlockIndices x ε).card ≤ Nat.log 2 x + 2 := by
  calc
    (lemma6LargeBlockIndices x ε).card ≤
        (Finset.range (Nat.log 2 x + 2)).card :=
      Finset.card_le_card (lemma6LargeBlockIndices_subset_range hxlog)
    _ = Nat.log 2 x + 2 := Finset.card_range _

/-- The occupied prime-pair block indices are also logarithmically bounded. -/
theorem lemma6PairBlockIndices_subset_range
    {x m : ℕ} (hx : 1 ≤ x) :
    lemma6PairBlockIndices x m ⊆
      Finset.range (Nat.log 2 (x * x) + 1) := by
  intro k hk
  rw [lemma6PairBlockIndices, Finset.mem_image] at hk
  obtain ⟨q, hqP, rfl⟩ := hk
  have hqchen : q ∈ chenPairs x := (Finset.mem_filter.mp hqP).1
  obtain ⟨j, hj⟩ := exists_mem_lemma6PairBlock hx hqchen
  have hcanonical := lemma6PairBlockIndex_mem ⟨j, hj⟩
  have hkdata := hcanonical
  rw [lemma6PairBlock, Finset.mem_filter] at hkdata
  have hqdata := hqchen
  rw [chenPairs, Finset.mem_filter] at hqdata
  have hq1x : q.1 ≤ x := by
    have := Finset.mem_range.mp (Finset.mem_product.mp hqdata.1).1
    omega
  have hq2x : q.2 ≤ x := by
    have := Finset.mem_range.mp (Finset.mem_product.mp hqdata.1).2
    omega
  have hprodx : q.1 * q.2 ≤ x * x := Nat.mul_le_mul hq1x hq2x
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hscale : (1 : ℝ) ≤ (x : ℝ) ^ ((13 : ℝ) / 30) := by
    exact Real.one_le_rpow (by exact_mod_cast hx) (by norm_num)
  have hpowltR : ((2 : ℕ) ^ (lemma6PairBlockIndex x q) : ℝ) <
      (q.1 * q.2 : ℕ) := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : ℝ) ^ lemma6PairBlockIndex x q ≤
          (2 : ℝ) ^ lemma6PairBlockIndex x q *
            (x : ℝ) ^ ((13 : ℝ) / 30) := by
        exact le_mul_of_one_le_right (by positivity) hscale
      _ < (q.1 * q.2 : ℕ) := hkdata.2.1
  have hpowlt : (2 : ℕ) ^ lemma6PairBlockIndex x q < q.1 * q.2 := by
    exact_mod_cast hpowltR
  have hlogbound : lemma6PairBlockIndex x q ≤ Nat.log 2 (x * x) :=
    Nat.le_log_of_pow_le (by norm_num) (hpowlt.le.trans hprodx)
  rw [Finset.mem_range]
  omega

theorem card_lemma6PairBlockIndices_le
    {x m : ℕ} (hx : 1 ≤ x) :
    (lemma6PairBlockIndices x m).card ≤ Nat.log 2 (x * x) + 1 := by
  calc
    (lemma6PairBlockIndices x m).card ≤
        (Finset.range (Nat.log 2 (x * x) + 1)).card :=
      Finset.card_le_card (lemma6PairBlockIndices_subset_range hx)
    _ = Nat.log 2 (x * x) + 1 := Finset.card_range _

theorem card_lemma6LargeBlockIndices_cast_le_log
    {x : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    ((lemma6LargeBlockIndices x ε).card : ℝ) ≤
      (1 / Real.log 2 + 2) * Real.log x := by
  have hcardNat := card_lemma6LargeBlockIndices_le (x := x) (ε := ε) hxlog
  have hcardR : ((lemma6LargeBlockIndices x ε).card : ℝ) ≤
      (Nat.log 2 x : ℝ) + 2 := by exact_mod_cast hcardNat
  have hx1 : 1 ≤ x := by
    by_contra hx
    have : x = 0 := by omega
    subst x
    norm_num at hxlog
  have hnatlog := natLog_two_cast_le hx1
  calc
    ((lemma6LargeBlockIndices x ε).card : ℝ) ≤
        (Nat.log 2 x : ℝ) + 2 := hcardR
    _ ≤ Real.log x / Real.log 2 + 2 * Real.log x := by
      exact add_le_add hnatlog (by nlinarith)
    _ = (1 / Real.log 2 + 2) * Real.log x := by ring

theorem card_lemma6PairBlockIndices_cast_le_log
    {x m : ℕ} (hx : 1 ≤ x) (hxlog : 1 ≤ Real.log (x : ℝ)) :
    ((lemma6PairBlockIndices x m).card : ℝ) ≤
      (2 / Real.log 2 + 1) * Real.log x := by
  have hcardNat := card_lemma6PairBlockIndices_le (x := x) (m := m) hx
  have hcardR : ((lemma6PairBlockIndices x m).card : ℝ) ≤
      (Nat.log 2 (x * x) : ℝ) + 1 := by exact_mod_cast hcardNat
  have hxx : 1 ≤ x * x := by
    simpa only [one_mul] using Nat.mul_le_mul hx hx
  have hnatlog := natLog_two_cast_le hxx
  have hx0 : x ≠ 0 := by omega
  have hlogxx : Real.log (x * x : ℕ) = 2 * Real.log x := by
    norm_num only [Nat.cast_mul]
    rw [Real.log_mul (by exact_mod_cast hx0) (by exact_mod_cast hx0)]
    ring
  rw [hlogxx] at hnatlog
  calc
    ((lemma6PairBlockIndices x m).card : ℝ) ≤
        (Nat.log 2 (x * x) : ℝ) + 1 := hcardR
    _ ≤ (2 * Real.log x) / Real.log 2 + Real.log x := by
      gcongr
    _ = (2 / Real.log 2 + 1) * Real.log x := by ring

theorem lemma6Nm_eq_small_add_large (x : ℕ) (ε : ℝ) (m : ℕ) :
    lemma6Nm x ε m = lemma6NmSmall x ε m + lemma6NmLarge x ε m := by
  unfold lemma6Nm lemma6NmSmall lemma6NmLarge lemma6LargeConductors
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := (sieveModuli x ε).erase 1)
      (p := fun l : ℕ => (l : ℝ) ≤ (Real.log x) ^ 100)
      (f := lemma6NmTerm x m)).symm

theorem lemma6Nm_nonneg (x : ℕ) (ε : ℝ) (m : ℕ) :
    0 ≤ lemma6Nm x ε m := by
  unfold lemma6Nm
  apply Finset.sum_nonneg
  intro l hl
  exact lemma6NmTerm_nonneg x m l

/-- Removing the zero conductor-one summand is exactly `Finset.erase 1`. -/
private theorem sum_ite_one_eq_sum_erase
    (S : Finset ℕ) (f : ℕ → ℝ) :
    ∑ l ∈ S, (if l = 1 then 0 else f l) =
      ∑ l ∈ S.erase 1, f l := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      by_cases ha1 : a = 1
      · subst a
        simp [ha, ih]
      · rw [Finset.erase_insert_of_ne ha1]
        simp [ha, ha1, ih]

/-- The inner conductor sum in the independent majorant is at most one
logarithm times `N_m`. -/
theorem lemma6_inner_sum_le_nm
    {x m : ℕ} {ε : ℝ} :
    (∑ l ∈ sieveModuli x ε,
        if l = 1 then 0
        else lemma6TotientWeight l * ‖lemma6PrimitiveBlock x m l‖) ≤
      (2 / Real.log 2) * Real.log x * lemma6Nm x ε m := by
  rw [sum_ite_one_eq_sum_erase]
  unfold lemma6Nm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hlmem : l ∈ sieveModuli x ε := Finset.mem_of_mem_erase hl
  have hl2 : 2 ≤ l := by
    have hlne : l ≠ 1 := Finset.ne_of_mem_erase hl
    have hlpos := (Finset.mem_filter.mp hlmem).2.1
    omega
  unfold lemma6NmTerm
  calc
    lemma6TotientWeight l * ‖lemma6PrimitiveBlock x m l‖ ≤
        ((2 / Real.log 2) * Real.log x * lemma6LinearWeight l) *
          ‖lemma6PrimitiveBlock x m l‖ := by
      exact mul_le_mul_of_nonneg_right
        (lemma6TotientWeight_le_log_mul_linearWeight hlmem hl2)
        (norm_nonneg _)
    _ = (2 / Real.log 2) * Real.log x *
        (lemma6LinearWeight l * ‖lemma6PrimitiveBlock x m l‖) := by ring

/-- The finite range `1 < m ≤ x^(1/2)` over which equation (12) takes its
maximum. -/
noncomputable def lemma6MRange (x : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter fun m =>
    (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2)

theorem mem_lemma6MRange {x m : ℕ} :
    m ∈ lemma6MRange x ↔
      1 < m ∧ m ≤ x ∧
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
  simp [lemma6MRange, Nat.lt_iff_add_one_le, and_assoc]

/-- Every nontrivial sieve modulus lies in the larger range used for the
maximum in equation (12). -/
theorem sieveModuli_mem_lemma6MRange
    {x m : ℕ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 ≤ ε)
    (hm : m ∈ sieveModuli x ε) (hm1 : m ≠ 1) :
    m ∈ lemma6MRange x := by
  rw [mem_lemma6MRange]
  have hmdata := (Finset.mem_filter.mp hm)
  have hmpos : 1 ≤ m := hmdata.2.1
  have hmx : m ≤ x := by
    have := Finset.mem_range.mp hmdata.1
    omega
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  refine ⟨by omega, hmx, ?_⟩
  calc
    (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hmdata.2.2.2
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hxR (by linarith)

theorem lemma6MRange_nonempty {x : ℕ} (hx : 4 ≤ x) :
    (lemma6MRange x).Nonempty := by
  refine ⟨2, ?_⟩
  rw [mem_lemma6MRange]
  refine ⟨by norm_num, by omega, ?_⟩
  have hxR : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  calc
    (2 : ℝ) = Real.sqrt 4 := by
      symm
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt hxR
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _

theorem two_mem_lemma6MRange {x : ℕ} (hx : 4 ≤ x) :
    2 ∈ lemma6MRange x := by
  rw [mem_lemma6MRange]
  refine ⟨by norm_num, by omega, ?_⟩
  have hxR : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  calc
    (2 : ℝ) = Real.sqrt 4 := by
      symm
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt hxR
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _

/-- On the nonempty range of equation (12), one of the finitely many `N_m`
attains the maximum. -/
theorem exists_lemma6Nm_max {x : ℕ} (hx : 4 ≤ x) (ε : ℝ) :
    ∃ m ∈ lemma6MRange x, ∀ m' ∈ lemma6MRange x,
      lemma6Nm x ε m' ≤ lemma6Nm x ε m :=
  Finset.exists_max_image (lemma6MRange x) (lemma6Nm x ε)
    (lemma6MRange_nonempty hx)

/-- Assembly of the independent double sum before the elementary logarithmic
bounds are applied. -/
theorem lemma6IndependentMajorant_le_nm_bound
    {x : ℕ} {ε M : ℝ} (hx4 : 4 ≤ x) (hε : 0 ≤ ε)
    (hone : lemma6Nm x ε 1 = lemma6Nm x ε 2)
    (hM : ∀ m ∈ lemma6MRange x, lemma6Nm x ε m ≤ M) :
    lemma6IndependentMajorant x ε ≤
      (∑ m ∈ sieveModuli x ε, lemma6TotientWeight m) *
        ((2 / Real.log 2) * Real.log x * M) := by
  have hx1 : 1 ≤ x := by omega
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx1)
  have hc0 : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
  have hfactor0 : 0 ≤ (2 / Real.log 2) * Real.log x :=
    mul_nonneg hc0 hlog0
  have hNmAll : ∀ m ∈ sieveModuli x ε, lemma6Nm x ε m ≤ M := by
    intro m hm
    by_cases hm1 : m = 1
    · subst m
      rw [hone]
      exact hM 2 (two_mem_lemma6MRange hx4)
    · exact hM m (sieveModuli_mem_lemma6MRange hx1 hε hm hm1)
  rw [lemma6IndependentMajorant_eq_bisum]
  calc
    ∑ m ∈ sieveModuli x ε,
        lemma6TotientWeight m *
          (∑ l ∈ sieveModuli x ε,
            if l = 1 then 0
            else lemma6TotientWeight l * ‖lemma6PrimitiveBlock x m l‖) ≤
        ∑ m ∈ sieveModuli x ε,
          lemma6TotientWeight m *
            ((2 / Real.log 2) * Real.log x * lemma6Nm x ε m) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left lemma6_inner_sum_le_nm
        (lemma6TotientWeight_nonneg m)
    _ ≤ ∑ m ∈ sieveModuli x ε,
          lemma6TotientWeight m *
            ((2 / Real.log 2) * Real.log x * M) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left (hNmAll m hm) hfactor0
      · exact lemma6TotientWeight_nonneg m
    _ = (∑ m ∈ sieveModuli x ε, lemma6TotientWeight m) *
          ((2 / Real.log 2) * Real.log x * M) := by
      rw [Finset.sum_mul]

/-- The remaining arithmetic core of equation (12), stated against an
arbitrary common upper bound `M` for the finitely many `N_m`.

The exact character/conductor reindexing, zero extension, cofactor split,
coefficient estimates, and enlargement to `lemma6IndependentMajorant` are
assembled above.  The harmless cofactor `m = 1` is replaced by `m = 2`, and
the common upper bound is later chosen to be a finite maximum. -/
theorem mTwo_le_log6_mul_nm_uniform
    (ε : ℝ) (hε : 0 < ε) (_hε' : ε < 1 / 100) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop, Even x →
      ∀ M : ℝ,
        (∀ m ∈ lemma6MRange x, lemma6Nm x ε m ≤ M) →
          mTwo x ε ≤ A * (Real.log x) ^ 6 * M := by
  let c : ℝ := 2 / Real.log 2
  let A : ℝ := c * (1 + 8 * c)
  refine ⟨A, ?_, ?_⟩
  · dsimp only [A, c]
    positivity
  · have hlogOneReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
    have hlogOne : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually hlogOneReal
    filter_upwards [hlogOne, eventually_lemma6Nm_one_eq_two ε,
      eventually_ge_atTop 4] with x hxlog hone hx4
    intro _hxEven M hM
    let L : ℝ := Real.log x
    let H : ℝ := harmonic x
    have hc0 : 0 ≤ c := by
      dsimp only [c]
      positivity
    have hcpos : 0 < c := by
      dsimp only [c]
      positivity
    have hL0 : 0 ≤ L := zero_le_one.trans hxlog
    have hM0 : 0 ≤ M :=
      (lemma6Nm_nonneg x ε 2).trans
        (hM 2 (two_mem_lemma6MRange hx4))
    have hH0 : 0 ≤ H := by
      dsimp only [H]
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
      positivity
    have hHle : H ≤ 2 * L := by
      dsimp only [H, L]
      have hH := harmonic_le_one_add_log x
      linarith
    have hL4 : (1 : ℝ) ≤ L ^ 4 := by
      have : (1 : ℝ) ^ 4 ≤ L ^ 4 := by gcongr
      simpa using this
    have houter := sum_sieveModuli_lemma6TotientWeight_le
      (x := x) (by omega : 2 ≤ x) ε
    have houter' :
        ∑ d ∈ sieveModuli x ε, lemma6TotientWeight d ≤
          (1 + 8 * c) * L ^ 4 := by
      calc
        ∑ d ∈ sieveModuli x ε, lemma6TotientWeight d ≤
            1 + c * L * H ^ 3 := by
          simpa only [c, L, H] using houter
        _ ≤ 1 + c * L * (2 * L) ^ 3 := by gcongr
        _ = 1 + 8 * c * L ^ 4 := by ring
        _ ≤ L ^ 4 + 8 * c * L ^ 4 := add_le_add_left hL4 _
        _ = (1 + 8 * c) * L ^ 4 := by ring
    have hind := lemma6IndependentMajorant_le_nm_bound
      hx4 hε.le hone hM
    have hfactorM0 : 0 ≤ c * L * M := by positivity
    have hL5le6 : L ^ 5 ≤ L ^ 6 := by
      calc
        L ^ 5 ≤ L ^ 5 * L :=
          le_mul_of_one_le_right (pow_nonneg hL0 5) hxlog
        _ = L ^ 6 := by ring
    calc
      mTwo x ε ≤ lemma6IndependentMajorant x ε :=
        mTwo_le_lemma6IndependentMajorant x ε
      _ ≤ (∑ d ∈ sieveModuli x ε, lemma6TotientWeight d) *
          (c * L * M) := by
        simpa only [c, L] using hind
      _ ≤ ((1 + 8 * c) * L ^ 4) * (c * L * M) :=
        mul_le_mul_of_nonneg_right houter' hfactorM0
      _ = A * L ^ 5 * M := by
        dsimp only [A]
        ring
      _ ≤ A * L ^ 6 * M := by
        gcongr
      _ = A * (Real.log x) ^ 6 * M := by rfl

/-- Equation (12), with the finite maximum made explicit. -/
theorem mTwo_le_log6_mul_nm
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop, Even x →
      ∃ m : ℕ, 1 < m ∧
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) ∧
        mTwo x ε ≤
          A * (Real.log x) ^ 6 * lemma6Nm x ε m := by
  obtain ⟨A, hA, huniform⟩ :=
    mTwo_le_log6_mul_nm_uniform ε hε hε'
  refine ⟨A, hA, ?_⟩
  filter_upwards [huniform, eventually_ge_atTop 4] with x hxuniform hx4
  intro hxEven
  obtain ⟨m, hmRange, hmmax⟩ := exists_lemma6Nm_max hx4 ε
  have hm := (mem_lemma6MRange.mp hmRange)
  refine ⟨m, hm.1, hm.2.2, ?_⟩
  exact hxuniform hxEven (lemma6Nm x ε m) hmmax

/-- For every occupied positive conductor block, its real upper endpoint is
strictly below the `2x^(1/2-ε)` ceiling used in equation (20). -/
theorem lemma6_occupied_modulusScale_lt_two_threshold
    {x l : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hl : l ∈ lemma6LargeBlockIndices x ε) :
    lemma6DyadicModulusScale x l <
      2 * (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
  rw [lemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, rfl⟩ := hl
  obtain ⟨j, hj1, hj⟩ :=
    lemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hindex : lemma6ModulusBlockIndex x d = j :=
    lemma6ModulusBlockIndex_eq hj
  have hjdata := hj
  rw [lemma6ModulusBlock, Finset.mem_filter] at hjdata
  have hdlarge := (Finset.mem_filter.mp hd).1
  have hderase := (Finset.mem_filter.mp hdlarge).1
  have hdsieve : d ∈ sieveModuli x ε := Finset.mem_of_mem_erase hderase
  have hdthreshold : (d : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
    (Finset.mem_filter.mp hdsieve).2.2.2
  rw [hindex]
  unfold lemma6DyadicModulusScale
  have hpow : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    calc
      (2 : ℝ) ^ j = 2 ^ ((j - 1) + 1) := by congr 1; omega
      _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (j - 1) := by ring
  rw [hpow]
  nlinarith [hjdata.2.2.1]

/-- The three parameter regions on pages 11--12 are exhaustive for every
occupied `(l,k)` block: the first two disjuncts are the two cases combined
in equation (19), and the last disjunct is equation (20). -/
theorem lemma6_occupied_pair_modulus_regime_split
    {x l k : ℕ} {ε : ℝ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hl : l ∈ lemma6LargeBlockIndices x ε) :
    lemma6PairDyadicScale x k > (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ∨
      ((x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≥ lemma6PairDyadicScale x k ∧
        lemma6PairDyadicScale x k > lemma6DyadicModulusScale x l) ∨
      (lemma6PairDyadicScale x k ≤ lemma6DyadicModulusScale x l ∧
        lemma6DyadicModulusScale x l <
          2 * (x : ℝ) ^ ((1 : ℝ) / 2 - ε)) := by
  have hmod := lemma6_occupied_modulusScale_lt_two_threshold hxlog hl
  by_cases hhigh : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) <
      lemma6PairDyadicScale x k
  · exact Or.inl hhigh
  · right
    have hthreshold : lemma6PairDyadicScale x k ≤
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := le_of_not_gt hhigh
    by_cases hpair : lemma6DyadicModulusScale x l <
        lemma6PairDyadicScale x k
    · exact Or.inl ⟨hthreshold, hpair⟩
    · exact Or.inr ⟨le_of_not_gt hpair, hmod⟩

/-! ### Equations (14)--(20): the occupied `(l,k)` block estimate -/

/-- Integrability of the per-conductor `A` integrand on the `α`-line,
obtained from the complex `A = U - B` decomposition. -/
theorem integrable_kernelNorm_mul_rawAModulus_alpha
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ) :
    Integrable (fun ν : ℝ =>
      ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
        lemma6RawAModulus (d := d) x H (lemma6AdmissiblePairBlock x m k)
          (lemma6AlphaPoint x ν)) := by
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hA (χ : DirichletCharacter ℂ d) :
      Integrable (fun ν : ℝ =>
        (if χ.IsPrimitive then
          ‖lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)‖
        else 0 : ℝ)) := by
    by_cases hp : χ.IsPrimitive
    · simp only [hp, if_true]
      exact (integrable_lemma6AContourIntegrand_alpha_of_B hx hlog1 m k H χ
        (integrable_lemma6BContourIntegrand_alpha hd hx hlog1 m k H χ hp)).norm
    · simp only [hp, if_false]
      exact integrable_zero _ _ _
  have hsum : Integrable (fun ν : ℝ =>
      ∑ χ : DirichletCharacter ℂ d,
        if χ.IsPrimitive then
          ‖lemma6AContourIntegrand x m k H χ (lemma6AlphaPoint x ν)‖
        else 0) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun χ _ => hA χ)
  apply hsum.congr
  filter_upwards with ν
  simp only [lemma6RawAModulus, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true, lemma6AContourIntegrand, lemma6PairBlockPolynomial,
      norm_neg, norm_mul]
    ring
  · simp [hp]

/-- Integrability of the per-conductor `B` integrand on the shifted
`β`-line, directly from the characterwise contour integrability. -/
theorem integrable_kernelNorm_mul_BModulusTotal_beta
    {x d : ℕ} [NeZero d] (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ) :
    Integrable (fun ν : ℝ =>
      ‖(x : ℂ) ^ lemma6BetaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
        lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν)) := by
  have hB (χ : DirichletCharacter ℂ d) :
      Integrable (fun ν : ℝ =>
        (if χ.IsPrimitive then
          ‖lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)‖
        else 0 : ℝ)) := by
    by_cases hp : χ.IsPrimitive
    · simp only [hp, if_true]
      exact (integrable_lemma6BContourIntegrand_beta
        hd hx hxlog m k H hp).norm
    · simp only [hp, if_false]
      exact integrable_zero _ _ _
  have hsum : Integrable (fun ν : ℝ =>
      ∑ χ : DirichletCharacter ℂ d,
        if χ.IsPrimitive then
          ‖lemma6BContourIntegrand x m k H χ (lemma6BetaPoint x ν)‖
        else 0) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun χ _ => hB χ)
  apply hsum.congr
  filter_upwards with ν
  unfold lemma6BModulusTotal
  simp only [dif_neg (NeZero.ne d), lemma6BModulus,
    primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true, lemma6BContourIntegrand, lemma6PairBlockPolynomial,
      norm_neg, norm_mul]
    ring
  · simp [hp]

/-- The raw `A` summand, totalized at modulus zero so that conductor sums
can range over an unrestricted finite set of moduli. -/
noncomputable def lemma6RawAModulusTotal
    (d x m k H : ℕ) (s : ℂ) : ℝ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    lemma6RawAModulus (d := d) x H (lemma6AdmissiblePairBlock x m k) s

theorem lemma6RawAModulusTotal_eq
    {d : ℕ} [NeZero d] (x m k H : ℕ) (s : ℂ) :
    lemma6RawAModulusTotal d x m k H s =
      lemma6RawAModulus (d := d) x H (lemma6AdmissiblePairBlock x m k) s := by
  unfold lemma6RawAModulusTotal
  rw [dif_neg (NeZero.ne d)]

theorem lemma6RawAModulusTotal_nonneg (d x m k H : ℕ) (s : ℂ) :
    0 ≤ lemma6RawAModulusTotal d x m k H s := by
  unfold lemma6RawAModulusTotal
  split_ifs
  · exact le_rfl
  · unfold lemma6RawAModulus primSum
    exact tsum_nonneg fun χ => by split_ifs <;> positivity

theorem lemma6AModulusTotal_nonneg (d x m k H : ℕ) (s : ℂ) :
    0 ≤ lemma6AModulusTotal d x m k H s := by
  unfold lemma6AModulusTotal
  split_ifs
  · exact le_rfl
  · unfold lemma6AModulus primSum
    exact tsum_nonneg fun χ => by split_ifs <;> positivity

/-- The equation-(17) `A` block is nonnegative. -/
theorem lemma6ABlockAtAlpha_nonneg (x m l k H : ℕ) (ν : ℝ) :
    0 ≤ lemma6ABlockAtAlpha x m l k H ν := by
  unfold lemma6ABlockAtAlpha
  exact Finset.sum_nonneg fun d _ =>
    mul_nonneg (lemma6LinearWeight_nonneg d)
      (lemma6AModulusTotal_nonneg _ _ _ _ _ _)

/-- The per-conductor `α`-line `A` integrand in norm form, totalized over
all natural moduli. -/
noncomputable def lemma6BlockAContourNorm
    (x m k H d : ℕ) (ν : ℝ) : ℝ :=
  ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
      lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
    lemma6RawAModulusTotal d x m k H (lemma6AlphaPoint x ν)

/-- The per-conductor shifted `β`-line `B` integrand in norm form,
totalized over all natural moduli. -/
noncomputable def lemma6BlockBContourNorm
    (x m k H d : ℕ) (ν : ℝ) : ℝ :=
  ‖(x : ℂ) ^ lemma6BetaPoint x ν *
      lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
    lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν)

theorem integrable_lemma6BlockAContourNorm
    {x d : ℕ} (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ) :
    Integrable (lemma6BlockAContourNorm x m k H d) := by
  have hd0 : d ≠ 0 := by omega
  letI : NeZero d := ⟨hd0⟩
  apply (integrable_kernelNorm_mul_rawAModulus_alpha hd hx hxlog m k H).congr
  filter_upwards with ν
  unfold lemma6BlockAContourNorm
  rw [lemma6RawAModulusTotal_eq x m k H _]

theorem integrable_lemma6BlockBContourNorm
    {x d : ℕ} (hd : 2 ≤ d) (hx : 2 ≤ x)
    (hxlog : 3 ≤ Real.log (x : ℝ)) (m k H : ℕ) :
    Integrable (lemma6BlockBContourNorm x m k H d) := by
  have hd0 : d ≠ 0 := by omega
  letI : NeZero d := ⟨hd0⟩
  apply (integrable_kernelNorm_mul_BModulusTotal_beta hd hx hxlog m k H).congr
  filter_upwards with ν
  rw [lemma6BlockBContourNorm]

/-- The contour-split block estimate underlying equations (19) and (20):
the conductor sum over one occupied dyadic block is bounded by the `α`-line
`A` integral and the shifted `β`-line `B` integral. -/
theorem sum_largeConductor_pairTerm_le_alpha_beta_integrals
    {x : ℕ} (hx : 2 ≤ x) (hxlog : 3 ≤ Real.log (x : ℝ))
    (ε : ℝ) (m l k H : ℕ)
    (hintA : Integrable (fun ν : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
        lemma6ABlockAtAlpha x m l k H ν))
    (hintB : Integrable (fun ν : ℝ =>
      ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
        lemma6BBlockAtBeta x m l k H ν)) :
    (∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
        (fun d => d ∈ lemma6ModulusBlock x l),
      lemma6NmPairTerm x m d k) ≤
      (1 / (2 * Real.pi)) *
        (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
            (∫ ν : ℝ,
              ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
                lemma6ABlockAtAlpha x m l k H ν) +
          (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
            (∫ ν : ℝ,
              ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
                lemma6BBlockAtBeta x m l k H ν)) := by
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  apply (sum_largeConductor_pairTerm_le_modulusBlock_sum x ε m l k).trans
  have hd2 : ∀ d ∈ lemma6ModulusBlock x l, 2 ≤ d := fun d hd =>
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hlog1 hd)).1
  -- per-conductor norm bound, with the linear weight moved inside
  have hper : ∀ d ∈ lemma6ModulusBlock x l,
      lemma6LinearWeight d * ‖lemma6PrimitivePairBlock x m d k‖ ≤
        (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) := by
    intro d hd
    have hd2d := hd2 d hd
    have hd0 : d ≠ 0 := by omega
    letI : NeZero d := ⟨hd0⟩
    have hnorm := norm_lemma6PrimitivePairBlock_le_A_alpha_add_B_beta
      hd2d hx hxlog m k H
      (fun χ hχ => lemma6BHorizontalEdgesVanish_primitive
        hd2d hx hxlog m k H hχ)
      (fun χ hχ => integrable_lemma6BContourIntegrand_beta
        hd2d hx hxlog m k H hχ)
    have hw0 := lemma6LinearWeight_nonneg d
    have hcongA : (∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
          lemma6RawAModulus (d := d) x H (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν)) =
        ∫ ν : ℝ, lemma6BlockAContourNorm x m k H d ν := by
      apply integral_congr_ae
      filter_upwards with ν
      unfold lemma6BlockAContourNorm
      rw [lemma6RawAModulusTotal_eq x m k H _]
    have hcongB : (∫ ν : ℝ,
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
          lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν)) =
        ∫ ν : ℝ, lemma6BlockBContourNorm x m k H d ν := by
      apply integral_congr_ae
      filter_upwards with ν
      rfl
    rw [hcongA, hcongB] at hnorm
    calc
      lemma6LinearWeight d * ‖lemma6PrimitivePairBlock x m d k‖ ≤
          lemma6LinearWeight d *
            ((1 / (2 * Real.pi)) *
              ((∫ ν : ℝ, lemma6BlockAContourNorm x m k H d ν) +
                ∫ ν : ℝ, lemma6BlockBContourNorm x m k H d ν)) :=
        mul_le_mul_of_nonneg_left hnorm hw0
      _ = (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) := by
        simp only [MeasureTheory.integral_const_mul]
        ring
  have hintA' : ∀ d ∈ lemma6ModulusBlock x l,
      Integrable (fun ν : ℝ => lemma6LinearWeight d *
        lemma6BlockAContourNorm x m k H d ν) := fun d hd =>
    (integrable_lemma6BlockAContourNorm (hd2 d hd) hx hxlog m k H).const_mul
      (lemma6LinearWeight d)
  have hintB' : ∀ d ∈ lemma6ModulusBlock x l,
      Integrable (fun ν : ℝ => lemma6LinearWeight d *
        lemma6BlockBContourNorm x m k H d ν) := fun d hd =>
    (integrable_lemma6BlockBContourNorm (hd2 d hd) hx hxlog m k H).const_mul
      (lemma6LinearWeight d)
  -- pointwise majorization of the two block sums
  have hpointA : ∀ ν : ℝ,
      (∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
          lemma6BlockAContourNorm x m k H d ν) ≤
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
          (4 * Real.log (x : ℝ) ^ 2 * lemma6ABlockAtAlpha x m l k H ν) := by
    intro ν
    have hAB : 4 * Real.log (x : ℝ) ^ 2 * lemma6ABlockAtAlpha x m l k H ν =
        ∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
          (4 * Real.log (x : ℝ) ^ 2 *
            lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      unfold lemma6ABlockAtAlpha
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [hAB, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : d ≠ 0 := by have := hd2 d hd; omega
    letI : NeZero d := ⟨hd0⟩
    have hraw : lemma6RawAModulusTotal d x m k H (lemma6AlphaPoint x ν) ≤
        4 * Real.log (x : ℝ) ^ 2 *
          lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) := by
      rw [lemma6RawAModulusTotal_eq x m k H _]
      have htotal : lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) =
          lemma6AModulus (d := d) x H (lemma6AdmissiblePairBlock x m k)
            (lemma6AlphaPoint x ν) := by
        unfold lemma6AModulusTotal
        rw [dif_neg hd0]
      rw [htotal]
      exact lemma6RawAModulus_le_four_log_sq_mul_AModulus_at_alpha
        (d := d) (H := H) hx (lemma6AdmissiblePairBlock x m k) ν
    have h1 : lemma6LinearWeight d * lemma6BlockAContourNorm x m k H d ν =
        ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
          (lemma6LinearWeight d *
            lemma6RawAModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      unfold lemma6BlockAContourNorm
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hraw (lemma6LinearWeight_nonneg d))
      (norm_nonneg _)
  have hpointB : ∀ ν : ℝ,
      (∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
          lemma6BlockBContourNorm x m k H d ν) =
        ‖(x : ℂ) ^ lemma6BetaPoint x ν *
            lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
          lemma6BBlockAtBeta x m l k H ν := by
    intro ν
    unfold lemma6BBlockAtBeta
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    unfold lemma6BlockBContourNorm
    ring
  -- norms of the horizontal factors are ν-independent
  have hKαeq : ∀ ν : ℝ,
      ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ =
        (Real.exp 1 * (x : ℝ)) *
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ := by
    intro ν
    rw [norm_mul, norm_nat_cpow_lemma6AlphaPoint hx]
  have hKβeq : ∀ ν : ℝ,
      ‖(x : ℂ) ^ lemma6BetaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ =
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ := by
    intro ν
    rw [norm_mul, norm_nat_cpow_lemma6BetaPoint hx]
  have hintAmaj : Integrable (fun ν : ℝ =>
      ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
        (4 * Real.log (x : ℝ) ^ 2 * lemma6ABlockAtAlpha x m l k H ν)) := by
    apply (hintA.const_mul
      (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)))).congr
    filter_upwards with ν
    rw [hKαeq]
    ring
  have hintBmaj : Integrable (fun ν : ℝ =>
      ‖(x : ℂ) ^ lemma6BetaPoint x ν *
          lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
        lemma6BBlockAtBeta x m l k H ν) := by
    apply (hintB.const_mul (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2))).congr
    filter_upwards with ν
    rw [hKβeq]
    ring
  calc
    (∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d * ‖lemma6PrimitivePairBlock x m d k‖) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) :=
      Finset.sum_le_sum fun d hd => hper d hd
    _ = (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ, ∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            ∫ ν : ℝ, ∑ d ∈ lemma6ModulusBlock x l, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) := by
      have hsplit : ∀ d ∈ lemma6ModulusBlock x l,
          (1 / (2 * Real.pi)) *
            ((∫ ν : ℝ, lemma6LinearWeight d *
                lemma6BlockAContourNorm x m k H d ν) +
              ∫ ν : ℝ, lemma6LinearWeight d *
                lemma6BlockBContourNorm x m k H d ν) =
          (1 / (2 * Real.pi)) * (∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockAContourNorm x m k H d ν) +
            (1 / (2 * Real.pi)) * (∫ ν : ℝ, lemma6LinearWeight d *
              lemma6BlockBContourNorm x m k H d ν) :=
        fun d _ => by ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum,
        MeasureTheory.integral_finsetSum _ (fun d hd => hintA' d hd),
        MeasureTheory.integral_finsetSum _ (fun d hd => hintB' d hd)]
      ring
    _ ≤ (1 / (2 * Real.pi)) *
          ((∫ ν : ℝ,
              ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
                  lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
                (4 * Real.log (x : ℝ) ^ 2 *
                  lemma6ABlockAtAlpha x m l k H ν)) +
            ∫ ν : ℝ,
              ‖(x : ℂ) ^ lemma6BetaPoint x ν *
                  lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
                lemma6BBlockAtBeta x m l k H ν) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact MeasureTheory.integral_mono
          (MeasureTheory.integrable_finsetSum _ fun d hd => hintA' d hd)
          hintAmaj hpointA
      · exact le_of_eq (integral_congr_ae (ae_of_all _ hpointB))
    _ = (1 / (2 * Real.pi)) *
          (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
              (∫ ν : ℝ,
                ‖lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6AlphaPoint x ν)‖ *
                  lemma6ABlockAtAlpha x m l k H ν) +
            (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
              (∫ ν : ℝ,
                ‖lemma6SmoothingMellinKernel (x : ℝ)
                    (lemma6BetaPoint x ν)‖ *
                  lemma6BBlockAtBeta x m l k H ν)) := by
      have hfunA : (fun ν : ℝ =>
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
            (4 * Real.log (x : ℝ) ^ 2 *
              lemma6ABlockAtAlpha x m l k H ν)) =
          fun ν : ℝ =>
            (4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ))) *
              (‖lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6AlphaPoint x ν)‖ *
                lemma6ABlockAtAlpha x m l k H ν) := by
        funext ν
        rw [hKαeq]
        ring
      have hfunB : (fun ν : ℝ =>
          ‖(x : ℂ) ^ lemma6BetaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
            lemma6BBlockAtBeta x m l k H ν) =
          fun ν : ℝ =>
            (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
              (‖lemma6SmoothingMellinKernel (x : ℝ)
                  (lemma6BetaPoint x ν)‖ *
                lemma6BBlockAtBeta x m l k H ν) := by
        funext ν
        rw [hKβeq]
        ring
      have hAint : (∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6AlphaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
            (4 * Real.log (x : ℝ) ^ 2 *
              lemma6ABlockAtAlpha x m l k H ν)) =
        4 * Real.log (x : ℝ) ^ 2 * (Real.exp 1 * (x : ℝ)) *
          ∫ ν : ℝ,
            ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6AlphaPoint x ν)‖ *
              lemma6ABlockAtAlpha x m l k H ν := by
        rw [hfunA, MeasureTheory.integral_const_mul]
      have hBint : (∫ ν : ℝ,
          ‖(x : ℂ) ^ lemma6BetaPoint x ν *
              lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
            lemma6BBlockAtBeta x m l k H ν) =
        (Real.exp 1 * (x : ℝ) ^ ((1 : ℝ) / 2)) *
          ∫ ν : ℝ,
            ‖lemma6SmoothingMellinKernel (x : ℝ) (lemma6BetaPoint x ν)‖ *
              lemma6BBlockAtBeta x m l k H ν := by
        rw [hfunB, MeasureTheory.integral_const_mul]
      rw [hAint, hBint]

/-- The squared norm of Chen's `α`-line point. -/
theorem norm_sq_lemma6AlphaPoint_le
    {x : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    ‖lemma6AlphaPoint x ν‖ ^ 2 ≤ 4 * (1 + ν ^ 2) := by
  have hlog : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
  have him : (lemma6AlphaPoint x ν).im = ν := by
    change 0 + (ν * 1 + 0 * 0) = ν
    ring
  rw [Complex.sq_norm, Complex.normSq_apply, lemma6AlphaPoint_re, him]
  have h1 : 1 / Real.log (x : ℝ) ≤ 1 := by
    rw [div_le_one hlog]
    exact hxlog
  have h2 : 0 < 1 / Real.log (x : ℝ) := by positivity
  have hu2 : (1 / Real.log (x : ℝ)) ^ 2 ≤ 1 := pow_le_one₀ h2.le h1
  nlinarith [sq_nonneg ν, h2, hu2]

/-- The integer dyadic logarithm against the real logarithm. -/
theorem natLog_two_add_one_le_three_mul_log
    {H : ℕ} (hH : 1 ≤ H) (hlogH : 1 ≤ Real.log (H : ℝ)) :
    (Nat.log 2 H : ℝ) + 1 ≤ 3 * Real.log (H : ℝ) := by
  have h := natLog_two_cast_le hH
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h1 := Real.log_two_gt_d9
    linarith
  have hkey : Real.log (H : ℝ) ≤ 2 * Real.log (H : ℝ) * Real.log 2 := by
    have h2 := mul_le_mul_of_nonneg_right hlog2
      (show (0 : ℝ) ≤ Real.log (H : ℝ) by linarith)
    nlinarith [h2]
  calc
    (Nat.log 2 H : ℝ) + 1 ≤ Real.log (H : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ 2 * Real.log (H : ℝ) + 1 := by
      have h3 : Real.log (H : ℝ) / Real.log 2 ≤ 2 * Real.log (H : ℝ) := by
        rw [div_le_iff₀ hlog2pos]
        linarith
      linarith
    _ ≤ 3 * Real.log (H : ℝ) := by linarith

/-- Crude scale bound for the equation-(14) remainder majorant: all
logarithmic factors are collected into `(log x)^3 (log H)^2` and the
dyadic dependence into the three displayed terms. -/
theorem lemma6RemainderSecondMajorant_le_crude
    {Cp Ct : ℝ} (hCp : 0 < Cp) (hCt : 0 < Ct)
    {x l H : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (hl : 1 ≤ l) (hH : 1 ≤ H)
    (hD4 : 4 ≤ lemma6DyadicModulusScale x l)
    (hlogH : 1 ≤ Real.log (H : ℝ))
    (hlogHH : Real.log ((2 * H * H : ℕ) : ℝ) ≤ 8 * Real.log (x : ℝ))
    (hlogQ : Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
      2 * Real.log (x : ℝ))
    (ν : ℝ) :
    lemma6RemainderSecondMajorant Cp Ct x l H ν ≤
      (36864 * Cp + 200 * Ct ^ 2) * Real.log (x : ℝ) ^ 3 *
        Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
  have hP0 : (0 : ℝ) < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
  have hP : 1 ≤ Real.log (x : ℝ) := hxlog
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlogH
  have hDpos : 0 < lemma6DyadicModulusScale x l := by
    unfold lemma6DyadicModulusScale
    positivity
  have hQge : lemma6DyadicModulusScale x l ≤ (lemma6ModulusCutoff x l : ℝ) :=
    lemma6DyadicModulusScale_le_modulusCutoff x l
  have hQ54 : (lemma6ModulusCutoff x l : ℝ) ≤
      5 / 4 * lemma6DyadicModulusScale x l :=
    lemma6ModulusCutoff_cast_le_five_quarters_scale hD4
  have hR : lemma6DyadicModulusScale x l / 4 ≤
      (lemma6ModulusLowerCutoff x l : ℝ) :=
    lemma6_quarter_scale_le_modulusLowerCutoff hl hD4
  have hRpos : (0 : ℝ) < (lemma6ModulusLowerCutoff x l : ℝ) :=
    (div_pos hDpos (by norm_num)).trans_le hR
  have hRinv : (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
      4 / lemma6DyadicModulusScale x l := by
    have h := one_div_le_one_div_of_le (div_pos hDpos (by norm_num)) hR
    rw [one_div, one_div, inv_div] at h
    exact h
  have hnl : (Nat.log 2 H : ℝ) + 1 ≤ 3 * Real.log (H : ℝ) :=
    natLog_two_add_one_le_three_mul_log hH hlogH
  have hL20 : 0 ≤ Real.log ((2 * H * H : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * H * H by nlinarith [hH]))
  have hL2pow : Real.log ((2 * H * H : ℕ) : ℝ) ^ 3 ≤
      (8 * Real.log (x : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hL20 hlogHH 3
  have hL30 : 0 ≤ Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) :=
    Real.log_nonneg (by linarith [hQge, hD4])
  have hL3pow : Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2 ≤
      (2 * Real.log (x : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hL30 hlogQ 2
  have hnormsq : ‖lemma6AlphaPoint x ν‖ ^ 2 ≤ 4 * (1 + ν ^ 2) :=
    norm_sq_lemma6AlphaPoint_le hxlog ν
  have hharm0 : (0 : ℝ) ≤ (harmonic H : ℝ) := by
    have h : (0 : ℚ) ≤ harmonic H := by
      rw [harmonic_eq_sum_Icc]
      exact Finset.sum_nonneg fun i _ => by positivity
    exact_mod_cast h
  have hharm : (harmonic H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
    have h := harmonic_le_one_add_log H
    linarith
  have hinner0 : 0 ≤ 2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
      ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ := by
    positivity
  have hinner : 2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
        ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
      (5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
        12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l := by
    have e1 : 2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) ≤
        (5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) := by
      rw [show (5 / 2 : ℝ) * (lemma6DyadicModulusScale x l / (H : ℝ)) =
          (5 / 2 * lemma6DyadicModulusScale x l) / (H : ℝ) by ring]
      rw [div_le_div_iff_of_pos_right hHpos]
      nlinarith [hQ54]
    have e2 : ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
        12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l := by
      have h2 := mul_le_mul hnl hRinv (inv_nonneg.mpr hRpos.le)
        (by linarith : (0 : ℝ) ≤ 3 * Real.log (H : ℝ))
      calc ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹ ≤
          (3 * Real.log (H : ℝ)) * (4 / lemma6DyadicModulusScale x l) := h2
        _ = 12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l := by ring
    exact add_le_add e1 e2
  have hpart1 :
      2 * (Cp * ((Nat.log 2 H : ℝ) + 1) *
          (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
            ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) *
          Real.log ((2 * H * H : ℕ) : ℝ) ^ 3) ≤
        36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
    have hcore : Cp * ((Nat.log 2 H : ℝ) + 1) *
          (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
            ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) *
          Real.log ((2 * H * H : ℕ) : ℝ) ^ 3 ≤
        Cp * (3 * Real.log (H : ℝ)) *
          ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
            12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l) *
          (8 * Real.log (x : ℝ)) ^ 3 := by
      have s1 : Cp * ((Nat.log 2 H : ℝ) + 1) ≤ Cp * (3 * Real.log (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hnl hCp.le
      have s2 : Cp * ((Nat.log 2 H : ℝ) + 1) *
            (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
              ((Nat.log 2 H : ℝ) + 1) *
                (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) ≤
          Cp * (3 * Real.log (H : ℝ)) *
            ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l) :=
        mul_le_mul s1 hinner hinner0 (by positivity)
      exact mul_le_mul s2 hL2pow (pow_nonneg hL20 3) (by positivity)
    calc 2 * (Cp * ((Nat.log 2 H : ℝ) + 1) *
          (2 * (lemma6ModulusCutoff x l : ℝ) / (H : ℝ) +
            ((Nat.log 2 H : ℝ) + 1) * (lemma6ModulusLowerCutoff x l : ℝ)⁻¹) *
          Real.log ((2 * H * H : ℕ) : ℝ) ^ 3)
        ≤ 2 * (Cp * (3 * Real.log (H : ℝ)) *
            ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 * Real.log (H : ℝ) / lemma6DyadicModulusScale x l) *
            (8 * Real.log (x : ℝ)) ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hcore
      _ = 3072 * Cp * Real.log (x : ℝ) ^ 3 *
            (Real.log (H : ℝ) * ((5 / 2) *
                (lemma6DyadicModulusScale x l / (H : ℝ))) +
              12 * Real.log (H : ℝ) ^ 2 / lemma6DyadicModulusScale x l) := by
          field_simp [hDpos.ne', hHpos.ne']
          ring
      _ ≤ 3072 * Cp * Real.log (x : ℝ) ^ 3 *
            (Real.log (H : ℝ) ^ 2 * ((5 / 2) *
                (lemma6DyadicModulusScale x l / (H : ℝ))) +
              12 * Real.log (H : ℝ) ^ 2 / lemma6DyadicModulusScale x l) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hLHsq : Real.log (H : ℝ) ≤ Real.log (H : ℝ) ^ 2 := by
            have hsq : Real.log (H : ℝ) * 1 ≤
                Real.log (H : ℝ) * Real.log (H : ℝ) :=
              mul_le_mul_of_nonneg_left hlogH hlogH0.le
            simpa only [pow_two, mul_one] using hsq
          exact add_le_add
            (mul_le_mul_of_nonneg_right hLHsq (by positivity)) le_rfl
      _ = 3072 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            ((5 / 2) * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 / lemma6DyadicModulusScale x l) := by ring
      _ ≤ 3072 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (12 * (lemma6DyadicModulusScale x l / (H : ℝ)) +
              12 * (1 / lemma6DyadicModulusScale x l)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          · exact le_of_eq (by ring)
      _ = 36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l) := by ring
      _ ≤ 36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_right (by positivity)
  have hsq : (Ct * ‖lemma6AlphaPoint x ν‖ *
        Real.sqrt (lemma6ModulusCutoff x l : ℝ) *
        Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) / (H : ℝ)) ^ 2 ≤
      Ct ^ 2 * (4 * (1 + ν ^ 2)) * (lemma6ModulusCutoff x l : ℝ) *
        (2 * Real.log (x : ℝ)) ^ 2 / (H : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ (lemma6ModulusCutoff x l : ℝ) by positivity)]
    have h2 : Ct ^ 2 * ‖lemma6AlphaPoint x ν‖ ^ 2 *
          (lemma6ModulusCutoff x l : ℝ) *
          Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2 ≤
        Ct ^ 2 * (4 * (1 + ν ^ 2)) * (lemma6ModulusCutoff x l : ℝ) *
          (2 * Real.log (x : ℝ)) ^ 2 := by
      have t1 : ‖lemma6AlphaPoint x ν‖ ^ 2 *
            Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2 ≤
          (4 * (1 + ν ^ 2)) * (2 * Real.log (x : ℝ)) ^ 2 :=
        mul_le_mul hnormsq hL3pow (sq_nonneg _) (by positivity)
      calc Ct ^ 2 * ‖lemma6AlphaPoint x ν‖ ^ 2 *
              (lemma6ModulusCutoff x l : ℝ) *
              Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2
          = Ct ^ 2 * (lemma6ModulusCutoff x l : ℝ) *
              (‖lemma6AlphaPoint x ν‖ ^ 2 *
                Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ^ 2) := by ring
        _ ≤ Ct ^ 2 * (lemma6ModulusCutoff x l : ℝ) *
              ((4 * (1 + ν ^ 2)) * (2 * Real.log (x : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left t1 (by positivity)
        _ = Ct ^ 2 * (4 * (1 + ν ^ 2)) * (lemma6ModulusCutoff x l : ℝ) *
              (2 * Real.log (x : ℝ)) ^ 2 := by ring
    exact (div_le_div_iff_of_pos_right
      (by positivity : (0 : ℝ) < (H : ℝ) ^ 2)).2 h2
  have hpart2 : (lemma6ModulusCutoff x l : ℝ) *
        (2 * ((Ct * ‖lemma6AlphaPoint x ν‖ *
            Real.sqrt (lemma6ModulusCutoff x l : ℝ) *
            Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) / (H : ℝ)) ^ 2 *
          (harmonic H : ℝ) ^ 2)) ≤
        200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
    have h1 : (harmonic H : ℝ) ^ 2 ≤ (2 * Real.log (H : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hharm0 hharm 2
    calc (lemma6ModulusCutoff x l : ℝ) *
          (2 * ((Ct * ‖lemma6AlphaPoint x ν‖ *
              Real.sqrt (lemma6ModulusCutoff x l : ℝ) *
              Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) / (H : ℝ)) ^ 2 *
            (harmonic H : ℝ) ^ 2))
        ≤ (5 / 4 * lemma6DyadicModulusScale x l) *
            (2 * ((Ct ^ 2 * (4 * (1 + ν ^ 2)) *
                (lemma6ModulusCutoff x l : ℝ) *
                (2 * Real.log (x : ℝ)) ^ 2 / (H : ℝ) ^ 2) *
              (2 * Real.log (H : ℝ)) ^ 2)) := by
          apply mul_le_mul hQ54 _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hsq h1 (by positivity) (by positivity)
      _ = 160 * Ct ^ 2 *
            (lemma6DyadicModulusScale x l * (lemma6ModulusCutoff x l : ℝ)) *
            (Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by
          field_simp [hHpos.ne']
          ring
      _ ≤ 160 * Ct ^ 2 *
            (lemma6DyadicModulusScale x l *
              (5 / 4 * lemma6DyadicModulusScale x l)) *
            (Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ54 hDpos.le
      _ = 200 * Ct ^ 2 * lemma6DyadicModulusScale x l ^ 2 *
            (Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by ring
      _ ≤ 200 * Ct ^ 2 * lemma6DyadicModulusScale x l ^ 2 *
            (Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
              (1 + ν ^ 2) / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hP23 : Real.log (x : ℝ) ^ 2 ≤ Real.log (x : ℝ) ^ 3 :=
            pow_le_pow_right₀ hP (by norm_num)
          rw [show Real.log (x : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 *
                (1 + ν ^ 2) / (H : ℝ) ^ 2 =
              Real.log (x : ℝ) ^ 2 *
                (Real.log (H : ℝ) ^ 2 * (1 + ν ^ 2) / (H : ℝ) ^ 2) by ring,
            show Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
                (1 + ν ^ 2) / (H : ℝ) ^ 2 =
              Real.log (x : ℝ) ^ 3 *
                (Real.log (H : ℝ) ^ 2 * (1 + ν ^ 2) / (H : ℝ) ^ 2) by ring]
          exact mul_le_mul_of_nonneg_right hP23 (by positivity)
      _ = 200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            ((1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
          ring
      _ ≤ 200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
            (lemma6DyadicModulusScale x l / (H : ℝ) +
              1 / lemma6DyadicModulusScale x l +
              (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_add_of_nonneg_left (by positivity)
  unfold lemma6RemainderSecondMajorant
  rw [show (36864 * Cp + 200 * Ct ^ 2) * Real.log (x : ℝ) ^ 3 *
        Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) =
      36864 * Cp * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) +
        200 * Ct ^ 2 * Real.log (x : ℝ) ^ 3 * Real.log (H : ℝ) ^ 2 *
          (lemma6DyadicModulusScale x l / (H : ℝ) +
            1 / lemma6DyadicModulusScale x l +
            (1 + ν ^ 2) * lemma6DyadicModulusScale x l ^ 2 / (H : ℝ) ^ 2) by
      ring]
  exact add_le_add hpart1 hpart2

/-- An occupied large-conductor dyadic index is positive. -/
theorem lemma6_one_le_of_mem_largeBlockIndices {x l : ℕ} {ε : ℝ}
    (hxlog : 1 ≤ Real.log (x : ℝ)) (hl : l ∈ lemma6LargeBlockIndices x ε) :
    1 ≤ l := by
  rw [lemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, hdl⟩ := hl
  obtain ⟨j, hj1, hj⟩ := lemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hindex : lemma6ModulusBlockIndex x d = j := lemma6ModulusBlockIndex_eq hj
  have hjl : j = l := hindex ▸ hdl
  have hmem : d ∈ lemma6ModulusBlock x l := hjl ▸ hj
  by_contra h
  push Not at h
  interval_cases l
  rw [lemma6ModulusBlock, Finset.mem_filter] at hmem
  have hdsq : (d : ℝ) ≤ (Real.log (x : ℝ)) ^ 100 := by
    have h2 := hmem.2.2.2
    simpa using h2
  have hdd := hd
  rw [lemma6LargeSquarefreeConductors, Finset.mem_filter] at hdd
  have hdlarge := hdd.1
  rw [lemma6LargeConductors, Finset.mem_filter] at hdlarge
  exact hdlarge.2 hdsq

/-- On an occupied block the dyadic scale beats `(log x)^100`. -/
theorem lemma6_log_pow_hundred_lt_dyadicScale {x l : ℕ} {ε : ℝ}
    (hxlog : 1 ≤ Real.log (x : ℝ)) (hl : l ∈ lemma6LargeBlockIndices x ε) :
    (Real.log (x : ℝ)) ^ 100 < lemma6DyadicModulusScale x l := by
  rw [lemma6LargeBlockIndices, Finset.mem_image] at hl
  obtain ⟨d, hd, hdl⟩ := hl
  obtain ⟨j, hj1, hj⟩ := lemma6LargeSquarefreeConductor_exists_block hxlog hd
  have hindex : lemma6ModulusBlockIndex x d = j := lemma6ModulusBlockIndex_eq hj
  have hjl : j = l := hindex ▸ hdl
  have hmem : d ∈ lemma6ModulusBlock x l := hjl ▸ hj
  rw [lemma6ModulusBlock, Finset.mem_filter] at hmem
  have hdlt : (Real.log (x : ℝ)) ^ 100 < (d : ℝ) := by
    have hdd := hd
    rw [lemma6LargeSquarefreeConductors, Finset.mem_filter] at hdd
    have hdlarge := hdd.1
    rw [lemma6LargeConductors, Finset.mem_filter] at hdlarge
    exact lt_of_not_ge hdlarge.2
  exact hdlt.trans_le hmem.2.2.2

/-- On an occupied block with `log x ≥ 3`, the dyadic scale is at least
`54`. -/
theorem lemma6_fiftyfour_le_dyadicScale {x l : ℕ} {ε : ℝ}
    (hxlog : 3 ≤ Real.log (x : ℝ)) (hl : l ∈ lemma6LargeBlockIndices x ε) :
    54 ≤ lemma6DyadicModulusScale x l := by
  have h := lemma6_log_pow_hundred_lt_dyadicScale (by linarith) hl
  have h3 : (3 : ℝ) ^ 100 ≤ (Real.log (x : ℝ)) ^ 100 :=
    pow_le_pow_left₀ (by norm_num) hxlog 100
  have h4 : (54 : ℝ) ≤ (3 : ℝ) ^ 100 := by norm_num
  linarith

/-- The product of a Chen prime pair is at most `x^(2/3)`. -/
theorem chenPairs_product_le_rpow {x : ℕ} (hx : 1 ≤ x) {q : ℕ × ℕ}
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

/-- On an occupied pair block, the dyadic pair scale is at most
`x^(2/3)`. -/
theorem lemma6_pairScale_le_of_mem_pairBlockIndices {x m k : ℕ} (hx : 1 ≤ x)
    (hk : k ∈ lemma6PairBlockIndices x m) :
    lemma6PairDyadicScale x k ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [lemma6PairBlockIndices, Finset.mem_image] at hk
  obtain ⟨q, hqP, hqk⟩ := hk
  have hqchen : q ∈ chenPairs x := (Finset.mem_filter.mp hqP).1
  have hmem : q ∈ lemma6PairBlock x k := by
    obtain ⟨j, hj⟩ := exists_mem_lemma6PairBlock hx hqchen
    have h := lemma6PairBlockIndex_mem ⟨j, hj⟩
    rwa [hqk] at h
  rw [lemma6PairBlock, Finset.mem_filter] at hmem
  exact hmem.2.1.le.trans (chenPairs_product_le_rpow hx hmem.1)

/-- The pair dyadic scale always dominates `x^(13/30)`. -/
theorem lemma6_rpow_thirteen_thirty_le_pairScale (x k : ℕ) :
    (x : ℝ) ^ ((13 : ℝ) / 30) ≤ lemma6PairDyadicScale x k := by
  unfold lemma6PairDyadicScale
  calc (x : ℝ) ^ ((13 : ℝ) / 30) = 1 * (x : ℝ) ^ ((13 : ℝ) / 30) := by ring
    _ ≤ (2 : ℝ) ^ k * (x : ℝ) ^ ((13 : ℝ) / 30) :=
      mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num))
        (Real.rpow_nonneg (by positivity) _)

/-- Eventually `x^(13/30)` is at least `2`. -/
theorem eventually_two_le_rpow_thirteen_thirty :
    ∀ᶠ x : ℕ in atTop, (2 : ℝ) ≤ (x : ℝ) ^ ((13 : ℝ) / 30) := by
  filter_upwards [eventually_ge_atTop 5] with x hx
  have h5 : (5 : ℝ) ≤ x := by exact_mod_cast hx
  have h2 : (2 : ℝ) = ((2 : ℝ) ^ 30) ^ ((1 : ℝ) / 30) := by
    have e1 : ((2 : ℝ) ^ 30) ^ ((1 : ℝ) / 30) =
        (2 : ℝ) ^ (((30 : ℕ) : ℝ) * (1 / 30)) := by
      rw [← Real.rpow_natCast _ 30, ← Real.rpow_mul (by norm_num)]
    rw [e1, show ((30 : ℕ) : ℝ) * (1 / 30) = 1 by norm_num, Real.rpow_one]
  have h3 : (5 : ℝ) ^ ((13 : ℝ) / 30) = ((5 : ℝ) ^ 13) ^ ((1 : ℝ) / 30) := by
    have e1 : ((5 : ℝ) ^ 13) ^ ((1 : ℝ) / 30) =
        (5 : ℝ) ^ (((13 : ℕ) : ℝ) * (1 / 30)) := by
      rw [← Real.rpow_natCast _ 13, ← Real.rpow_mul (by norm_num)]
    rw [e1, show ((13 : ℕ) : ℝ) * (1 / 30) = 13 / 30 by norm_num]
  calc (2 : ℝ) = ((2 : ℝ) ^ 30) ^ ((1 : ℝ) / 30) := h2
    _ ≤ ((5 : ℝ) ^ 13) ^ ((1 : ℝ) / 30) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      norm_num
    _ = (5 : ℝ) ^ ((13 : ℝ) / 30) := h3.symm
    _ ≤ (x : ℝ) ^ ((13 : ℝ) / 30) :=
      Real.rpow_le_rpow (by norm_num) h5 (by norm_num)

/-- For `log x ≥ 3`, the exceptional factor is at least one. -/
theorem one_le_lemma6ExceptionalFactorAt {x l : ℕ}
    (hxlog : 3 ≤ Real.log (x : ℝ)) :
    1 ≤ lemma6ExceptionalFactorAt x l := by
  have hlogx0 : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hloglog : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) :=
    (Real.le_log_iff_exp_le hlogx0).2
      (Real.exp_one_lt_d9.le.trans (by linarith))
  have hD : (Real.log (x : ℝ)) ^ 100 ≤ lemma6DyadicModulusScale x l := by
    unfold lemma6DyadicModulusScale
    calc (Real.log (x : ℝ)) ^ 100 = 1 * (Real.log (x : ℝ)) ^ 100 := by ring
      _ ≤ (2 : ℝ) ^ l * (Real.log (x : ℝ)) ^ 100 :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)
  have hlogD : (1 : ℝ) ≤ Real.log (lemma6DyadicModulusScale x l) := by
    have h1 := Real.log_le_log (by positivity) hD
    rw [Real.log_pow] at h1
    have h2 : (100 : ℝ) ≤ 100 * Real.log (Real.log (x : ℝ)) := by
      nlinarith [hloglog]
    linarith [h2.trans h1]
  have hloglogD : (0 : ℝ) ≤ Real.log (Real.log (lemma6DyadicModulusScale x l)) :=
    Real.log_nonneg hlogD
  have hratio : (0 : ℝ) ≤ 6 * logLogRatio (lemma6DyadicModulusScale x l) := by
    unfold logLogRatio
    exact mul_nonneg (by norm_num)
      (div_nonneg (by linarith) hloglogD)
  unfold lemma6ExceptionalFactorAt lemma6ExceptionalFactor
  exact Real.one_le_exp hratio

/-- A constant times a fixed log power is eventually absorbed by any
positive power of `x`. -/
theorem eventually_const_mul_log_pow_le_rpow (C : ℝ) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, C * (Real.log (x : ℝ)) ^ N ≤ (x : ℝ) ^ δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have htend : Tendsto (fun x : ℕ => (x : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop hδ2).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_pow_nat_le_rpow N hδ2,
    htend.eventually_ge_atTop (max C 1), eventually_ge_atTop 1] with
    x hx1 hx2 hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg hx1'
  have hlog0 : 0 ≤ (Real.log (x : ℝ)) ^ N := by positivity
  calc
    C * (Real.log (x : ℝ)) ^ N ≤ max C 1 * (x : ℝ) ^ (δ / 2) := by
      exact mul_le_mul (le_max_left C 1) hx1 hlog0
        (zero_le_one.trans (le_max_right C 1))
    _ ≤ (x : ℝ) ^ (δ / 2) * (x : ℝ) ^ (δ / 2) := by
      exact mul_le_mul_of_nonneg_right hx2 (Real.rpow_nonneg hx0.le _)
    _ = (x : ℝ) ^ δ := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring

/-- A constant times a smaller power is eventually dominated by a larger
power. -/
theorem eventually_const_mul_rpow_le_rpow (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℕ in atTop, C * (x : ℝ) ^ a ≤ (x : ℝ) ^ b := by
  have h2 : 0 < (b - a) / 2 := by linarith
  have htend : Tendsto (fun x : ℕ => (x : ℝ) ^ ((b - a) / 2)) atTop atTop :=
    (tendsto_rpow_atTop h2).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (max C 1),
    eventually_ge_atTop 1] with x hx hx1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  calc
    C * (x : ℝ) ^ a ≤ (x : ℝ) ^ ((b - a) / 2) * (x : ℝ) ^ a := by
      exact mul_le_mul_of_nonneg_right ((le_max_left C 1).trans hx)
        (Real.rpow_nonneg hx0.le _)
    _ = (x : ℝ) ^ ((b - a) / 2 + a) := by rw [← Real.rpow_add hx0]
    _ ≤ (x : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)

/-- Eventually `log x ≥ 3`. -/
theorem eventually_three_le_log_nat :
    ∀ᶠ x : ℕ in atTop, (3 : ℝ) ≤ Real.log (x : ℝ) := by
  filter_upwards [eventually_ge_atTop 22] with x hx
  have hx22 : (22 : ℝ) ≤ x := by exact_mod_cast hx
  have h1 : Real.exp 3 ≤ 22 := by
    have he := Real.exp_one_lt_d9
    calc Real.exp 3 = Real.exp 1 ^ 3 := by
          rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
          ring
      _ ≤ (2.7182818286 : ℝ) ^ 3 := by
          exact pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
      _ ≤ 22 := by norm_num
  have h2 : (3 : ℝ) ≤ Real.log 22 :=
    (Real.le_log_iff_exp_le (by norm_num)).2 h1
  exact h2.trans (Real.log_le_log (by norm_num) hx22)

/-- On occupied large blocks, the exceptional factor is at most
`2 * x^(ε/32)` eventually. -/
theorem eventually_exceptionalFactor_le_of_mem {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε,
      lemma6ExceptionalFactorAt x l ≤ 2 * (x : ℝ) ^ (ε / 32) := by
  have hδ : (0 : ℝ) < ε / 16 := by positivity
  filter_upwards [eventually_lemma6ExceptionalFactorAt_le_rpow hδ,
    eventually_three_le_log_nat, eventually_ge_atTop 1] with
    x hI hxlog hx1
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hD2T := lemma6_occupied_modulusScale_lt_two_threshold hlog1 hl
  have hT : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hD : lemma6DyadicModulusScale x l ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    linarith
  have hID : lemma6ExceptionalFactorAt x l ≤
      lemma6DyadicModulusScale x l ^ (ε / 16) := hI l
  have h2ε : (2 : ℝ) ^ (ε / 16) ≤ 2 := by
    calc (2 : ℝ) ^ (ε / 16) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  calc lemma6ExceptionalFactorAt x l ≤
        lemma6DyadicModulusScale x l ^ (ε / 16) := hID
    _ ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 2)) ^ (ε / 16) := by
      exact Real.rpow_le_rpow (lemma6DyadicModulusScale_nonneg x l) hD
        hδ.le
    _ = (2 : ℝ) ^ (ε / 16) * ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ (ε / 16) := by
      exact Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _)
    _ = (2 : ℝ) ^ (ε / 16) * (x : ℝ) ^ ((1 : ℝ) / 2 * (ε / 16)) := by
      rw [← Real.rpow_mul hx0.le]
    _ ≤ 2 * (x : ℝ) ^ (ε / 32) := by
      apply mul_le_mul h2ε _ (Real.rpow_nonneg hx0.le _) (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hx1'
      linarith

/-- On occupied large blocks, the equation-(19) cutoff is at most `x^2`
eventually. -/
theorem eventually_equation19HCutoff_le_sq {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε,
      (lemma6Equation19HCutoff x l : ℝ) ≤ (x : ℝ) ^ 2 := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 16 := by norm_num
  have hab : (9 : ℝ) / 16 + ε / 32 < 7 / 8 := by linarith
  filter_upwards [eventually_exceptionalFactor_le_of_mem hε hε',
    eventually_three_le_log_nat,
    eventually_log_pow_nat_le_rpow 100 hδ,
    eventually_const_mul_rpow_le_rpow 4 hab,
    eventually_ge_atTop 2] with x hI hxlog hlogpow hpow hx2
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hD2T := lemma6_occupied_modulusScale_lt_two_threshold hlog1 hl
  have hT : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hD : lemma6DyadicModulusScale x l ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    linarith
  have hIl : lemma6ExceptionalFactorAt x l ≤ 2 * (x : ℝ) ^ (ε / 32) :=
    hI l hl
  have hI0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  have hlog0 : 0 ≤ Real.log (x : ℝ) ^ 100 := by positivity
  have hscale : lemma6Equation19HScale x l ≤ (x : ℝ) ^ (7 / 8 : ℝ) := by
    have h1 : lemma6Equation19HScale x l ≤
        4 * ((Real.log (x : ℝ)) ^ 100 * (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := by
      unfold lemma6Equation19HScale
      have e1 : lemma6DyadicModulusScale x l * (Real.log x) ^ 100 *
            lemma6ExceptionalFactorAt x l ≤
          (2 * (x : ℝ) ^ ((1 : ℝ) / 2)) * (Real.log x) ^ 100 *
            (2 * (x : ℝ) ^ (ε / 32)) := by
        apply mul_le_mul _ hIl hI0 (by positivity)
        exact mul_le_mul_of_nonneg_right hD (by positivity)
      calc lemma6DyadicModulusScale x l * (Real.log x) ^ 100 *
              lemma6ExceptionalFactorAt x l ≤
            (2 * (x : ℝ) ^ ((1 : ℝ) / 2)) * (Real.log x) ^ 100 *
              (2 * (x : ℝ) ^ (ε / 32)) := e1
        _ = 4 * ((Real.log x) ^ 100 *
              ((x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ (ε / 32))) := by ring
        _ = 4 * ((Real.log (x : ℝ)) ^ 100 *
              (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := by
          rw [← Real.rpow_add hx0]
    calc lemma6Equation19HScale x l ≤
          4 * ((Real.log (x : ℝ)) ^ 100 *
            (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := h1
      _ ≤ 4 * ((x : ℝ) ^ ((1 : ℝ) / 16) *
            (x : ℝ) ^ ((1 : ℝ) / 2 + ε / 32)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hlogpow (Real.rpow_nonneg hx0.le _)
      _ = 4 * (x : ℝ) ^ (9 / 16 + ε / 32 : ℝ) := by
        rw [← Real.rpow_add hx0]
        congr 1
        congr 1
        ring
      _ ≤ (x : ℝ) ^ (7 / 8 : ℝ) := hpow
  calc (lemma6Equation19HCutoff x l : ℝ) ≤ lemma6Equation19HScale x l + 1 :=
      (lemma6Equation19HCutoff_cast_lt_scale_add_one x l).le
    _ ≤ (x : ℝ) ^ (7 / 8 : ℝ) + 1 := by linarith [hscale]
    _ ≤ (x : ℝ) ^ 2 := by
      have h2 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
      have h78 : (0 : ℝ) ≤ (x : ℝ) ^ (7 / 8 : ℝ) := Real.rpow_nonneg hx0.le _
      have h9 : (2 : ℝ) ≤ (x : ℝ) ^ (9 / 8 : ℝ) := by
        calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ (2 : ℝ) ^ (9 / 8 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ ≤ (x : ℝ) ^ (9 / 8 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
      have hprod : (x : ℝ) ^ (9 / 8 : ℝ) * (x : ℝ) ^ (7 / 8 : ℝ) =
          (x : ℝ) ^ 2 := by
        rw [← Real.rpow_add hx0, show (9 : ℝ) / 8 + 7 / 8 = 2 by norm_num,
          Real.rpow_two]
      have h22 : (2 : ℝ) ≤ (x : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ (x : ℝ) by linarith)]
      nlinarith [h9, h78, hprod, h22]

/-- On occupied large blocks, the equation-(20) cutoff is at most `x^2`
eventually. -/
theorem eventually_equation20HCutoff_le_sq {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε, ∀ k : ℕ,
      (lemma6Equation20HCutoff x l k ε : ℝ) ≤ (x : ℝ) ^ 2 := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 60 := by norm_num
  have hab : (7 : ℝ) / 12 - 63 * ε / 32 < 3 / 4 := by linarith
  filter_upwards [eventually_exceptionalFactor_le_of_mem hε hε',
    eventually_three_le_log_nat,
    eventually_log_pow_nat_le_rpow 200 hδ,
    eventually_const_mul_rpow_le_rpow 8 hab,
    eventually_ge_atTop 2] with x hI hxlog hlogpow hpow hx2
  intro l hl k
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hD2T := lemma6_occupied_modulusScale_lt_two_threshold hlog1 hl
  have hT : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hD : lemma6DyadicModulusScale x l ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    linarith
  have hDsq : lemma6DyadicModulusScale x l ^ 2 ≤
      4 * (x : ℝ) ^ (1 - 2 * ε : ℝ) := by
    have h2 : lemma6DyadicModulusScale x l ^ 2 ≤
        (2 * (x : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^ 2 :=
      pow_le_pow_left₀ (lemma6DyadicModulusScale_nonneg x l) hD2T.le 2
    have h3 : (2 * (x : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^ 2 =
        4 * (x : ℝ) ^ (1 - 2 * ε : ℝ) := by
      rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num]
      congr 1
      rw [← Real.rpow_two, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    exact h2.trans_eq h3
  have hIl : lemma6ExceptionalFactorAt x l ≤ 2 * (x : ℝ) ^ (ε / 32) :=
    hI l hl
  have hI0 : 0 ≤ lemma6ExceptionalFactorAt x l :=
    (lemma6ExceptionalFactor_pos _).le
  have hlog2000 : 0 ≤ Real.log (x : ℝ) ^ 200 := by positivity
  have hY : (x : ℝ) ^ ((13 : ℝ) / 30) ≤ lemma6PairDyadicScale x k :=
    lemma6_rpow_thirteen_thirty_le_pairScale x k
  have hYpos : 0 < lemma6PairDyadicScale x k :=
    (Real.rpow_pos_of_pos hx0 _).trans_le hY
  have hF : lemma6Equation20HFirstScale x l k ≤
      8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) := by
    have e1 : lemma6Equation20HFirstScale x l k =
        (lemma6DyadicModulusScale x l ^ 2 * (Real.log x) ^ 200 *
            lemma6ExceptionalFactorAt x l) / lemma6PairDyadicScale x k := by
      unfold lemma6Equation20HFirstScale
      ring
    rw [e1, div_le_iff₀ hYpos]
    have e2 : lemma6DyadicModulusScale x l ^ 2 * (Real.log x) ^ 200 *
          lemma6ExceptionalFactorAt x l ≤
        (4 * (x : ℝ) ^ (1 - 2 * ε : ℝ)) * (x : ℝ) ^ ((1 : ℝ) / 60) *
          (2 * (x : ℝ) ^ (ε / 32)) := by
      apply mul_le_mul _ hIl hI0 (by positivity)
      exact mul_le_mul hDsq hlogpow hlog2000 (by positivity)
    have hexp : (1 : ℝ) - 2 * ε + 1 / 60 + ε / 32 =
        (7 / 12 - 63 * ε / 32) + 13 / 30 := by ring
    calc lemma6DyadicModulusScale x l ^ 2 * (Real.log x) ^ 200 *
            lemma6ExceptionalFactorAt x l ≤
          (4 * (x : ℝ) ^ (1 - 2 * ε : ℝ)) * (x : ℝ) ^ ((1 : ℝ) / 60) *
            (2 * (x : ℝ) ^ (ε / 32)) := e2
      _ = 8 * ((x : ℝ) ^ (1 - 2 * ε : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 60) *
            (x : ℝ) ^ (ε / 32)) := by ring
      _ = 8 * (x : ℝ) ^ ((1 - 2 * ε) + 1 / 60 + ε / 32 : ℝ) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ = 8 * ((x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) *
            (x : ℝ) ^ ((13 : ℝ) / 30)) := by
        rw [hexp, Real.rpow_add hx0]
      _ ≤ 8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) *
            lemma6PairDyadicScale x k := by
        calc 8 * ((x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ) *
                (x : ℝ) ^ ((13 : ℝ) / 30))
            = (8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ)) *
                (x : ℝ) ^ ((13 : ℝ) / 30) := by ring
          _ ≤ (8 * (x : ℝ) ^ (7 / 12 - 63 * ε / 32 : ℝ)) *
                lemma6PairDyadicScale x k :=
            mul_le_mul_of_nonneg_left hY (by positivity)
  have hT2 : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hscale : lemma6Equation20HScale x l k ε ≤ (x : ℝ) ^ (3 / 4 : ℝ) := by
    have hF' : lemma6Equation20HFirstScale x l k ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
      hF.trans hpow
    unfold lemma6Equation20HScale
    exact max_le hF' hT2
  have h34 : (x : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have h340 : (0 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
    have h5 : (2 : ℝ) ≤ (x : ℝ) ^ (5 / 4 : ℝ) := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ (5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ (x : ℝ) ^ (5 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
    have hprod : (x : ℝ) ^ (5 / 4 : ℝ) * (x : ℝ) ^ (3 / 4 : ℝ) =
        (x : ℝ) ^ 2 := by
      rw [← Real.rpow_add hx0, show (5 : ℝ) / 4 + 3 / 4 = 2 by norm_num,
        Real.rpow_two]
    have h22 : (2 : ℝ) ≤ (x : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ (x : ℝ) by linarith)]
    nlinarith [h5, h340, hprod, h22]
  calc (lemma6Equation20HCutoff x l k ε : ℝ) ≤
        lemma6Equation20HScale x l k ε + 1 :=
      (lemma6Equation20HCutoff_cast_lt_scale_add_one x l k ε).le
    _ ≤ (x : ℝ) ^ (3 / 4 : ℝ) + 1 := by linarith [hscale]
    _ ≤ (x : ℝ) ^ 2 := h34

/-- Logarithm of the doubled squared cutoffs, for equation (19). -/
theorem eventually_log_two_mul_H19sq_le {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε,
      Real.log ((2 * lemma6Equation19HCutoff x l *
          lemma6Equation19HCutoff x l : ℕ) : ℝ) ≤
        8 * Real.log (x : ℝ) := by
  filter_upwards [eventually_equation19HCutoff_le_sq hε hε',
    eventually_three_le_log_nat, eventually_ge_atTop 2] with
    x hH hxlog hx2
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hHl := hH l hl
  have hH1 : (1 : ℝ) ≤ (lemma6Equation19HCutoff x l : ℝ) := by
    have hle := lemma6Equation19HScale_le_cutoff x l
    have hD := lemma6_fiftyfour_le_dyadicScale hxlog hl
    have hI1 := one_le_lemma6ExceptionalFactorAt (x := x) (l := l) hxlog
    have hInn : (0 : ℝ) ≤ lemma6ExceptionalFactorAt x l := by linarith
    have hDnn : (0 : ℝ) ≤ lemma6DyadicModulusScale x l := by linarith
    have hp : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 := one_le_pow₀ (by linarith)
    have h1 : (1 : ℝ) ≤ lemma6Equation19HScale x l := by
      unfold lemma6Equation19HScale
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ lemma6DyadicModulusScale x l * Real.log (x : ℝ) ^ 100 *
              lemma6ExceptionalFactorAt x l :=
          mul_le_mul (mul_le_mul (by linarith) hp (by positivity) (by linarith))
            hI1 (by linarith) (by positivity)
    linarith
  have hcast : ((2 * lemma6Equation19HCutoff x l *
        lemma6Equation19HCutoff x l : ℕ) : ℝ) =
      2 * (lemma6Equation19HCutoff x l : ℝ) ^ 2 := by
    push_cast
    ring
  have hle : ((2 * lemma6Equation19HCutoff x l *
        lemma6Equation19HCutoff x l : ℕ) : ℝ) ≤ (x : ℝ) ^ 5 := by
    rw [hcast]
    have h1 : (lemma6Equation19HCutoff x l : ℝ) ^ 2 ≤ ((x : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hHl 2
    have h2 : ((x : ℝ) ^ 2) ^ 2 = (x : ℝ) ^ 4 := by ring
    have h3 : (x : ℝ) ^ 4 ≤ (x : ℝ) ^ 5 :=
      pow_le_pow_right₀ (by exact_mod_cast (show (1:ℕ) ≤ x by omega) : (1 : ℝ) ≤ x) (by norm_num)
    have h4 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have h5 : (0 : ℝ) < (x : ℝ) ^ 4 := by positivity
    nlinarith [h1, h2, h3, h4, h5]
  have hpos : (0 : ℝ) < (2 * lemma6Equation19HCutoff x l *
      lemma6Equation19HCutoff x l : ℕ) := by
    have hH1n : 1 ≤ lemma6Equation19HCutoff x l := by exact_mod_cast hH1
    exact_mod_cast (mul_pos (by omega : (0 : ℕ) < 2 * lemma6Equation19HCutoff x l)
      (by omega))
  calc Real.log ((2 * lemma6Equation19HCutoff x l *
          lemma6Equation19HCutoff x l : ℕ) : ℝ) ≤
        Real.log ((x : ℝ) ^ 5) := Real.log_le_log hpos hle
    _ = 5 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_cast
    _ ≤ 8 * Real.log (x : ℝ) := by linarith

/-- Logarithm of the doubled squared cutoffs, for equation (20). -/
theorem eventually_log_two_mul_H20sq_le {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε, ∀ k : ℕ,
      Real.log ((2 * lemma6Equation20HCutoff x l k ε *
          lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) ≤
        8 * Real.log (x : ℝ) := by
  filter_upwards [eventually_equation20HCutoff_le_sq hε hε',
    eventually_three_le_log_nat, eventually_ge_atTop 2] with
    x hH hxlog hx2
  intro l hl k
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hHl := hH l hl k
  have hH1 : (1 : ℝ) ≤ (lemma6Equation20HCutoff x l k ε : ℝ) := by
    have hle := lemma6Equation20HScale_le_cutoff x l k ε
    have hT : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
      apply Real.one_le_rpow (by exact_mod_cast (show (1:ℕ) ≤ x by omega) : (1 : ℝ) ≤ x)
      linarith
    have hle2 := lemma6_threshold_le_Equation20HScale x l k ε
    linarith
  have hcast : ((2 * lemma6Equation20HCutoff x l k ε *
        lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) =
      2 * (lemma6Equation20HCutoff x l k ε : ℝ) ^ 2 := by
    push_cast
    ring
  have hle : ((2 * lemma6Equation20HCutoff x l k ε *
        lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) ≤ (x : ℝ) ^ 5 := by
    rw [hcast]
    have h1 : (lemma6Equation20HCutoff x l k ε : ℝ) ^ 2 ≤ ((x : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hHl 2
    have h2 : ((x : ℝ) ^ 2) ^ 2 = (x : ℝ) ^ 4 := by ring
    have h3 : (x : ℝ) ^ 4 ≤ (x : ℝ) ^ 5 :=
      pow_le_pow_right₀ (by exact_mod_cast (show (1:ℕ) ≤ x by omega) : (1 : ℝ) ≤ x) (by norm_num)
    have h4 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have h5 : (0 : ℝ) < (x : ℝ) ^ 4 := by positivity
    nlinarith [h1, h2, h3, h4, h5]
  have hpos : (0 : ℝ) < (2 * lemma6Equation20HCutoff x l k ε *
      lemma6Equation20HCutoff x l k ε : ℕ) := by
    have hH1n : 1 ≤ lemma6Equation20HCutoff x l k ε := by exact_mod_cast hH1
    exact_mod_cast (mul_pos (by omega : (0 : ℕ) < 2 * lemma6Equation20HCutoff x l k ε)
      (by omega))
  calc Real.log ((2 * lemma6Equation20HCutoff x l k ε *
          lemma6Equation20HCutoff x l k ε : ℕ) : ℝ) ≤
        Real.log ((x : ℝ) ^ 5) := Real.log_le_log hpos hle
    _ = 5 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_cast
    _ ≤ 8 * Real.log (x : ℝ) := by linarith

/-- Logarithm of the doubled modulus cutoff, on occupied blocks. -/
theorem eventually_log_two_mul_modulusCutoff_le {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε,
      Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤ 2 * Real.log (x : ℝ) := by
  filter_upwards [eventually_three_le_log_nat, eventually_ge_atTop 25] with
    x hxlog hx25
  intro l hl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hD2T := lemma6_occupied_modulusScale_lt_two_threshold hlog1 hl
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hT : (x : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hD : lemma6DyadicModulusScale x l ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    linarith
  have hQ := lemma6DyadicModulusScale_le_modulusCutoff x l
  have hQ2 : (lemma6ModulusCutoff x l : ℝ) ≤
      lemma6DyadicModulusScale x l + 1 :=
    (lemma6ModulusCutoff_cast_lt_scale_add_one x l).le
  have hx25' : (25 : ℝ) ≤ x := by exact_mod_cast hx25
  have h5 : (5 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ 2 := by
    have hsq : ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = x := by
      have h1 : ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (x : ℝ) ^ (((1 : ℝ) / 2) * 2) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hx0.le]
      rw [h1, show ((1 : ℝ) / 2) * 2 = 1 by norm_num, Real.rpow_one]
    have h1 : (5 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      have h2 : (25 : ℝ) ≤ ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [hsq]
        exact hx25'
      have h3 : (5 : ℝ) ^ 2 ≤ ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [show (5 : ℝ) ^ 2 = 25 by ring]
        exact h2
      exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hx0.le _) h3
    calc (5 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2) ≤
          (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)
      _ = ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by ring
      _ = x := hsq
      _ ≤ (x : ℝ) ^ 2 := by
        nth_rw 1 [← Real.rpow_one (x : ℝ)]
        rw [← Real.rpow_natCast (x : ℝ) 2]
        exact Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)
  have hle : 2 * (lemma6ModulusCutoff x l : ℝ) ≤ (x : ℝ) ^ 2 := by
    nlinarith [hQ2, hD, h5, Real.rpow_nonneg hx0.le ((1 : ℝ) / 2)]
  have hpos : (0 : ℝ) < 2 * (lemma6ModulusCutoff x l : ℝ) := by
    have h54 := lemma6_fiftyfour_le_dyadicScale hxlog hl
    linarith [hQ]
  calc Real.log (2 * (lemma6ModulusCutoff x l : ℝ)) ≤
        Real.log ((x : ℝ) ^ 2) := Real.log_le_log hpos hle
    _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_cast

/-- On occupied blocks, the exceptional factor times `(log x)^100` is at
most `Y` eventually. -/
theorem eventually_exceptionalFactor_mul_log100_le_pairScale {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε, ∀ k : ℕ,
      lemma6ExceptionalFactorAt x l * (Real.log (x : ℝ)) ^ 100 ≤
        lemma6PairDyadicScale x k := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 16 := by norm_num
  have hab : (1 : ℝ) / 16 + ε / 32 < 13 / 30 := by linarith
  filter_upwards [eventually_exceptionalFactor_le_of_mem hε hε',
    eventually_log_pow_nat_le_rpow 100 hδ,
    eventually_const_mul_rpow_le_rpow 2 hab,
    eventually_ge_atTop 1] with x hI hlogpow hpow hx1
  intro l hl k
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg hx1'
  have hIl := hI l hl
  have hlog0 : 0 ≤ Real.log (x : ℝ) ^ 100 := by positivity
  calc lemma6ExceptionalFactorAt x l * (Real.log (x : ℝ)) ^ 100 ≤
        (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) :=
      mul_le_mul hIl hlogpow hlog0 (by positivity)
    _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 16 + ε / 32 : ℝ) := by
      rw [show (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) =
          2 * ((x : ℝ) ^ (ε / 32) * (x : ℝ) ^ ((1 : ℝ) / 16)) by ring]
      rw [← Real.rpow_add hx0]
      congr 1
      congr 1
      ring
    _ ≤ (x : ℝ) ^ ((13 : ℝ) / 30) := hpow
    _ ≤ lemma6PairDyadicScale x k :=
      lemma6_rpow_thirteen_thirty_le_pairScale x k

/-- On occupied blocks, the exceptional factor times `(log x)^100` is at
most the threshold `T` eventually. -/
theorem eventually_exceptionalFactor_mul_log100_le_threshold {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε,
      lemma6ExceptionalFactorAt x l * (Real.log (x : ℝ)) ^ 100 ≤
        (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 16 := by norm_num
  have hab : (1 : ℝ) / 16 + ε / 32 < (1 : ℝ) / 2 - ε := by linarith
  filter_upwards [eventually_exceptionalFactor_le_of_mem hε hε',
    eventually_log_pow_nat_le_rpow 100 hδ,
    eventually_const_mul_rpow_le_rpow 2 hab,
    eventually_ge_atTop 1] with x hI hlogpow hpow hx1
  intro l hl
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg hx1'
  have hIl := hI l hl
  have hlog0 : 0 ≤ Real.log (x : ℝ) ^ 100 := by positivity
  calc lemma6ExceptionalFactorAt x l * (Real.log (x : ℝ)) ^ 100 ≤
        (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) :=
      mul_le_mul hIl hlogpow hlog0 (by positivity)
    _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 16 + ε / 32 : ℝ) := by
      rw [show (2 * (x : ℝ) ^ (ε / 32)) * (x : ℝ) ^ ((1 : ℝ) / 16) =
          2 * ((x : ℝ) ^ (ε / 32) * (x : ℝ) ^ ((1 : ℝ) / 16)) by ring]
      rw [← Real.rpow_add hx0]
      congr 1
      congr 1
      ring
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - ε) := hpow

/-- On occupied blocks, `(log x)^200` times the exceptional factor is at
most `Y` eventually. -/
theorem eventually_log200_mul_exceptionalFactor_le_pairScale {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∀ᶠ x : ℕ in atTop, ∀ l ∈ lemma6LargeBlockIndices x ε, ∀ k : ℕ,
      (Real.log (x : ℝ)) ^ 200 * lemma6ExceptionalFactorAt x l ≤
        lemma6PairDyadicScale x k := by
  have hδ : (0 : ℝ) < (1 : ℝ) / 60 := by norm_num
  have hab : (1 : ℝ) / 60 + ε / 32 < 13 / 30 := by linarith
  filter_upwards [eventually_exceptionalFactor_le_of_mem hε hε',
    eventually_log_pow_nat_le_rpow 200 hδ,
    eventually_const_mul_rpow_le_rpow 2 hab,
    eventually_ge_atTop 1] with x hI hlogpow hpow hx1
  intro l hl k
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx0 : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg
    (by exact_mod_cast hx1)
  have hIl := hI l hl
  have hlog0 : 0 ≤ Real.log (x : ℝ) ^ 200 := by positivity
  calc (Real.log (x : ℝ)) ^ 200 * lemma6ExceptionalFactorAt x l ≤
        (x : ℝ) ^ ((1 : ℝ) / 60) * (2 * (x : ℝ) ^ (ε / 32)) :=
      mul_le_mul hlogpow hIl (lemma6ExceptionalFactor_pos _).le
        (Real.rpow_nonneg hx0.le _)
    _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 60 + ε / 32 : ℝ) := by
      rw [show (x : ℝ) ^ ((1 : ℝ) / 60) * (2 * (x : ℝ) ^ (ε / 32)) =
          2 * ((x : ℝ) ^ ((1 : ℝ) / 60) * (x : ℝ) ^ (ε / 32)) by ring]
      rw [← Real.rpow_add hx0]
    _ ≤ (x : ℝ) ^ ((13 : ℝ) / 30) := hpow
    _ ≤ lemma6PairDyadicScale x k :=
      lemma6_rpow_thirteen_thirty_le_pairScale x k


/-- Focused analytic target for equations (19) and (20): every occupied
`(l,k)` block has the paper's `x/(log x)^20` bound. -/
def Lemma6LargePairBlockEstimate (ε : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop, Even x →
    ∀ m : ℕ, 1 < m →
      (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
      ∀ l ∈ lemma6LargeBlockIndices x ε,
        ∀ k ∈ lemma6PairBlockIndices x m,
          ∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
              (fun d => d ∈ lemma6ModulusBlock x l),
            lemma6NmPairTerm x m d k ≤
          A * (x : ℝ) / (Real.log x) ^ 20

/-- Equations (14)--(20), with the derivative fourth moment exposing the
precise dependence on Lemma 3. -/
theorem lemma6_large_pair_block_estimate_of_deriv_fourth_moment
    (hfourth : Lemma6DerivativeFourthMoment)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    Lemma6LargePairBlockEstimate ε := by
  sorry

/-- Summing the `O((log x)^2)` occupied blocks loses exactly two logarithms. -/
theorem lemma6_nmLarge_le_log18_of_pair_block_estimate
    {ε : ℝ} (hblock : Lemma6LargePairBlockEstimate ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, Even x →
      ∀ m : ℕ, 1 < m →
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
        lemma6NmLarge x ε m ≤
          B * (x : ℝ) / (Real.log x) ^ 18 := by
  obtain ⟨A, hA, hblock⟩ := hblock
  let cL : ℝ := 1 / Real.log 2 + 2
  let cK : ℝ := 2 / Real.log 2 + 1
  let B : ℝ := cL * cK * A
  refine ⟨B, by dsimp only [B, cL, cK]; positivity, ?_⟩
  have hlogOneReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [hblock, hlogOne] with x hxblock hxlog
  intro hxEven m hm1 hmx
  have hx1 : 1 ≤ x := by
    by_contra hx
    have : x = 0 := by omega
    subst x
    norm_num at hxlog
  let R : ℝ := A * (x : ℝ) / (Real.log x) ^ 20
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hperL : ∀ l ∈ lemma6LargeBlockIndices x ε,
      ∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
          (fun d => d ∈ lemma6ModulusBlock x l),
        ∑ k ∈ lemma6PairBlockIndices x m,
          lemma6NmPairTerm x m d k ≤
        ((lemma6PairBlockIndices x m).card : ℝ) * R := by
    intro l hl
    rw [Finset.sum_comm]
    calc
      ∑ k ∈ lemma6PairBlockIndices x m,
          ∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
              (fun d => d ∈ lemma6ModulusBlock x l),
            lemma6NmPairTerm x m d k ≤
        ∑ _k ∈ lemma6PairBlockIndices x m, R := by
          apply Finset.sum_le_sum
          intro k hk
          simpa only [R] using hxblock hxEven m hm1 hmx l hl k hk
      _ = ((lemma6PairBlockIndices x m).card : ℝ) * R := by simp
  have hmajor := lemma6NmLarge_le_sum_pairBlocks
    (x := x) (m := m) (ε := ε) hx1 hxlog
  have hdouble :
      ∑ l ∈ lemma6LargeBlockIndices x ε,
        ∑ d ∈ (lemma6LargeSquarefreeConductors x ε).filter
            (fun d => d ∈ lemma6ModulusBlock x l),
          ∑ k ∈ lemma6PairBlockIndices x m,
            lemma6NmPairTerm x m d k ≤
      ((lemma6LargeBlockIndices x ε).card : ℝ) *
        (((lemma6PairBlockIndices x m).card : ℝ) * R) := by
    calc
      _ ≤ ∑ _l ∈ lemma6LargeBlockIndices x ε,
          ((lemma6PairBlockIndices x m).card : ℝ) * R := by
        apply Finset.sum_le_sum
        intro l hl
        exact hperL l hl
      _ = ((lemma6LargeBlockIndices x ε).card : ℝ) *
          (((lemma6PairBlockIndices x m).card : ℝ) * R) := by simp
  have hcL := card_lemma6LargeBlockIndices_cast_le_log
    (x := x) (ε := ε) hxlog
  have hcK := card_lemma6PairBlockIndices_cast_le_log
    (x := x) (m := m) hx1 hxlog
  apply hmajor.trans
  apply hdouble.trans
  calc
    ((lemma6LargeBlockIndices x ε).card : ℝ) *
        (((lemma6PairBlockIndices x m).card : ℝ) * R) ≤
      (cL * Real.log x) * ((cK * Real.log x) * R) := by
        gcongr
    _ = B * (x : ℝ) / (Real.log x) ^ 18 := by
      dsimp only [B, R]
      field_simp

/-- Equations (13), (19), and (20): the positive dyadic conductor blocks. -/
theorem lemma6_nmLarge_le_log18_of_deriv_fourth_moment
    (hfourth : Lemma6DerivativeFourthMoment)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, Even x →
      ∀ m : ℕ, 1 < m →
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
        lemma6NmLarge x ε m ≤
          B * (x : ℝ) / (Real.log x) ^ 18 :=
  lemma6_nmLarge_le_log18_of_pair_block_estimate
    (lemma6_large_pair_block_estimate_of_deriv_fourth_moment
      hfourth ε hε hε')

/-- Equation (21): small conductors are handled by shifting the contour into
the classical zero-free region. This input is independent of Lemma 3. -/
theorem lemma6_nmSmall_le_log18
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, Even x →
      ∀ m : ℕ, 1 < m →
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
        lemma6NmSmall x ε m ≤
          B * (x : ℝ) / (Real.log x) ^ 18 := by
  sorry

/-- Equations (13) and (19)--(21): after decomposing both the conductor and
`p₁p₂` ranges, every `N_m` has a uniform `x/(log x)^18` bound.

Chen proves `x/(log x)^20` for each block. There are `O((log x)^2)` blocks,
which gives the exponent `18` used here. -/
theorem lemma6_nm_le_log18_of_deriv_fourth_moment
    (hfourth : Lemma6DerivativeFourthMoment)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, Even x →
      ∀ m : ℕ, 1 < m →
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
        lemma6Nm x ε m ≤
          B * (x : ℝ) / (Real.log x) ^ 18 := by
  obtain ⟨Blarge, hBlarge, hlarge⟩ :=
    lemma6_nmLarge_le_log18_of_deriv_fourth_moment
      hfourth ε hε hε'
  obtain ⟨Bsmall, hBsmall, hsmall⟩ :=
    lemma6_nmSmall_le_log18 ε hε hε'
  let B : ℝ := Bsmall + Blarge
  refine ⟨B, add_pos hBsmall hBlarge, ?_⟩
  filter_upwards [hsmall, hlarge] with x hxsmall hxlarge
  intro hxEven m hm1 hmx
  rw [lemma6Nm_eq_small_add_large]
  calc
    lemma6NmSmall x ε m + lemma6NmLarge x ε m ≤
        Bsmall * (x : ℝ) / (Real.log x) ^ 18 +
          Blarge * (x : ℝ) / (Real.log x) ^ 18 :=
      add_le_add (hxsmall hxEven m hm1 hmx) (hxlarge hxEven m hm1 hmx)
    _ = B * (x : ℝ) / (Real.log x) ^ 18 := by
      dsimp only [B]
      ring

theorem lemma6_nm_le_log18
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, Even x →
      ∀ m : ℕ, 1 < m →
        (m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) →
        lemma6Nm x ε m ≤
          B * (x : ℝ) / (Real.log x) ^ 18 :=
  lemma6_nm_le_log18_of_deriv_fourth_moment
    lemma6_deriv_fourth_moment ε hε hε'

/-- Strong logarithmic form obtained directly from equations (12)--(21). -/
theorem mTwo_le_log12
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      mTwo x ε ≤ C * (x : ℝ) / (Real.log x) ^ 12 := by
  obtain ⟨A, hA, hreduce⟩ := mTwo_le_log6_mul_nm ε hε hε'
  obtain ⟨B, hB, hblocks⟩ := lemma6_nm_le_log18 ε hε hε'
  let C : ℝ := A * B
  refine ⟨C, mul_pos hA hB, ?_⟩
  have hlogOneReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [hreduce, hblocks, hlogOne] with x hxreduce hxblocks hxlog
  intro hxEven
  obtain ⟨m, hm1, hmx, hmTwo⟩ := hxreduce hxEven
  have hNm := hxblocks hxEven m hm1 hmx
  have hfactor : 0 ≤ A * (Real.log x) ^ 6 := by positivity
  have hlogne : Real.log (x : ℝ) ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hxlog)
  calc
    mTwo x ε ≤ A * (Real.log x) ^ 6 * lemma6Nm x ε m := hmTwo
    _ ≤ A * (Real.log x) ^ 6 *
          (B * (x : ℝ) / (Real.log x) ^ 18) :=
      mul_le_mul_of_nonneg_left hNm hfactor
    _ = C * (x : ℝ) / (Real.log x) ^ 12 := by
      dsimp only [C]
      field_simp [hlogne]

/-- **Lemma 6**: the primitive-character remainder satisfies
`M₂ ≪ x/(log x)^2.01`. -/
theorem mTwo_le
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      mTwo x ε ≤ C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨C, hC, hstrong⟩ := mTwo_le_log12 ε hε hε'
  refine ⟨C, hC, ?_⟩
  have hlogOneReal : ∀ᶠ y : ℝ in atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogOne : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogOneReal
  filter_upwards [hstrong, hlogOne] with x hxstrong hxlog
  intro hxEven
  have hpow :
      (Real.log x) ^ (2.01 : ℝ) ≤ (Real.log x) ^ 12 := by
    calc
      (Real.log x) ^ (2.01 : ℝ) ≤
          (Real.log x) ^ (12 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hxlog
          (by norm_num : (2.01 : ℝ) ≤ 12)
      _ = (Real.log x) ^ (12 : ℕ) :=
        Real.rpow_natCast _ 12
  have hden : 0 < (Real.log x) ^ (2.01 : ℝ) := by
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hxlog) _
  calc
    mTwo x ε ≤ C * (x : ℝ) / (Real.log x) ^ 12 := hxstrong hxEven
    _ ≤ C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg hC.le (by positivity)) hden hpow

end Chen
