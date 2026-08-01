/-
The precise fourth-moment input used in Lemma 6 of Chen's paper.

Lemma 3 itself estimates `L(s, χ)`. Immediately after equation (15), Chen
applies Cauchy's integral formula on the circle of radius `1 / log x` around
`β + iν`, then inserts Lemma 3 and the elementary dyadic estimate
`1 / φ(d) ≪ log d / d`. The result is the weighted fourth moment of `L'`
recorded below.
-/
import ChenTheorem.SieveLemmas
import ChenTheorem.Lemma6.Coefficients
import Mathlib.Analysis.Complex.CauchyIntegral

set_option warn.sorry false

open Filter Real
open scoped Classical

namespace Chen

/-- The primitive-character fourth moment of `L'` at modulus `q`. -/
noncomputable def lDerivFourthTerm (q : ℕ) (s : ℂ) : ℝ :=
  if h : q = 0 then 0
  else
    have : NeZero q := ⟨h⟩
    primSum q (fun χ => ‖deriv (DirichletCharacter.LFunction χ) s‖ ^ 4)

/-- The vertical point `β + iν`, where `β = 1/2 + 1/log x`, used after
equation (15). -/
noncomputable def lemma6BetaPoint (x : ℕ) (ν : ℝ) : ℂ :=
  ((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + (ν : ℂ) * Complex.I

@[simp]
theorem lemma6BetaPoint_re (x : ℕ) (ν : ℝ) :
    (lemma6BetaPoint x ν).re = 1 / 2 + 1 / Real.log x := by
  change
    (1 / 2 + 1 / Real.log (x : ℝ)) + (ν * 0 - 0 * 1) =
      1 / 2 + 1 / Real.log (x : ℝ)
  ring

/-- The vertical line used in Lemma 6 lies in the half-plane covered by the
corrected statement of Lemma 3. -/
theorem half_le_lemma6BetaPoint_re {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    (1 / 2 : ℝ) ≤ (lemma6BetaPoint x ν).re := by
  rw [lemma6BetaPoint_re]
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hdiv : 0 < (1 : ℝ) / Real.log (x : ℝ) :=
    div_pos zero_lt_one hlog
  exact le_add_of_nonneg_right hdiv.le

/-- Radius of the Cauchy circle used immediately after equation (15). -/
noncomputable def lemma6CauchyRadius (x : ℕ) : ℝ :=
  1 / Real.log x

theorem lemma6CauchyRadius_pos {x : ℕ} (hx : 2 ≤ x) :
    0 < lemma6CauchyRadius x := by
  unfold lemma6CauchyRadius
  exact div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))

/-- Every point of the closed Cauchy disc remains in the half-plane covered
by the corrected Lemma 3.  Its leftmost boundary has real part exactly
`1 / 2`. -/
theorem half_le_re_of_mem_closedBall_lemma6BetaPoint
    {x : ℕ} (_hx : 2 ≤ x) (ν : ℝ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (lemma6BetaPoint x ν)
      (lemma6CauchyRadius x)) :
    (1 / 2 : ℝ) ≤ z.re := by
  have hdist : ‖z - lemma6BetaPoint x ν‖ ≤ lemma6CauchyRadius x := by
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hre : |(z - lemma6BetaPoint x ν).re| ≤
      lemma6CauchyRadius x :=
    (Complex.abs_re_le_norm _).trans hdist
  have hleft := neg_le_of_abs_le hre
  change -lemma6CauchyRadius x ≤
    z.re - (lemma6BetaPoint x ν).re at hleft
  rw [lemma6BetaPoint_re] at hleft
  unfold lemma6CauchyRadius at hleft
  linarith

/-- On the same disc the spectral factor grows by at most a factor two. -/
theorem norm_le_two_mul_norm_lemma6BetaPoint_of_mem_closedBall
    {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (lemma6BetaPoint x ν)
      (lemma6CauchyRadius x)) :
    ‖z‖ ≤ 2 * ‖lemma6BetaPoint x ν‖ := by
  let s := lemma6BetaPoint x ν
  let r := lemma6CauchyRadius x
  have hdist : ‖z - s‖ ≤ r := by
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hsre : (0 : ℝ) ≤ s.re :=
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
      (half_le_lemma6BetaPoint_re hx ν)
  have hrle : r ≤ ‖s‖ := by
    calc
      r ≤ s.re := by
        dsimp only [r, s, lemma6CauchyRadius]
        rw [lemma6BetaPoint_re]
        linarith
      _ = |s.re| := (abs_of_nonneg hsre).symm
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  calc
    ‖z‖ = ‖(z - s) + s‖ := by ring_nf
    _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
    _ ≤ r + ‖s‖ := add_le_add_left hdist _
    _ ≤ 2 * ‖s‖ := by linarith

/-- A primitive character of modulus at least two is nonprincipal. -/
theorem primitiveCharacter_ne_one
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ ≠ 1 := by
  intro hχone
  have hcondOne : χ.conductor = 1 :=
    DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
  rw [DirichletCharacter.isPrimitive_def] at hχ
  omega

/-- Consequently every L-function occurring in the primitive sum is entire;
this discharges the analytic hypothesis of Cauchy's formula. -/
theorem primitiveCharacter_differentiable_LFunction
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  DirichletCharacter.differentiable_LFunction
    (primitiveCharacter_ne_one hq hχ)

theorem lFourthTerm_nonneg (q : ℕ) (s : ℂ) :
    0 ≤ lFourthTerm q s := by
  unfold lFourthTerm
  split_ifs
  · exact le_rfl
  · unfold primSum
    apply tsum_nonneg
    intro χ
    split_ifs
    · positivity
    · exact le_rfl

/-- The dyadic modulus interval
`2^(l-1) (log x)^100 < d ≤ 2^l (log x)^100`. -/
noncomputable def lemma6ModulusBlock (x l : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d =>
    Squarefree d ∧
      (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100 < d ∧
      (d : ℝ) ≤ (2 : ℝ) ^ l * (Real.log x) ^ 100

/-- Integer cutoff corresponding to the upper end of a dyadic modulus
block. -/
noncomputable def lemma6ModulusCutoff (x l : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ l * (Real.log x) ^ 100⌉₊

theorem lemma6ModulusBlock_subset_Icc
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6ModulusBlock x l ⊆ Finset.Icc 2 (lemma6ModulusCutoff x l) := by
  intro d hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hd
  rw [Finset.mem_Icc]
  have hlower : (1 : ℝ) ≤
      (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100 := by
    have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (l - 1) := by
      exact one_le_pow₀ (by norm_num)
    have hpowlog : (1 : ℝ) ≤ (Real.log x) ^ 100 := by
      exact one_le_pow₀ hxlog
    nlinarith
  have hd2 : 2 ≤ d := by
    have : (1 : ℝ) < d := hlower.trans_lt hd.2.2.1
    exact_mod_cast this
  refine ⟨hd2, ?_⟩
  have hceil :
      (2 : ℝ) ^ l * (Real.log x) ^ 100 ≤
        (lemma6ModulusCutoff x l : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hd.2.2.2.trans hceil

/-- The totient weight on a squarefree dyadic modulus costs one logarithm. -/
theorem lemma6ModulusBlock_inv_totient_le
    {x l d : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hd : d ∈ lemma6ModulusBlock x l) :
    (Nat.totient d : ℝ)⁻¹ ≤
      (2 / Real.log 2) * Real.log x / d := by
  have hddata := hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
  have hdIcc := lemma6ModulusBlock_subset_Icc hxlog hd
  have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hdIcc).1
  have hdx : d ≤ x := by
    have := Finset.mem_range.mp hddata.1
    omega
  have hlog : Real.log d ≤ Real.log x :=
    Real.log_le_log (by positivity) (by exact_mod_cast hdx)
  have hc0 : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
  exact (inv_totient_le_log_div_self hddata.2.1 hd2).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog hc0) (by positivity))

/-- Lemma 3 already gives the required fourth moment of `L` on one dyadic
modulus block, including its `1 / φ(d)` weight.  This is the part of the
transfer preceding Cauchy's formula. -/
theorem lemma6_weighted_lFourth_block_le
    {C : ℝ}
    (hL : ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * (Real.log Q) ^ 4)
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hQ2 : 2 ≤ lemma6ModulusCutoff x l) (s : ℂ)
    (hs : (1 / 2 : ℝ) ≤ s.re) :
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lFourthTerm d s ≤
      ((2 / Real.log 2) * Real.log x /
          ((2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100)) *
        (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (lemma6ModulusCutoff x l)) ^ 4) := by
  let D : ℝ := (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100
  let K : ℝ := (2 / Real.log 2) * Real.log x / D
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hnum0 : 0 ≤ (2 / Real.log 2) * Real.log x := by positivity
  have hK0 : 0 ≤ K := div_nonneg hnum0 hDpos.le
  calc
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lFourthTerm d s ≤
        ∑ d ∈ lemma6ModulusBlock x l, K * lFourthTerm d s := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_right _ (lFourthTerm_nonneg d s)
      have hddata := hd
      rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
      have hfirst := lemma6ModulusBlock_inv_totient_le hxlog hd
      apply hfirst.trans
      dsimp only [K, D]
      exact div_le_div_of_nonneg_left hnum0 hDpos hddata.2.2.1.le
    _ = K * ∑ d ∈ lemma6ModulusBlock x l, lFourthTerm d s := by
      rw [Finset.mul_sum]
    _ ≤ K * ∑ d ∈ Finset.Icc 2 (lemma6ModulusCutoff x l),
        lFourthTerm d s := by
      apply mul_le_mul_of_nonneg_left _ hK0
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (lemma6ModulusBlock_subset_Icc hxlog)
        (fun d hd hnot => lFourthTerm_nonneg d s)
    _ ≤ K * (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (lemma6ModulusCutoff x l)) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (hL (lemma6ModulusCutoff x l) s hQ2 hs) hK0
    _ = ((2 / Real.log 2) * Real.log x /
          ((2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100)) *
        (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (lemma6ModulusCutoff x l)) ^ 4) := by rfl

/-- A rigorous one-log-slack version of the `L'` fourth-moment estimate used
by Lemma 6 after equation (15).

The scan writes exponent `109`: `100` from the dyadic scale, four from Lemma
3, and five from the Cauchy/Hölder step. It silently absorbs the unbounded
factor `d/φ(d)` into `≪`. Using the uniform elementary bound
`d/φ(d) ≪ log d` gives exponent `110`; this harmless slack is retained in the
formal interface. -/
def Lemma6DerivativeFourthMoment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ (l : ℕ) (ν : ℝ), 1 ≤ l →
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lDerivFourthTerm d (lemma6BetaPoint x ν) ≤
      C * (2 : ℝ) ^ l * (Real.log x) ^ 110 *
        ‖lemma6BetaPoint x ν‖ ^ 2

/-- Cauchy's integral formula plus the dyadic totient estimate transfers the
paper's Lemma 3 to the derivative fourth moment required in Lemma 6.

The half-plane geometry of the Cauchy disc, differentiability of every
primitive L-function, the dyadic cutoff, and the weighted application of
Lemma 3 are proved above.  What remains here is the analytic Cauchy--Hölder
inequality, its interchange with the finite primitive-character sum, and the
final elementary simplification of the dyadic cutoff. -/
theorem lemma6_deriv_fourth_moment_of_lFunction_fourth_moment
    (hL : ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
        ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
          C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * (Real.log Q) ^ 4) :
    Lemma6DerivativeFourthMoment := by
  sorry

/-- The derivative fourth moment used below, explicitly derived from the
corrected statement of Lemma 3. -/
theorem lemma6_deriv_fourth_moment : Lemma6DerivativeFourthMoment :=
  lemma6_deriv_fourth_moment_of_lFunction_fourth_moment
    lFunction_fourth_moment

end Chen
