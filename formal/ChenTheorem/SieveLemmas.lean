/-
Analytic toolbox: Lemmas 1–4 of Chen's paper.

* Lemma 1 : properties of the smoothing function `Φ`
* Lemma 2 : the large sieve inequality for primitive Dirichlet characters
* Lemma 3 : the fourth-moment bound for Dirichlet `L`-functions on `Re s ≥ 1/2`
* Lemma 4 : the bound `|∑*_{χ mod k} χ(m)| ≤ (m - 1, k)` for squarefree odd `k`

Lemma 1's four qualitative assertions (`chenPhi_eq_zero`, `chenPhi_nonneg`,
`chenPhi_le_one`, `chenPhi_monotoneOn`) are proved in full, by recognizing `Φ`
as a (rescaled) incomplete Gamma integral: `n! · Φ(y) = ∫_{(0,a(y)]} e^{-t}t^n dt`
with `a(y) = (log x)^{1.1} log y`, `n = ⌊log x⌋`, compared against the convergent
Euler integral `n! = ∫_{(0,∞)} e^{-t}t^n dt` (`Real.Gamma_eq_integral`).
Lemmas 1, 2, and 4 are proved in full. Lemma 3 remains a `sorry`-placeholder.
-/
import ChenTheorem.Defs
import ChenTheorem.LargeSieve.Character
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.FunLike.Fintype
import Mathlib.NumberTheory.LSeries.DirichletContinuation

-- The remaining `sorry` is the explicitly documented Lemma 3 target.
set_option warn.sorry false

open Filter Real
open scoped Classical

namespace Chen

/-- Sum of `F` over all *primitive* Dirichlet characters mod `q`.
Stated as a `tsum` so that it is defined for every modulus `q : ℕ`
(for `q ≥ 1` there are only finitely many characters, so this is a finite sum). -/
noncomputable def primSum (q : ℕ) (F : DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑' χ : DirichletCharacter ℂ q, if χ.IsPrimitive then F χ else 0

/-- The `q`-th term `∑*_{χ mod q} |L(s, χ)|⁴` of Lemma 3, defined to be `0` for
`q = 0` (where `DirichletCharacter.LFunction` is not defined) so that it makes
sense to sum over an unrestricted range of moduli `q`. -/
noncomputable def lFourthTerm (q : ℕ) (s : ℂ) : ℝ :=
  if h : q = 0 then 0
  else
    have : NeZero q := ⟨h⟩
    primSum q (fun χ => ‖DirichletCharacter.LFunction χ s‖ ^ 4)

/-! ### Lemma 1 : the smoothing function `Φ` -/

/-- The integrand `t ↦ exp(-t) t^n` occurring in `chenPhi` is continuous. -/
private lemma continuous_gammaIntegrand (n : ℕ) :
    Continuous (fun t : ℝ => Real.exp (-t) * t ^ n) :=
  (Real.continuous_exp.comp continuous_neg).mul (continuous_pow n)

/-- The integrand is nonnegative on `t ≥ 0`. -/
private lemma gammaIntegrand_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Real.exp (-t) * t ^ n :=
  mul_nonneg (Real.exp_pos _).le (pow_nonneg ht n)

/-- The integrand is integrable on any bounded interval `Ioc 0 a` (it is continuous
on all of `ℝ`, hence integrable on the compact set `Icc 0 a`, hence on the subset
`Ioc 0 a`; this covers `a < 0`, where `Ioc 0 a = ∅`, uniformly as well). -/
private lemma integrableOn_gammaIntegrand_Ioc (n : ℕ) (a : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioc 0 a) :=
  (continuous_gammaIntegrand n).integrableOn_Ioc

/-- The integrand is integrable on `(0, ∞)`: this is the convergence of the Euler
integral defining `Γ(n+1)`. -/
private lemma integrableOn_gammaIntegrand_Ioi (n : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  have heq : (fun t : ℝ => Real.exp (-t) * t ^ ((n : ℝ) + 1 - 1)) =
      fun t : ℝ => Real.exp (-t) * t ^ n := by
    funext t
    rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring, Real.rpow_natCast]
  rwa [heq] at h

/-- `n! = ∫_0^∞ e^{-t} t^n dt`, the Euler integral representation of the Gamma
function at the positive integer `n+1`. -/
private lemma factorial_eq_integral (n : ℕ) :
    (n.factorial : ℝ) = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ n := by
  have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← Real.Gamma_nat_eq_factorial n, Real.Gamma_eq_integral hs]
  have hexp : (n : ℝ) + 1 - 1 = (n : ℝ) := by ring
  simp only [hexp, Real.rpow_natCast]

/-- The interval `Ioc 0 a` is empty whenever `a ≤ 0`. -/
private lemma Ioc_zero_eq_empty {a : ℝ} (ha : a ≤ 0) : Set.Ioc (0 : ℝ) a = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact absurd (ht.1.trans_le ht.2) (not_lt.mpr ha)

/-- **Lemma 1**, first assertion: `Φ(y) = 0` for `0 ≤ y ≤ 1`. -/
theorem chenPhi_eq_zero {x y : ℝ} (hx : 1 < x) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
    chenPhi x y = 0 := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hpow : 0 < (Real.log x) ^ (1.1 : ℝ) := Real.rpow_pos_of_pos hlogx _
  have hlogy : Real.log y ≤ 0 := Real.log_nonpos hy₀ hy₁
  have ha : (Real.log x) ^ (1.1 : ℝ) * Real.log y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpow.le hlogy
  unfold chenPhi
  rw [Ioc_zero_eq_empty ha, MeasureTheory.setIntegral_empty, mul_zero]

/-- `0 ≤ Φ(y)` for all `y ≥ 0` (indeed for all real `y`): the prefactor `1/n!` is
positive and the integral of a nonnegative integrand is nonnegative, whether or
not the integration domain `Ioc 0 a` happens to be empty. -/
theorem chenPhi_nonneg (x : ℝ) (_hx : 1 < x) {y : ℝ} (_hy : 0 ≤ y) :
    0 ≤ chenPhi x y := by
  unfold chenPhi
  set n := ⌊Real.log x⌋₊
  set a := (Real.log x) ^ (1.1 : ℝ) * Real.log y
  have hfact : (0 : ℝ) ≤ ((n.factorial : ℝ))⁻¹ := by positivity
  have hint : 0 ≤ ∫ t in Set.Ioc (0 : ℝ) a, Real.exp (-t) * t ^ n :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun t ht => gammaIntegrand_nonneg ht.1.le)
  exact mul_nonneg hfact hint

/-- `Φ(y) ≤ 1` for all real `y`: `Ioc 0 a ⊆ Ioi 0` for any `a`, and the Euler
integral over `Ioi 0` equals `n!`, so the partial integral over `Ioc 0 a` is at
most `n!`, whence dividing by `n!` gives at most `1`. -/
theorem chenPhi_le_one (x : ℝ) (_hx : 1 < x) {y : ℝ} (_hy : 0 ≤ y) :
    chenPhi x y ≤ 1 := by
  unfold chenPhi
  set n := ⌊Real.log x⌋₊
  set a := (Real.log x) ^ (1.1 : ℝ) * Real.log y
  have hmono : ∫ t in Set.Ioc (0 : ℝ) a, Real.exp (-t) * t ^ n ≤
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ n :=
    MeasureTheory.setIntegral_mono_set (integrableOn_gammaIntegrand_Ioi n)
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (MeasureTheory.ae_of_all _ (fun t ht => gammaIntegrand_nonneg ht.le)))
      (HasSubset.Subset.eventuallyLE Set.Ioc_subset_Ioi_self)
  rw [← factorial_eq_integral n] at hmono
  have hfactpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [inv_mul_le_iff₀ hfactpos, mul_one]
  exact hmono

/-- **Lemma 1**, second assertion: `Φ` is non-decreasing on `y ≥ 0`.
For `y₁, y₂ ≤ 1` both sides vanish (`chenPhi_eq_zero`); if `y₁ ≤ 1 ≤ y₂` the claim
is `chenPhi_nonneg`; and for `1 ≤ y₁ ≤ y₂` the upper limit
`a(y) = (log x)^{1.1} log y` of the defining integral is monotone in `y` (as
`log x > 0` and `log` is genuinely monotone on `[1,∞)`), so the integral over the
growing interval `Ioc 0 (a y)` is monotone since the integrand is nonnegative. -/
theorem chenPhi_monotoneOn (x : ℝ) (hx : 1 < x) :
    MonotoneOn (chenPhi x) (Set.Ici 0) := by
  intro y₁ hy₁ y₂ hy₂ hle
  simp only [Set.mem_Ici] at hy₁ hy₂
  by_cases h1 : y₁ ≤ 1
  · by_cases h2 : y₂ ≤ 1
    · rw [chenPhi_eq_zero hx hy₁ h1, chenPhi_eq_zero hx hy₂ h2]
    · rw [chenPhi_eq_zero hx hy₁ h1]
      exact chenPhi_nonneg x hx (hy₁.trans hle)
  · have h1' : 1 < y₁ := not_le.mp h1
    have hy₂' : 1 < y₂ := h1'.trans_le hle
    unfold chenPhi
    set n := ⌊Real.log x⌋₊
    have hlogx : 0 < Real.log x := Real.log_pos hx
    have hpow : 0 ≤ (Real.log x) ^ (1.1 : ℝ) := (Real.rpow_pos_of_pos hlogx _).le
    have hlog : Real.log y₁ ≤ Real.log y₂ := Real.log_le_log (by linarith) hle
    have ha : (Real.log x) ^ (1.1 : ℝ) * Real.log y₁ ≤
        (Real.log x) ^ (1.1 : ℝ) * Real.log y₂ := mul_le_mul_of_nonneg_left hlog hpow
    have hsub : Set.Ioc (0 : ℝ) ((Real.log x) ^ (1.1 : ℝ) * Real.log y₁) ⊆
        Set.Ioc (0 : ℝ) ((Real.log x) ^ (1.1 : ℝ) * Real.log y₂) :=
      Set.Ioc_subset_Ioc (le_refl 0) ha
    have hmono : ∫ t in Set.Ioc (0 : ℝ) ((Real.log x) ^ (1.1 : ℝ) * Real.log y₁),
          Real.exp (-t) * t ^ n ≤
        ∫ t in Set.Ioc (0 : ℝ) ((Real.log x) ^ (1.1 : ℝ) * Real.log y₂),
          Real.exp (-t) * t ^ n :=
      MeasureTheory.setIntegral_mono_set (integrableOn_gammaIntegrand_Ioc n _)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (MeasureTheory.ae_of_all _ (fun t ht => gammaIntegrand_nonneg ht.1.le)))
        (HasSubset.Subset.eventuallyLE hsub)
    have hfact : (0 : ℝ) ≤ ((n.factorial : ℝ))⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hmono hfact

/-- The rate-`c` exponential tail integral `∫_{(a,∞)} e^{-cx} dx = c⁻¹ e^{-ca}`, `c > 0`. -/
private lemma integral_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ∫ x in Set.Ioi a, Real.exp (-(c * x)) = c⁻¹ * Real.exp (-(c * a)) := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun t => Real.exp (-t)) a hc
  simp only [smul_eq_mul] at h
  rw [integral_exp_neg_Ioi] at h
  exact h

/-- The tangent line to `log` at `t = 2`: since `log` is concave, `log t ≤ log 2 + t/2 - 1`
for every `t > 0` (equality at `t = 2`). -/
private lemma log_le_half_sub_one {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ Real.log 2 + t / 2 - 1 := by
  have h2 : (0 : ℝ) < t / 2 := by linarith
  have h := Real.log_le_sub_one_of_pos h2
  rw [Real.log_div ht.ne' (two_ne_zero)] at h
  linarith

/-- The elementary factorial bound `n^n ≤ n! · e^n`, obtained from Stirling's inequality
`√(2πn)(n/e)^n ≤ n!` by discarding the (for `n ≥ 1`) factor `√(2πn) ≥ 1`. -/
private lemma pow_le_factorial_mul_exp (n : ℕ) :
    (n : ℝ) ^ n ≤ (n.factorial : ℝ) * Real.exp n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have hstirling := Stirling.le_factorial_stirling n
    have h1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * n) := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      apply Real.sqrt_le_sqrt
      have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [Real.pi_gt_three]
    have h2 : ((n : ℝ) / Real.exp 1) ^ n ≤ Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n := by
      nlinarith [pow_nonneg (div_nonneg (Nat.cast_nonneg n) (Real.exp_pos 1).le) n]
    have h3 : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := h2.trans hstirling
    rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < Real.exp 1 ^ n)] at h3
    rwa [← Real.exp_nat_mul, mul_one] at h3

/-- Rescaling `t = nx` turns the tail integral from `2n` into a tail integral from `2`:
`∫_{(2n,∞)} e^{-t}t^n dt = n^{n+1} ∫_{(2,∞)} e^{-nx}x^n dx`. -/
private lemma integral_gammaIntegrand_Ioi_two_mul_n (n : ℕ) (hn : 0 < n) :
    ∫ t in Set.Ioi (2 * (n : ℝ)), Real.exp (-t) * t ^ n
      = (n : ℝ) ^ (n + 1) * ∫ x in Set.Ioi (2 : ℝ), Real.exp (-((n : ℝ) * x)) * x ^ n := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun t : ℝ => Real.exp (-t) * t ^ n) (2 : ℝ) hn'
  simp only [smul_eq_mul, mul_pow] at h
  rw [show (n : ℝ) * 2 = 2 * (n : ℝ) by ring] at h
  have hpull : ∫ x in Set.Ioi (2 : ℝ), Real.exp (-((n : ℝ) * x)) * ((n : ℝ) ^ n * x ^ n)
      = (n : ℝ) ^ n * ∫ x in Set.Ioi (2 : ℝ), Real.exp (-((n : ℝ) * x)) * x ^ n := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    ring
  rw [hpull] at h
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  have hmul : (n : ℝ) * ((n : ℝ) ^ n *
        ∫ x in Set.Ioi (2 : ℝ), Real.exp (-((n : ℝ) * x)) * x ^ n)
      = (n : ℝ) * ((n : ℝ)⁻¹ *
        ∫ t in Set.Ioi (2 * (n : ℝ)), Real.exp (-t) * t ^ n) := by rw [h]
  rw [← mul_assoc, mul_inv_cancel_left₀ hn0] at hmul
  rw [← hmul]
  ring

/-- The pointwise bound `e^{-nx}x^n ≤ e^{n(log 2 - 1)} e^{-nx/2}` for `x ≥ 2`,
from the tangent-line bound `log x ≤ log 2 + x/2 - 1` (equality at `x = 2`), integrated
over `(2,∞)` to give `∫_{(2,∞)} e^{-nx}x^n dx ≤ e^{n(log2-1)} · (2/n) e^{-n}`, and hence
`∫_{(2n,∞)} e^{-t}t^n dt ≤ 2 n^n e^{n log2 - 2n}`. -/
private lemma integral_gammaIntegrand_Ioi_two_mul_n_le (n : ℕ) (hn : 0 < n) :
    ∫ t in Set.Ioi (2 * (n : ℝ)), Real.exp (-t) * t ^ n
      ≤ 2 * (n : ℝ) ^ n * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [integral_gammaIntegrand_Ioi_two_mul_n n hn]
  have hg_int : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.exp ((n : ℝ) * (Real.log 2 - 1)) * Real.exp (-((n : ℝ) / 2 * x)))
      (Set.Ioi (2 : ℝ)) := by
    apply MeasureTheory.Integrable.const_mul
    exact (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t)) (2 : ℝ) (show (0 : ℝ) < (n : ℝ) / 2 by positivity)).mpr
      (integrableOn_exp_neg_Ioi _)
  have hf_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (2 : ℝ))]
      (fun x : ℝ => Real.exp (-((n : ℝ) * x)) * x ^ n) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (MeasureTheory.ae_of_all _ fun x hx =>
        mul_nonneg (Real.exp_pos _).le
          (pow_nonneg (by linarith [Set.mem_Ioi.mp hx] : (0:ℝ) ≤ x) n))
  have hpt : (fun x : ℝ => Real.exp (-((n : ℝ) * x)) * x ^ n)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (2 : ℝ))]
      (fun x : ℝ => Real.exp ((n : ℝ) * (Real.log 2 - 1)) * Real.exp (-((n : ℝ) / 2 * x))) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
    apply MeasureTheory.ae_of_all
    intro x hx
    have hxpos : (0 : ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
    have hlog := log_le_half_sub_one hxpos
    have hxn : x ^ n ≤ Real.exp ((n : ℝ) * (Real.log 2 + x / 2 - 1)) := by
      have hxeq : x ^ n = Real.exp (Real.log x) ^ n := by rw [Real.exp_log hxpos]
      rw [hxeq, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n))
    calc Real.exp (-((n : ℝ) * x)) * x ^ n
        ≤ Real.exp (-((n : ℝ) * x)) * Real.exp ((n : ℝ) * (Real.log 2 + x / 2 - 1)) :=
          mul_le_mul_of_nonneg_left hxn (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) * (Real.log 2 - 1)) * Real.exp (-((n : ℝ) / 2 * x)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  have hbound := MeasureTheory.integral_mono_of_nonneg hf_nonneg hg_int hpt
  rw [MeasureTheory.integral_const_mul,
    integral_exp_neg_mul_Ioi (show (0 : ℝ) < (n : ℝ) / 2 by positivity)] at hbound
  have hfinal : Real.exp ((n : ℝ) * (Real.log 2 - 1)) * ((n : ℝ) / 2)⁻¹ *
      Real.exp (-((n : ℝ) / 2 * 2)) = 2 * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) / n := by
    rw [show (n : ℝ) / 2 * 2 = (n : ℝ) by ring,
      show ((n : ℝ) / 2)⁻¹ = 2 / (n : ℝ) by field_simp,
      show Real.exp ((n : ℝ) * (Real.log 2 - 1)) * (2 / (n : ℝ)) * Real.exp (-(n : ℝ))
        = (2 / (n : ℝ)) * (Real.exp ((n : ℝ) * (Real.log 2 - 1)) * Real.exp (-(n : ℝ))) by ring,
      ← Real.exp_add, show (n : ℝ) * (Real.log 2 - 1) + -(n : ℝ) = (n : ℝ) * Real.log 2 - 2 * n by ring]
    ring
  calc (n : ℝ) ^ (n + 1) * ∫ x in Set.Ioi (2 : ℝ), Real.exp (-((n : ℝ) * x)) * x ^ n
      ≤ (n : ℝ) ^ (n + 1) *
          (Real.exp ((n : ℝ) * (Real.log 2 - 1)) * ((n : ℝ) / 2)⁻¹ *
            Real.exp (-((n : ℝ) / 2 * 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hbound]
    _ = (n : ℝ) ^ (n + 1) * (2 * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) / n) := by rw [hfinal]
    _ = 2 * (n : ℝ) ^ n * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) := by
        rw [pow_succ]
        field_simp

/-- **Lemma 1**, main estimate: if `x > 1`, `log x ≥ 10⁴` and `y ≥ exp(2 (log x)^{-0.1})`,
then `1 - x^{-0.1} ≤ Φ(y)`.

(The paper's hypotheses are `log x ≥ 10⁴`, which forces `x > 1` already for the *positive*
reals `x` the paper considers; since `Real.log` uses `|x|` for negative arguments, this
formalization records `x > 1` as an explicit hypothesis so that `x ^ (-0.1 : ℝ)` — genuine
real exponentiation, which behaves differently at negative bases — means what it should.) -/
theorem chenPhi_ge {x y : ℝ} (hx1 : 1 < x) (hx : (10 : ℝ) ^ 4 ≤ Real.log x)
    (hy : Real.exp (2 * (Real.log x) ^ (-(0.1 : ℝ))) ≤ y) :
    1 - x ^ (-(0.1 : ℝ)) ≤ chenPhi x y := by
  have hlogxpos : (0 : ℝ) < Real.log x := by nlinarith [hx]
  set n := ⌊Real.log x⌋₊ with hn_def
  set a := (Real.log x) ^ (1.1 : ℝ) * Real.log y with ha_def
  have hn_ub : (n : ℝ) ≤ Real.log x := Nat.floor_le hlogxpos.le
  have hn_lb : Real.log x - 1 < (n : ℝ) := by
    have := Nat.lt_floor_add_one (Real.log x)
    linarith
  have hn_pos : 0 < n := by
    have : (0 : ℝ) < (n : ℝ) := by nlinarith [hx]
    exact_mod_cast this
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hlogy_lb : 2 * (Real.log x) ^ (-(0.1 : ℝ)) ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos _) hy
    rwa [Real.log_exp] at h
  have hpow_eq : (Real.log x) ^ (1.1 : ℝ) * (Real.log x) ^ (-(0.1 : ℝ)) = Real.log x := by
    rw [← Real.rpow_add hlogxpos]
    norm_num
  have ha_lb : 2 * Real.log x ≤ a := by
    rw [ha_def]
    calc 2 * Real.log x
        = 2 * ((Real.log x) ^ (1.1 : ℝ) * (Real.log x) ^ (-(0.1 : ℝ))) := by rw [hpow_eq]
      _ = (Real.log x) ^ (1.1 : ℝ) * (2 * (Real.log x) ^ (-(0.1 : ℝ))) := by ring
      _ ≤ (Real.log x) ^ (1.1 : ℝ) * Real.log y :=
          mul_le_mul_of_nonneg_left hlogy_lb (Real.rpow_nonneg hlogxpos.le _)
  have ha_ge_2n : 2 * (n : ℝ) ≤ a := by nlinarith [hn_ub, ha_lb]
  have ha_nonneg : 0 ≤ a := by nlinarith [ha_ge_2n, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact absurd (lt_of_le_of_lt ht1.2 ht2) (lt_irrefl t)
  have hsplit : (n.factorial : ℝ) = (∫ t in Set.Ioc (0 : ℝ) a, Real.exp (-t) * t ^ n)
      + ∫ t in Set.Ioi a, Real.exp (-t) * t ^ n := by
    rw [factorial_eq_integral n, ← Set.Ioc_union_Ioi_eq_Ioi ha_nonneg,
      MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        (integrableOn_gammaIntegrand_Ioc n a)
        ((integrableOn_gammaIntegrand_Ioi n).mono_set (Set.Ioi_subset_Ioi ha_nonneg))]
  have hone_sub : 1 - chenPhi x y = (n.factorial : ℝ)⁻¹ * ∫ t in Set.Ioi a, Real.exp (-t) * t ^ n := by
    have hfactpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have hIoc_eq : (∫ t in Set.Ioc (0 : ℝ) a, Real.exp (-t) * t ^ n)
        = (n.factorial : ℝ) - ∫ t in Set.Ioi a, Real.exp (-t) * t ^ n := by linarith [hsplit]
    unfold chenPhi
    rw [hIoc_eq, mul_sub, inv_mul_cancel₀ hfactpos.ne']
    ring
  have hmono2 : (∫ t in Set.Ioi a, Real.exp (-t) * t ^ n)
      ≤ ∫ t in Set.Ioi (2 * (n : ℝ)), Real.exp (-t) * t ^ n :=
    MeasureTheory.setIntegral_mono_set
      ((integrableOn_gammaIntegrand_Ioi n).mono_set (Set.Ioi_subset_Ioi (by positivity)))
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (MeasureTheory.ae_of_all _ (fun t ht =>
          gammaIntegrand_nonneg (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)) ht).le)))
      (HasSubset.Subset.eventuallyLE (Set.Ioi_subset_Ioi ha_ge_2n))
  have hcombine : (∫ t in Set.Ioi a, Real.exp (-t) * t ^ n)
      ≤ 2 * (n : ℝ) ^ n * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) :=
    hmono2.trans (integral_gammaIntegrand_Ioi_two_mul_n_le n hn_pos)
  have hfactle : (n : ℝ) ^ n ≤ (n.factorial : ℝ) * Real.exp n := pow_le_factorial_mul_exp n
  have h1 : 1 - chenPhi x y ≤
      (n.factorial : ℝ)⁻¹ * (2 * (n : ℝ) ^ n * Real.exp ((n : ℝ) * Real.log 2 - 2 * n)) := by
    rw [hone_sub]
    exact mul_le_mul_of_nonneg_left hcombine (by positivity)
  have h2 : (n.factorial : ℝ)⁻¹ * (2 * (n : ℝ) ^ n * Real.exp ((n : ℝ) * Real.log 2 - 2 * n))
      ≤ 2 * Real.exp (n : ℝ) * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) := by
    have hfactpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have hstep : (n.factorial : ℝ)⁻¹ * (n : ℝ) ^ n ≤ Real.exp n := by
      rw [inv_mul_le_iff₀ hfactpos]
      linarith [hfactle]
    calc (n.factorial : ℝ)⁻¹ * (2 * (n : ℝ) ^ n * Real.exp ((n : ℝ) * Real.log 2 - 2 * n))
        = 2 * ((n.factorial : ℝ)⁻¹ * (n : ℝ) ^ n) * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) := by
          ring
      _ ≤ 2 * Real.exp (n : ℝ) * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          nlinarith [hstep]
  have h3 : 1 - chenPhi x y ≤ 2 * Real.exp ((n : ℝ) * (Real.log 2 - 1)) := by
    have heq : Real.exp (n : ℝ) * Real.exp ((n : ℝ) * Real.log 2 - 2 * (n : ℝ))
        = Real.exp ((n : ℝ) * (Real.log 2 - 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc 1 - chenPhi x y
        ≤ 2 * Real.exp (n : ℝ) * Real.exp ((n : ℝ) * Real.log 2 - 2 * n) := by linarith [h1, h2]
      _ = 2 * (Real.exp (n : ℝ) * Real.exp ((n : ℝ) * Real.log 2 - 2 * n)) := by ring
      _ = 2 * Real.exp ((n : ℝ) * (Real.log 2 - 1)) := by rw [heq]
  have hxpos : (0 : ℝ) < x := lt_trans one_pos hx1
  have hrpow_eq : x ^ (-(0.1 : ℝ)) = Real.exp (-(0.1 * Real.log x)) := by
    rw [Real.rpow_def_of_pos hxpos]
    congr 1
    ring
  have hfinal_num : 2 * Real.exp ((n : ℝ) * (Real.log 2 - 1)) ≤ Real.exp (-(0.1 * Real.log x)) := by
    have hlog2ub : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
    have hlog2lb : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hkey : Real.log 2 + (n : ℝ) * (Real.log 2 - 1) ≤ -(0.1 * Real.log x) := by
      have hnmul : (n : ℝ) * (Real.log 2 - 1) ≤ (Real.log x - 1) * (Real.log 2 - 1) := by
        apply mul_le_mul_of_nonpos_right hn_lb.le
        linarith [hlog2ub]
      have step1 : Real.log 2 + (n : ℝ) * (Real.log 2 - 1)
          ≤ Real.log 2 + (Real.log x - 1) * (Real.log 2 - 1) := by linarith [hnmul]
      have step2 : Real.log 2 + (Real.log x - 1) * (Real.log 2 - 1)
          = Real.log x * Real.log 2 - Real.log x + 1 := by ring
      rw [step2] at step1
      have step3 : Real.log x * Real.log 2 ≤ Real.log x * 0.7 :=
        mul_le_mul_of_nonneg_left hlog2ub.le (by linarith [hx])
      linarith [step1, step3, hx]
    calc 2 * Real.exp ((n : ℝ) * (Real.log 2 - 1))
        = Real.exp (Real.log 2) * Real.exp ((n : ℝ) * (Real.log 2 - 1)) := by
          rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ = Real.exp (Real.log 2 + (n : ℝ) * (Real.log 2 - 1)) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-(0.1 * Real.log x)) := Real.exp_le_exp.mpr hkey
  rw [hrpow_eq]
  linarith [h3, hfinal_num]

/-! ### Lemma 2 : the large sieve -/

/-- **Lemma 2**, inequality (2): the large sieve for primitive characters,
`∑_{q ≤ X} (q/φ(q)) ∑*_{χ mod q} |∑_{M < n ≤ M+N} aₙ χ(n)|² ≤ (X² + πN) ∑ |aₙ|²`. -/
theorem large_sieve (X M N : ℕ) (a : ℕ → ℝ) :
    ∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (Nat.totient q : ℝ) *
        primSum q (fun χ => ‖∑ n ∈ Finset.Ioc M (M + N), (a n : ℂ) * χ n‖ ^ 2) ≤
      ((X : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), (a n) ^ 2 := by
  simpa only [primSum, tsum_fintype, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    LargeSieve.large_sieve_character X M N (fun n => (a n : ℂ))

/-- **Lemma 2**, inequality (3): the dyadic form,
`∑_{D < q ≤ Q} φ(q)⁻¹ ∑*_{χ mod q} |∑ aₙ χ(n)|² ≪ (Q + N/D) ∑ |aₙ|²`. -/
theorem large_sieve_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ (D Q M N : ℕ) (a : ℕ → ℝ), 1 ≤ D → D ≤ Q →
      ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
          primSum q (fun χ => ‖∑ n ∈ Finset.Ioc M (M + N), (a n : ℂ) * χ n‖ ^ 2) ≤
        C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), (a n) ^ 2 := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N a hD hDQ
  simpa only [primSum, tsum_fintype, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    hlarge D Q M N (fun n => (a n : ℂ)) hD hDQ

/-! ### Lemma 3 : fourth moment of `L`-functions -/

/-- **Lemma 3**: for `Re s ≥ 1/2`,
`∑_{q ≤ Q} ∑*_{χ mod q} |L(s, χ)|⁴ ≪ Q² |s|² (log Q)⁴`. -/
theorem lFunction_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 1 Q, lFourthTerm q s ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * (Real.log Q) ^ 4 := by
  sorry

/-! ### Lemma 4 : primitive character sums at a point -/

/- The paper factors the primitive sum over the prime divisors of a squarefree modulus.
The next lemmas implement that factorization through the Chinese remainder theorem. -/

private noncomputable def combineChars {a b : ℕ}
    (x : DirichletCharacter ℂ a × DirichletCharacter ℂ b) :
    DirichletCharacter ℂ (a * b) :=
  DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) x.1 *
    DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) x.2

private theorem combineChars_injective {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) : Function.Injective (combineChars (a := a) (b := b)) := by
  rintro ⟨χ, ψ⟩ ⟨χ', ψ'⟩ h
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  dsimp only [combineChars] at h
  have hlev :
      DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) (χ * χ'⁻¹) =
        DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) (ψ' * ψ⁻¹) := by
    simp only [map_mul, map_inv]
    calc
      _ = (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ *
            DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ) *
          ((DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ)⁻¹ *
            (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ')⁻¹) := by group
      _ = (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ' *
            DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ') *
          ((DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ)⁻¹ *
            (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ')⁻¹) := by rw [h]
      _ = _ := by
        rw [show
          (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ' *
              DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ') *
              ((DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ)⁻¹ *
                (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ')⁻¹) =
            (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ' *
                (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ')⁻¹) *
              (DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ' *
                (DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ)⁻¹) by ac_rfl]
        simp
  have hfac := DirichletCharacter.factorsThrough_gcd (χ * χ'⁻¹) (ψ' * ψ⁻¹) hlev
  rw [hab.gcd_eq_one, DirichletCharacter.factorsThrough_one_iff] at hfac
  have hχ : χ = χ' := by
    have h' := congrArg (fun z : DirichletCharacter ℂ a => z * χ') hfac
    simpa [mul_assoc] using h'
  subst χ'
  have hψlev :
      DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ =
        DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ' := by
    exact mul_left_cancel h
  have hψ := DirichletCharacter.changeLevel_injective
    (R := ℂ) (Nat.dvd_mul_left b a) hψlev
  subst ψ'
  rfl

private noncomputable def combineCharsEquiv {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) :
    (DirichletCharacter ℂ a × DirichletCharacter ℂ b) ≃
      DirichletCharacter ℂ (a * b) := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  apply Equiv.ofBijective combineChars
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨combineChars_injective hab, ?_⟩
  rw [← Nat.card_eq_fintype_card
        (α := DirichletCharacter ℂ a × DirichletCharacter ℂ b),
    ← Nat.card_eq_fintype_card (α := DirichletCharacter ℂ (a * b)), Nat.card_prod,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ a,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ b,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (a * b),
    Nat.totient_mul hab]

private theorem conductor_combineChars {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) :
    (combineChars (χ, ψ)).conductor = χ.conductor * ψ.conductor := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  let χa := DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ
  let ψb := DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ
  have hχa : χa.conductor = χ.conductor :=
    DirichletCharacter.conductor_changeLevel χ (Nat.dvd_mul_right a b)
  have hψb : ψb.conductor = ψ.conductor :=
    DirichletCharacter.conductor_changeLevel ψ (Nat.dvd_mul_left b a)
  have hc_coprime : χ.conductor.Coprime ψ.conductor :=
    (hab.of_dvd_left χ.conductor_dvd_level).of_dvd_right ψ.conductor_dvd_level
  have hupper : (combineChars (χ, ψ)).conductor ∣ χ.conductor * ψ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor χa ψb
    rw [show χa * ψb = combineChars (χ, ψ) by rfl, hχa, hψb,
      hc_coprime.lcm_eq_mul] at h
    exact h
  have hχ_dvd : χ.conductor ∣ (combineChars (χ, ψ)).conductor := by
    have hcancel : combineChars (χ, ψ) * ψb⁻¹ = χa := by
      dsimp only [combineChars, χa, ψb]
      simp [mul_assoc]
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor
      (combineChars (χ, ψ)) ψb⁻¹
    rw [hcancel, DirichletCharacter.conductor_inv, hχa, hψb] at h
    exact hc_coprime.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))
  have hψ_dvd : ψ.conductor ∣ (combineChars (χ, ψ)).conductor := by
    have hcancel : combineChars (χ, ψ) * χa⁻¹ = ψb := by
      dsimp only [combineChars, χa, ψb]
      rw [show
        DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ *
              DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ *
              (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ)⁻¹ =
            (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ *
              (DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ)⁻¹) *
              DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ by ac_rfl]
      simp
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor
      (combineChars (χ, ψ)) χa⁻¹
    rw [hcancel, DirichletCharacter.conductor_inv, hψb, hχa] at h
    exact hc_coprime.symm.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm hupper (hc_coprime.mul_dvd_of_dvd_of_dvd hχ_dvd hψ_dvd)

private theorem combineChars_isPrimitive_iff {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) :
    (combineChars (χ, ψ)).IsPrimitive ↔ χ.IsPrimitive ∧ ψ.IsPrimitive := by
  simp only [DirichletCharacter.isPrimitive_def, conductor_combineChars hab]
  constructor
  · intro hprod
    have ha_dvd : a ∣ χ.conductor := by
      apply (hab.of_dvd_right ψ.conductor_dvd_level).dvd_of_dvd_mul_right
      rw [hprod]
      exact Nat.dvd_mul_right a b
    have hb_dvd : b ∣ ψ.conductor := by
      apply (hab.symm.of_dvd_right χ.conductor_dvd_level).dvd_of_dvd_mul_right
      rw [mul_comm, hprod]
      exact Nat.dvd_mul_left b a
    exact ⟨Nat.dvd_antisymm χ.conductor_dvd_level ha_dvd,
      Nat.dvd_antisymm ψ.conductor_dvd_level hb_dvd⟩
  · rintro ⟨hχ, hψ⟩
    rw [hχ, hψ]

private theorem combineChars_apply {a b m : ℕ} [NeZero a] [NeZero b]
    (hm : m.Coprime (a * b)) (χ : DirichletCharacter ℂ a)
    (ψ : DirichletCharacter ℂ b) :
    combineChars (χ, ψ) m = χ m * ψ m := by
  have hm' : IsCoprime (m : ℤ) (a * b : ℤ) := Nat.isCoprime_iff_coprime.mpr hm
  simp only [combineChars, MulChar.mul_apply]
  have hχ : DirichletCharacter.changeLevel (Nat.dvd_mul_right a b) χ (m : ℤ) = χ (m : ℤ) :=
    DirichletCharacter.changeLevel_eq_cast_of_dvd' χ (Nat.dvd_mul_right a b) hm'
  have hψ : DirichletCharacter.changeLevel (Nat.dvd_mul_left b a) ψ (m : ℤ) = ψ (m : ℤ) :=
    DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ (Nat.dvd_mul_left b a) hm'
  simpa only [Int.cast_natCast] using congrArg₂ (· * ·) hχ hψ

private theorem primitiveSum_mul {a b m : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) (hm : m.Coprime (a * b)) :
    (∑' ξ : DirichletCharacter ℂ (a * b), if ξ.IsPrimitive then ξ m else 0) =
      (∑' χ : DirichletCharacter ℂ a, if χ.IsPrimitive then χ m else 0) *
        (∑' ψ : DirichletCharacter ℂ b, if ψ.IsPrimitive then ψ m else 0) := by
  rw [tsum_fintype, tsum_fintype, tsum_fintype,
    ← (combineCharsEquiv hab).sum_comp]
  change (∑ x : DirichletCharacter ℂ a × DirichletCharacter ℂ b,
    if (combineChars x).IsPrimitive then combineChars x m else 0) = _
  rw [Fintype.sum_prod_type]
  simp_rw [combineChars_isPrimitive_iff hab, combineChars_apply hm]
  have hif : ∀ (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b),
      (if χ.IsPrimitive ∧ ψ.IsPrimitive then χ m * ψ m else 0) =
        (if χ.IsPrimitive then χ m else 0) * (if ψ.IsPrimitive then ψ m else 0) := by
    intro χ ψ
    by_cases hχ : χ.IsPrimitive <;> by_cases hψ : ψ.IsPrimitive <;> simp [hχ, hψ]
  simp_rw [hif]
  rw [Finset.sum_mul_sum]

private theorem primitiveSum_one (m : ℕ) :
    ‖∑' χ : DirichletCharacter ℂ 1, if χ.IsPrimitive then χ m else 0‖ ≤
      (Nat.gcd (m - 1) 1 : ℝ) := by
  rw [tsum_fintype]
  simp only [Subsingleton.elim (α := DirichletCharacter ℂ 1) _ 1,
    DirichletCharacter.isPrimitive_one_level_one, if_true]
  have hmz : (m : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [hmz, map_one, Finset.sum_const, Finset.card_univ,
    show Fintype.card (DirichletCharacter ℂ 1) = 1 from Fintype.card_unique,
    one_nsmul, norm_one]
  simp

/-- **Lemma 4, prime case**: for an odd prime `p` and `m ≠ 1`,
`|∑*_{χ mod p} χ(m)| ≤ (m - 1, p)`.

This is the base case (`k = p`) of `primitive_char_sum_bound`: for a *prime* modulus every
nontrivial character is automatically primitive — its conductor divides `p`, hence is `1`
or `p`, and conductor `1` forces the character trivial — so the primitive sum collapses to
`(∑_{all χ} χ(m)) - χ₀(m)`, both terms computable in closed form via Mathlib's Dirichlet
character orthogonality relation (`DirichletCharacter.sum_characters_eq`) and the value of
the principal character. The general squarefree case below combines this base case with a
CRT decomposition and strong induction over the modulus. -/
theorem primitive_char_sum_bound_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (m : ℕ) (hm : m ≠ 1) :
    ‖∑' χ : DirichletCharacter ℂ p, if χ.IsPrimitive then χ m else 0‖ ≤
      (Nat.gcd (m - 1) p : ℝ) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hiff : ∀ χ : DirichletCharacter ℂ p, χ.IsPrimitive ↔ χ ≠ 1 := by
    intro χ
    unfold DirichletCharacter.IsPrimitive
    constructor
    · intro h heq
      rw [heq, DirichletCharacter.conductor_one] at h
      exact hp.ne_one h.symm
    · intro hne
      rcases hp.eq_one_or_self_of_dvd _ χ.conductor_dvd_level with h1 | hpp
      · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1) hne
      · exact hpp
  have hfun_eq : (fun χ : DirichletCharacter ℂ p => if χ.IsPrimitive then (χ m : ℂ) else 0)
      = fun χ => if χ ≠ 1 then (χ m : ℂ) else 0 := by
    funext χ; simp only [hiff]
  rw [hfun_eq, tsum_fintype]
  have hsplit : ∀ χ : DirichletCharacter ℂ p, (if χ ≠ 1 then (χ m : ℂ) else 0)
      = (χ m : ℂ) - (if χ = 1 then (χ m : ℂ) else 0) := by
    intro χ; by_cases h : χ = 1 <;> simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib,
    Fintype.sum_ite_eq' (1 : DirichletCharacter ℂ p) (fun χ => (χ m : ℂ)),
    DirichletCharacter.sum_characters_eq ℂ (m : ZMod p)]
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  by_cases hcase1 : (m : ZMod p) = 1
  · rw [if_pos hcase1]
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · exact absurd hcase1 (by simp)
      · exact h
    have hpdvd : p ∣ (m - 1) :=
      (Nat.modEq_iff_dvd' hm1).mp ((ZMod.natCast_eq_natCast_iff 1 m p).mp (by simpa using hcase1.symm))
    have hgcd : Nat.gcd (m - 1) p = p := Nat.gcd_eq_right hpdvd
    have hunit : IsUnit (m : ZMod p) := hcase1 ▸ isUnit_one
    rw [MulChar.one_apply hunit, Nat.totient_prime hp, hgcd]
    have h1p : (1 : ℕ) ≤ p := hp.one_lt.le
    have heq : ((p - 1 : ℕ) : ℂ) - 1 = (p : ℂ) - 2 := by
      push_cast [Nat.cast_sub h1p]; ring
    rw [heq]
    have : (p : ℂ) - 2 = ((p - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hp3' : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    rw [abs_of_nonneg (by linarith [hp3'] : (0:ℝ) ≤ (p:ℝ) - 2)]
    linarith [hp3']
  · rw [if_neg hcase1, zero_sub, norm_neg]
    by_cases hunit : IsUnit (m : ZMod p)
    · rw [MulChar.one_apply hunit, norm_one]
      have hgcdpos : 1 ≤ Nat.gcd (m - 1) p := Nat.gcd_pos_of_pos_right _ hp.pos
      exact_mod_cast hgcdpos
    · rw [MulChar.map_nonunit _ hunit]
      simp

private theorem primitiveSum_bound_of_prime
    (hprime : ∀ {p : ℕ}, p.Prime → Odd p → ∀ (m : ℕ), m ≠ 1 →
      ‖∑' χ : DirichletCharacter ℂ p, if χ.IsPrimitive then χ m else 0‖ ≤
        (Nat.gcd (m - 1) p : ℝ)) :
    ∀ (k : ℕ), Squarefree k → Odd k → ∀ (m : ℕ), m ≠ 1 →
      ‖∑' χ : DirichletCharacter ℂ k, if χ.IsPrimitive then χ m else 0‖ ≤
        (Nat.gcd (m - 1) k : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk hodd m hm1
      haveI : NeZero k := ⟨hodd.pos.ne'⟩
      by_cases hmk : m.Coprime k
      · by_cases hk1 : k = 1
        · subst k
          exact primitiveSum_one m
        · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hk1
          let n := k / p
          have hpn : p * n = k := by
            dsimp only [n]
            exact Nat.mul_div_cancel' hpdvd
          have hsqprod : Squarefree (p * n) := by rw [hpn]; exact hk
          have hcop : p.Coprime n := Nat.coprime_of_squarefree_mul hsqprod
          have hsqn : Squarefree n := (Nat.squarefree_mul hcop).mp hsqprod |>.2
          have hndvd : n ∣ k := ⟨p, by simpa [mul_comm] using hpn.symm⟩
          have hoddp : Odd p := hodd.of_dvd_nat hpdvd
          have hoddn : Odd n := hodd.of_dvd_nat hndvd
          haveI : NeZero p := ⟨hp.ne_zero⟩
          haveI : NeZero n := ⟨hoddn.pos.ne'⟩
          have hnlt : n < k := by
            dsimp only [n]
            exact Nat.div_lt_self hodd.pos hp.one_lt
          have hmprod : m.Coprime (p * n) := by rwa [hpn]
          have hp_bound := hprime hp hoddp m hm1
          have hn_bound := ih n hnlt hsqn hoddn m hm1
          have hsum := primitiveSum_mul hcop hmprod
          have hgprod_dvd_left :
              Nat.gcd (m - 1) p * Nat.gcd (m - 1) n ∣ m - 1 :=
            (hcop.gcd_both (m - 1) (m - 1)).mul_dvd_of_dvd_of_dvd
              (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
          have hgprod_dvd_right :
              Nat.gcd (m - 1) p * Nat.gcd (m - 1) n ∣ p * n :=
            Nat.mul_dvd_mul (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
          have hgprod_dvd :
              Nat.gcd (m - 1) p * Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) (p * n) :=
            Nat.dvd_gcd hgprod_dvd_left hgprod_dvd_right
          rw [← hpn, hsum, norm_mul]
          calc
            ‖∑' χ : DirichletCharacter ℂ p,
                if χ.IsPrimitive then χ m else 0‖ *
                  ‖∑' ψ : DirichletCharacter ℂ n,
                    if ψ.IsPrimitive then ψ m else 0‖ ≤
                (Nat.gcd (m - 1) p : ℝ) * (Nat.gcd (m - 1) n : ℝ) :=
              mul_le_mul hp_bound hn_bound (norm_nonneg _)
                (by positivity)
            _ = ((Nat.gcd (m - 1) p * Nat.gcd (m - 1) n : ℕ) : ℝ) := by
              norm_cast
            _ ≤ (Nat.gcd (m - 1) (p * n) : ℝ) := by
              exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (mul_pos hp.pos hoddn.pos))
                hgprod_dvd
      · have hm' : ¬ IsCoprime (m : ℤ) (k : ℤ) := by
          simpa only [Nat.isCoprime_iff_coprime] using hmk
        have hz : ∀ χ : DirichletCharacter ℂ k, χ m = 0 := by
          intro χ
          have hz' : χ (m : ℤ) = 0 :=
            (DirichletCharacter.apply_eq_zero_iff χ (m : ℤ)).mpr hm'
          simpa only [Int.cast_natCast] using hz'
        simp_rw [hz]
        simp

/-- **Lemma 4**: for squarefree odd `k` and `m ≠ 1`,
`|∑*_{χ mod k} χ(m)| ≤ (m - 1, k)`.

For `(m, k) ≠ 1` every character value vanishes.  Otherwise, split a nontrivial
squarefree `k` as `p * n`; CRT makes the primitive sum a product of the two
primitive sums, and strong induction reduces it to the prime case. -/
theorem primitive_char_sum_bound (k : ℕ) (hk : Squarefree k) (hodd : Odd k)
    (m : ℕ) (hm : m ≠ 1) :
    ‖∑' χ : DirichletCharacter ℂ k, if χ.IsPrimitive then χ m else 0‖ ≤
      (Nat.gcd (m - 1) k : ℝ) := by
  exact primitiveSum_bound_of_prime
    (fun hp hoddp m hm1 => primitive_char_sum_bound_prime hp hoddp m hm1)
    k hk hodd m hm

end Chen
