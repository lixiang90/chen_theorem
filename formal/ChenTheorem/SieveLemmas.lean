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
Lemma 1's quantitative tail estimate (`chenPhi_ge`) and Lemmas 2–4 remain
`sorry`-placeholders; the statements are the formalization targets.
-/
import ChenTheorem.Defs

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
  sorry

/-- **Lemma 2**, inequality (3): the dyadic form,
`∑_{D < q ≤ Q} φ(q)⁻¹ ∑*_{χ mod q} |∑ aₙ χ(n)|² ≪ (Q + N/D) ∑ |aₙ|²`. -/
theorem large_sieve_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ (D Q M N : ℕ) (a : ℕ → ℝ), 1 ≤ D → D ≤ Q →
      ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
          primSum q (fun χ => ‖∑ n ∈ Finset.Ioc M (M + N), (a n : ℂ) * χ n‖ ^ 2) ≤
        C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), (a n) ^ 2 := by
  sorry

/-! ### Lemma 3 : fourth moment of `L`-functions -/

/-- **Lemma 3**: for `Re s ≥ 1/2`,
`∑_{q ≤ Q} ∑*_{χ mod q} |L(s, χ)|⁴ ≪ Q² |s|² (log Q)⁴`. -/
theorem lFunction_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 1 Q, lFourthTerm q s ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * (Real.log Q) ^ 4 := by
  sorry

/-! ### Lemma 4 : primitive character sums at a point -/

/-- **Lemma 4**: for squarefree odd `k` and `m ≠ 1`,
`|∑*_{χ mod k} χ(m)| ≤ (m - 1, k)`. -/
theorem primitive_char_sum_bound (k : ℕ) (hk : Squarefree k) (hodd : Odd k)
    (m : ℕ) (hm : m ≠ 1) :
    ‖∑' χ : DirichletCharacter ℂ k, if χ.IsPrimitive then χ m else 0‖ ≤
      (Nat.gcd (m - 1) k : ℝ) := by
  sorry

end Chen
