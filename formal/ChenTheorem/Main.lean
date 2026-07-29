/-
The main results: the key inequality (28) and Theorems 1 and 2 of Chen's paper.

The deduction of Theorem 1 is:
  (28)      `P_x(1,2) ≥ P_x(x, x^{1/10}) - (1/2) ∑ P_x(x, p, x^{1/10}) - Ω/2 - x^{0.91}`
  Lemma 9   lower-bounds the sieve terms by `2.6408 x C_x/(log x)²`,
  Lemma 8   upper-bounds `Ω/2` by `1.9702 x C_x/(log x)²`,
and `2.6408 - 1.9702 = 0.6706 > 0.67`, the term `x^{0.91}` being negligible
against `x C_x/(log x)²` (using `C_x ≥ twinConst > 0`).

The remaining analytic inputs are isolated in their supporting modules; this
file proves the final deductions from those named interfaces.
-/
import ChenTheorem.Main.KeyInequality
import ChenTheorem.Main.ShiftedEstimate

open Filter Real
open scoped Classical

namespace Chen

/-- Inequality **(28)** of the paper: every prime counted by
`P_x(x, x^{1/10})` but not by `P_x(1,2)` forces `x - p` to have at least three
prime factors, all `> x^{1/10}`; such `p` are accounted for (with multiplicity)
by `(1/2) ∑ P_x(x, p', x^{1/10}) + Ω/2`, up to `O(x^{0.91})` degenerate cases. -/
theorem key_inequality :
    ∀ᶠ x : ℕ in atTop, Even x →
      (sievedPrimeCount x : ℝ) -
          (1 / 2) * ∑ p' ∈ midPrimes x, (sievedPrimeCountAt x p' : ℝ) -
          (sieveOmega x : ℝ) / 2 - (x : ℝ) ^ (0.91 : ℝ) ≤
        (chenCount x : ℝ) := by
  exact key_inequality_of_witness_count

/-- The explicit `x^0.91` loss in (28) is eventually smaller than the
`0.0006` margin between Chen's numerical constants. -/
theorem eventually_rpow_091_le_singular_error :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (0.91 : ℝ) ≤
        0.0006 * (x : ℝ) * chenConst x /
          (Real.log x) ^ 2 := by
  let k : ℝ := 0.0006 * twinConst
  have hk : 0 < k := by
    dsimp only [k]
    exact mul_pos (by norm_num) twinConst_pos
  have hlogReal :
      ∀ᶠ y : ℝ in atTop,
        ‖Real.log y ^ (2 : ℝ)‖ ≤
          k * ‖y ^ (0.09 : ℝ)‖ :=
    (isLittleO_log_rpow_rpow_atTop
      (2 : ℝ) (by norm_num : (0 : ℝ) < 0.09)).def hk
  have hlogNat :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  have hlogOne :
      ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 1)
  filter_upwards [hlogNat, hlogOne, eventually_ge_atTop 1] with
      x hlog hlogOne hx
  have hxpos : (0 : ℝ) < x := by
    exact zero_lt_one.trans_le (by exact_mod_cast hx)
  have hlogpos : 0 < Real.log (x : ℝ) :=
    zero_lt_one.trans_le hlogOne
  have hlogsq :
      (Real.log x) ^ 2 ≤ k * (x : ℝ) ^ (0.09 : ℝ) := by
    simpa [Real.rpow_natCast,
      Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hlog
  have hpow :
      (x : ℝ) ^ (0.91 : ℝ) *
          (x : ℝ) ^ (0.09 : ℝ) = x := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsmall :
      (x : ℝ) ^ (0.91 : ℝ) ≤
        k * (x : ℝ) / (Real.log x) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).2
    calc
      (x : ℝ) ^ (0.91 : ℝ) * (Real.log x) ^ 2 ≤
          (x : ℝ) ^ (0.91 : ℝ) *
            (k * (x : ℝ) ^ (0.09 : ℝ)) := by
        gcongr
      _ = k * ((x : ℝ) ^ (0.91 : ℝ) *
          (x : ℝ) ^ (0.09 : ℝ)) := by ring
      _ = k * (x : ℝ) := by rw [hpow]
  have hconst := twinConst_le_chenConst x
  calc
    (x : ℝ) ^ (0.91 : ℝ) ≤
        k * (x : ℝ) / (Real.log x) ^ 2 := hsmall
    _ ≤ 0.0006 * (x : ℝ) * chenConst x /
          (Real.log x) ^ 2 := by
      dsimp only [k]
      have hden : 0 ≤ ((Real.log x) ^ 2)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        0.0006 * twinConst * (x : ℝ) *
            ((Real.log x) ^ 2)⁻¹ =
          0.0006 * (x : ℝ) * twinConst *
            ((Real.log x) ^ 2)⁻¹ := by ring
        _ ≤ 0.0006 * (x : ℝ) * chenConst x *
            ((Real.log x) ^ 2)⁻¹ := by gcongr

/-- **Theorem 1 (quantitative form)**: for all sufficiently large even `x`,
`P_x(1,2) ≥ 0.67 x C_x / (log x)²`.

Follows from `key_inequality`, `sieved_lower_bound` (Lemma 9),
`sieveOmega_le` (Lemma 8), `twinConst_pos` and `twinConst_le_chenConst`:
`2.6408 - 3.9404/2 = 0.6706` and `x^{0.91} = o(x C_x/(log x)²)`. -/
theorem chenCount_lower :
    ∀ᶠ x : ℕ in atTop, Even x →
      0.67 * (x : ℝ) * chenConst x / (Real.log x) ^ 2 ≤ (chenCount x : ℝ) := by
  filter_upwards [key_inequality, sieved_lower_bound,
      sieveOmega_le, eventually_rpow_091_le_singular_error] with
      x hkey hlower homega herror
  intro hxEven
  have hkey' := hkey hxEven
  have hlower' := hlower hxEven
  have homega' := homega hxEven
  let B : ℝ :=
    (x : ℝ) * chenConst x / (Real.log x) ^ 2
  have hOmegaHalf :
      (sieveOmega x : ℝ) / 2 ≤ 1.9702 * B := by
    dsimp only [B]
    ring_nf at homega' ⊢
    linarith
  have herror' :
      (x : ℝ) ^ (0.91 : ℝ) ≤ 0.0006 * B := by
    calc
      (x : ℝ) ^ (0.91 : ℝ) ≤
          0.0006 * (x : ℝ) * chenConst x /
            (Real.log x) ^ 2 := herror
      _ = 0.0006 * B := by
        dsimp only [B]
        ring
  dsimp only [B] at hkey' hlower' hOmegaHalf herror' ⊢
  ring_nf at hkey' hlower' hOmegaHalf herror' ⊢
  linarith

/-- **Theorem 1 (qualitative form — Chen's theorem)**: every sufficiently large
even number is the sum of a prime and a number that is either a prime or a
product of two primes. -/
theorem chen_theorem :
    ∀ᶠ x : ℕ in atTop, Even x →
      ∃ p m : ℕ, p.Prime ∧ IsP2 m ∧ p + m = x := by
  filter_upwards [chenCount_lower, eventually_gt_atTop 1] with
      x hlower hx
  intro hxEven
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hconst :
      0 < chenConst x :=
    twinConst_pos.trans_le (twinConst_le_chenConst x)
  have hmainPos :
      0 < 0.67 * (x : ℝ) * chenConst x /
        (Real.log x) ^ 2 := by positivity
  have hcountPosR : 0 < (chenCount x : ℝ) :=
    hmainPos.trans_le (hlower hxEven)
  have hcountPos : 0 < chenCount x := by
    exact_mod_cast hcountPosR
  unfold chenCount at hcountPos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcountPos
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p, x - p, hp'.2.1, hp'.2.2, ?_⟩
  have hple : p ≤ x := by
    have := Finset.mem_range.mp hp'.1
    omega
  omega

/-- **Theorem 2 (quantitative form)**: for every positive even `h` and all
sufficiently large `x`,
`x_h(1,2) ≥ 0.67 x C_h / (log x)²`.
(The singular series for the shifted problem `p + h` is `C_h`, the product
running over the odd primes dividing `h`.) -/
theorem chenCountShift_lower (h : ℕ) (hh : Even h) (h0 : 0 < h) :
    ∀ᶠ x : ℕ in atTop,
      0.67 * (x : ℝ) * chenConst h / (Real.log x) ^ 2 ≤
        (chenCountShift h x : ℝ) := by
  exact chenCountShift_lower_estimate h hh h0

theorem tendsto_chenShiftMain_atTop (h : ℕ) :
    Tendsto
      (fun x : ℕ =>
        0.67 * (x : ℝ) * chenConst h /
          (Real.log x) ^ 2)
      atTop atTop := by
  let K : ℝ := 0.67 * chenConst h
  have hconst :
      0 < chenConst h :=
    twinConst_pos.trans_le (twinConst_le_chenConst h)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hgReal :
      Tendsto (fun y : ℝ => K * y ^ (0.5 : ℝ))
        atTop atTop :=
    Tendsto.const_mul_atTop hK
      (tendsto_rpow_atTop (by norm_num))
  have hg :
      Tendsto (fun x : ℕ => K * (x : ℝ) ^ (0.5 : ℝ))
        atTop atTop :=
    hgReal.comp tendsto_natCast_atTop_atTop
  have hlogReal :
      ∀ᶠ y : ℝ in atTop,
        ‖Real.log y ^ (2 : ℝ)‖ ≤
          ‖y ^ (0.5 : ℝ)‖ :=
    (isLittleO_log_rpow_rpow_atTop
      (2 : ℝ) (by norm_num : (0 : ℝ) < 0.5)).eventuallyLE
  have hlogNat :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  have hbound :
      ∀ᶠ x : ℕ in atTop,
        K * (x : ℝ) ^ (0.5 : ℝ) ≤
          0.67 * (x : ℝ) * chenConst h /
            (Real.log x) ^ 2 := by
    filter_upwards [hlogNat, eventually_gt_atTop 1] with
        x hlog hx
    have hxpos : (0 : ℝ) < x := by positivity
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx)
    have hlogsq :
        (Real.log x) ^ 2 ≤ (x : ℝ) ^ (0.5 : ℝ) := by
      simpa [Real.rpow_natCast,
        Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le _),
        Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hlog
    have hhalf :
        (x : ℝ) ^ (0.5 : ℝ) *
            (x : ℝ) ^ (0.5 : ℝ) = x := by
      rw [← Real.rpow_add hxpos]
      norm_num
    apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).2
    calc
      K * (x : ℝ) ^ (0.5 : ℝ) *
          (Real.log x) ^ 2 ≤
        K * (x : ℝ) ^ (0.5 : ℝ) *
          (x : ℝ) ^ (0.5 : ℝ) := by gcongr
      _ = K * (x : ℝ) := by rw [mul_assoc, hhalf]
      _ = 0.67 * (x : ℝ) * chenConst h := by
        dsimp only [K]
        ring
  exact tendsto_atTop_mono' atTop hbound hg

/-- **Theorem 2 (qualitative form)**: for every positive even `h` there are
infinitely many primes `p` such that `p + h` has at most two prime factors.
For `h = 2` this is the celebrated approximation to the twin prime conjecture. -/
theorem chen_twin (h : ℕ) (hh : Even h) (h0 : 0 < h) :
    {p : ℕ | p.Prime ∧ IsP2 (p + h)}.Infinite := by
  let S : Set ℕ := {p : ℕ | p.Prime ∧ IsP2 (p + h)}
  change S.Infinite
  by_contra hInf
  have hfin : S.Finite := by
    rcases Set.finite_or_infinite S with hfin | hinfinite
    · exact hfin
    · exact (hInf hinfinite).elim
  let N : ℕ := hfin.toFinset.card
  have hg := tendsto_chenShiftMain_atTop h
  have hlarge :
      ∀ᶠ x : ℕ in atTop,
        (N : ℝ) <
          0.67 * (x : ℝ) * chenConst h /
            (Real.log x) ^ 2 :=
    hg.eventually (eventually_gt_atTop (N : ℝ))
  obtain ⟨x, hlower, hlarge⟩ :=
    ((chenCountShift_lower h hh h0).and hlarge).exists
  have hcountGtR :
      (N : ℝ) < (chenCountShift h x : ℝ) :=
    hlarge.trans_le hlower
  have hcountGt : N < chenCountShift h x := by
    exact_mod_cast hcountGtR
  have hsubset :
      (Finset.range (x + 1)).filter
          (fun p => p.Prime ∧ IsP2 (p + h)) ⊆
        hfin.toFinset := by
    intro p hp
    rw [Set.Finite.mem_toFinset]
    exact (Finset.mem_filter.mp hp).2
  have hcard :=
    Finset.card_le_card hsubset
  change chenCountShift h x ≤ N at hcard
  omega

end Chen
