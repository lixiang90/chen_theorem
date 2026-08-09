/-
# The squarefree exceptional weight in equation (18)

Chen absorbs `3 ^ ν(d)` into the dyadic factor `I_{l,x}`.  The key estimate
is obtained here without a prime number theorem: ordering the distinct prime
factors gives `ν(d)! ≤ d`, and Stirling's lower bound then gives the stronger
eventual estimate `ν(d) ≤ 2 log d / log log d`.
-/
import ChenTheorem.Lemma6.Coefficients
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Data.Finset.Sort

open scoped Classical

namespace Chen

/-- The product of `k` distinct positive natural numbers is at least `k!`. -/
theorem factorial_card_le_prod_of_pos (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) : Nat.factorial s.card ≤ ∏ n ∈ s, n := by
  let e : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hepos (i : Fin s.card) : 1 ≤ e i :=
    hs (e i) (s.orderEmbOfFin_mem rfl i)
  have hei (i : Fin s.card) : i.1 + 1 ≤ e i := by
    have hindex : ∀ n, (hn : n < s.card) →
        n + 1 ≤ e ⟨n, hn⟩ := by
      intro n
      induction n with
      | zero =>
          intro hn
          simpa using hepos ⟨0, hn⟩
      | succ n ih =>
          intro hn
          have hn' : n < s.card := (Nat.lt_succ_self n).trans hn
          have hprev := ih hn'
          have hlt : e ⟨n, hn'⟩ < e ⟨n + 1, hn⟩ :=
            e.strictMono (by simp)
          omega
    exact hindex i.1 i.2
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, e i := by
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hei i)
  calc
    Nat.factorial s.card = ∏ i ∈ Finset.range s.card, (i + 1) :=
      Finset.prod_range_add_one_eq_factorial _ |>.symm
    _ = ∏ i : Fin s.card, (i.1 + 1) :=
      (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card).symm
    _ ≤ ∏ i : Fin s.card, e i := hprod
    _ = ∏ n ∈ s, n := by
      calc
        ∏ i : Fin s.card, e i = ∏ n : s, n.1 :=
          Fintype.prod_equiv (s.orderIsoOfFin rfl).toEquiv
            (fun i : Fin s.card => e i) (fun n : s => n.1) (fun _ => rfl)
        _ = ∏ n ∈ s, n := by
          rw [← s.attach_eq_univ]
          exact Finset.prod_attach s (fun n : ℕ => n)

/-- For squarefree `d`, the factorial of the number of prime factors is at
most `d`. -/
theorem factorial_primeFactors_card_le {d : ℕ} (hd : Squarefree d) :
    Nat.factorial d.primeFactors.card ≤ d := by
  calc
    Nat.factorial d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p :=
      factorial_card_le_prod_of_pos d.primeFactors
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le)
    _ = d := Nat.prod_primeFactors_of_squarefree hd

/-- A concrete large-`d` form of the standard estimate
`ν(d) ≪ log d / log log d`.  The constant `2` is stronger than needed for
equation (18). -/
theorem primeFactors_card_le_two_log_div_loglog
    {d : ℕ} (hd : Squarefree d) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    (d.primeFactors.card : ℝ) ≤
      2 * Real.log d / Real.log (Real.log d) := by
  let k : ℕ := d.primeFactors.card
  let t : ℝ := Real.log d
  let u : ℝ := Real.log t
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have ht : 0 < t := by
    dsimp only [t]
    exact Real.log_pos hdR
  have hu : 0 < u := by dsimp only [u, t]; linarith
  have hk : k ≠ 0 := by
    dsimp only [k]
    rw [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    intro hempty
    have := Nat.primeFactors_eq_empty.mp hempty
    omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hfacNat : Nat.factorial k ≤ d := by
    simpa only [k] using factorial_primeFactors_card_le hd
  have hlogfac : Real.log (Nat.factorial k : ℝ) ≤ t := by
    dsimp only [t]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hfacNat)
  have hstirling := Stirling.le_log_factorial_stirling hk
  have hbase : (k : ℝ) * (Real.log k - 1) ≤ t := by
    calc
      (k : ℝ) * (Real.log k - 1) ≤
          (k : ℝ) * Real.log k - k + Real.log k / 2 +
            Real.log (2 * Real.pi) / 2 := by
        have hlogk : 0 ≤ Real.log (k : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk))
        have hlogpi : 0 ≤ Real.log (2 * Real.pi) :=
          Real.log_nonneg (by nlinarith [Real.pi_gt_three])
        linarith
      _ ≤ Real.log (Nat.factorial k : ℝ) := hstirling
      _ ≤ t := hlogfac
  by_contra hbound
  have hkgt : 2 * t / u < (k : ℝ) := lt_of_not_ge hbound
  have hqpos : 0 < 2 * t / u := div_pos (by positivity) hu
  have hlogu : Real.log u ≤ u / 2 - 1 + Real.log 2 := by
    calc
      Real.log u = Real.log (u / 2) + Real.log 2 := by
        rw [← Real.log_mul (by positivity) (by norm_num)]
        congr 1
        field_simp
      _ ≤ (u / 2 - 1) + Real.log 2 := by
        gcongr
        exact Real.log_le_sub_one_of_pos (by positivity)
  have hlogq : u / 2 + 1 ≤ Real.log (2 * t / u) := by
    have heq : Real.log (2 * t / u) = Real.log 2 + u - Real.log u := by
      rw [Real.log_div (by positivity) hu.ne', Real.log_mul (by norm_num) ht.ne']
    rw [heq]
    linarith
  have hloglt : Real.log (2 * t / u) < Real.log (k : ℝ) :=
    Real.strictMonoOn_log hqpos hkR hkgt
  have hku : t < (k : ℝ) * (u / 2) := by
    have := (div_lt_iff₀ hu).mp hkgt
    nlinarith
  have hprod : t < (k : ℝ) * (Real.log k - 1) := by
    have hloglarge : u / 2 < Real.log (k : ℝ) - 1 := by linarith
    nlinarith
  linarith

/-- The prime-factor exponential bound underlying equation (18). -/
theorem three_pow_primeFactors_card_le_exp
    {d : ℕ} (hd : Squarefree d) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    (3 : ℝ) ^ d.primeFactors.card ≤
      Real.exp (3 * Real.log d / Real.log (Real.log d)) := by
  have hcard := primeFactors_card_le_two_log_div_loglog hd hd2 hu1
  have ht : 0 < Real.log (d : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hu : 0 < Real.log (Real.log (d : ℝ)) := by linarith
  have hlog3 : Real.log 3 ≤ (3 : ℝ) / 2 := by
    linarith [Real.log_three_lt_d9]
  have hexponent :
      (d.primeFactors.card : ℝ) * Real.log 3 ≤
        3 * Real.log d / Real.log (Real.log d) := by
    calc
      (d.primeFactors.card : ℝ) * Real.log 3 ≤
          (2 * Real.log d / Real.log (Real.log d)) * ((3 : ℝ) / 2) :=
        mul_le_mul hcard hlog3 (Real.log_nonneg (by norm_num))
          (div_nonneg (by positivity) hu.le)
      _ = 3 * Real.log d / Real.log (Real.log d) := by ring
  calc
    (3 : ℝ) ^ d.primeFactors.card =
        Real.exp (Real.log ((3 : ℝ) ^ d.primeFactors.card)) :=
      (Real.exp_log (by positivity)).symm
    _ = Real.exp ((d.primeFactors.card : ℝ) * Real.log 3) := by
      rw [Real.log_pow]
    _ ≤ Real.exp (3 * Real.log d / Real.log (Real.log d)) :=
      Real.exp_le_exp.mpr hexponent

/-- Equation (18), stated with the paper's hypothesis `μ(d) ≠ 0`. -/
theorem lemma6_equation18
    {d : ℕ} (hμ : ArithmeticFunction.moebius d ≠ 0) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    (3 : ℝ) ^ distinctPrimeFactors d ≤
      Real.exp (3 * Real.log d / Real.log (Real.log d)) := by
  have hd : Squarefree d :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
  simpa only [distinctPrimeFactors] using
    three_pow_primeFactors_card_le_exp hd hd2 hu1

/-- Squared form of equation (18), ready for the weighted Cauchy and Hölder
inequalities used in (19). -/
theorem lemma6_equation18_sq
    {d : ℕ} (hμ : ArithmeticFunction.moebius d ≠ 0) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
      Real.exp (6 * Real.log d / Real.log (Real.log d)) := by
  have h := lemma6_equation18 hμ hd2 hu1
  calc
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
        (Real.exp (3 * Real.log d / Real.log (Real.log d))) ^ 2 := by
      gcongr
    _ = Real.exp (6 * Real.log d / Real.log (Real.log d)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- The explicit largeness condition in equation (18) is eventually
satisfied by every natural number. -/
theorem eventually_one_lt_log_log_nat :
    ∀ᶠ d : ℕ in Filter.atTop, 1 < Real.log (Real.log (d : ℝ)) := by
  have hreal : Filter.Tendsto (fun y : ℝ => Real.log (Real.log y))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  exact tendsto_natCast_atTop_atTop.eventually
    (hreal.eventually (Filter.eventually_gt_atTop 1))

/-- The increasing exponent `log Q / log log Q` in Chen's factor
`I_{l,x}`. -/
noncomputable def logLogRatio (y : ℝ) : ℝ :=
  Real.log y / Real.log (Real.log y)

theorem one_le_log_log_of_exp_exp_le {y : ℝ}
    (hy : Real.exp (Real.exp 1) ≤ y) :
    1 ≤ Real.log (Real.log y) := by
  have hypos : 0 < y := (by positivity : 0 < Real.exp (Real.exp 1)).trans_le hy
  have hlog : Real.exp 1 ≤ Real.log y := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ ≤ Real.log y := Real.log_le_log (by positivity) hy
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (Real.log y) := Real.log_le_log (by positivity) hlog

theorem one_lt_log_log_of_exp_exp_lt {y : ℝ}
    (hy : Real.exp (Real.exp 1) < y) :
    1 < Real.log (Real.log y) := by
  have hlog : Real.exp 1 < Real.log y := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ < Real.log y := Real.strictMonoOn_log (Real.exp_pos _)
        ((Real.exp_pos _).trans hy) hy
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log (Real.log y) := Real.strictMonoOn_log (Real.exp_pos 1)
      ((Real.exp_pos 1).trans hlog) hlog

theorem hasDerivAt_logLogRatio {y : ℝ}
    (hy : Real.exp (Real.exp 1) ≤ y) :
    HasDerivAt logLogRatio
      ((Real.log (Real.log y) - 1) /
        (y * (Real.log (Real.log y)) ^ 2)) y := by
  have hEpos : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have hypos : 0 < y := hEpos.trans_le hy
  have hy0 : y ≠ 0 := hypos.ne'
  have hy1 : y ≠ 1 := by
    have : (1 : ℝ) < Real.exp (Real.exp 1) :=
      Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
    linarith
  have hyneg1 : y ≠ -1 := by linarith
  have hloglogpos : 0 < Real.log (Real.log y) := by
    have := one_le_log_log_of_exp_exp_le hy
    linarith
  have hden : Real.log (Real.log y) ≠ 0 := hloglogpos.ne'
  have hlogyne : Real.log y ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hypos hy1
  unfold logLogRatio
  have hraw := (Real.hasDerivAt_log hy0).div
    (Real.hasDerivAt_log_log hy0 hy1 hyneg1) hden
  convert hraw using 1 <;> try {rfl}
  field_simp [hlogyne]

/-- `log Q / log log Q` is increasing once `Q ≥ exp(exp 1)`. -/
theorem monotoneOn_logLogRatio :
    MonotoneOn logLogRatio (Set.Ici (Real.exp (Real.exp 1))) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro y hy
    exact (hasDerivAt_logLogRatio hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    exact (hasDerivAt_logLogRatio hy.le).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    rw [(hasDerivAt_logLogRatio hy.le).deriv]
    have hloglog := one_le_log_log_of_exp_exp_le hy.le
    have hypos : 0 < y := (Real.exp_pos _).trans_le hy.le
    exact div_nonneg (sub_nonneg.mpr hloglog)
      (mul_nonneg hypos.le (sq_nonneg _))

/-- Chen's exceptional-factor envelope, written as a function of the
upper dyadic modulus endpoint `Q`. -/
noncomputable def lemma6ExceptionalFactor (Q : ℝ) : ℝ :=
  Real.exp (6 * logLogRatio Q)

theorem lemma6ExceptionalFactor_pos (Q : ℝ) :
    0 < lemma6ExceptionalFactor Q := by
  unfold lemma6ExceptionalFactor
  positivity

/-- Equation (18), squared and enlarged from `d` to a dyadic endpoint `Q`.
This is exactly the pointwise hypothesis consumed by the weighted
Cauchy--Hölder lemmas. -/
theorem lemma6_equation18_sq_le_exceptionalFactor
    {d : ℕ} (hμ : ArithmeticFunction.moebius d ≠ 0) (hd2 : 2 ≤ d)
    (hdlarge : Real.exp (Real.exp 1) < (d : ℝ))
    {Q : ℝ} (hdQ : (d : ℝ) ≤ Q) :
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
      lemma6ExceptionalFactor Q := by
  have hu1 := one_lt_log_log_of_exp_exp_lt hdlarge
  have hraw := lemma6_equation18_sq hμ hd2 hu1
  have hratio : logLogRatio (d : ℝ) ≤ logLogRatio Q :=
    monotoneOn_logLogRatio hdlarge.le (hdlarge.le.trans hdQ) hdQ
  calc
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
        Real.exp (6 * Real.log d / Real.log (Real.log d)) := hraw
    _ = Real.exp (6 * logLogRatio (d : ℝ)) := by
      unfold logLogRatio
      congr 1
      ring
    _ ≤ Real.exp (6 * logLogRatio Q) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hratio (by norm_num))
    _ = lemma6ExceptionalFactor Q := rfl

end Chen
