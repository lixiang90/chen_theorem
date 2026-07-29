import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Finset Real Filter
open scoped Nat.Prime Classical

namespace Chen

noncomputable def primeIndicator (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

theorem sum_primeIndicator_eq_primeCounting (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, primeIndicator k =
      (n.primeCounting : ℝ) := by
  have hset :
      (Finset.Icc 0 n).filter Nat.Prime = n.primesLE := by
    ext k
    simp [Nat.primesLE, Nat.primesBelow]
  rw [← Nat.primesLE_card_eq_primeCounting, ← hset]
  simp [primeIndicator]

theorem sum_inv_primeIndicator_eq_sum_primesLE (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, (k : ℝ)⁻¹ * primeIndicator k =
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ := by
  have hset :
      (Finset.Icc 0 n).filter Nat.Prime = n.primesLE := by
    ext k
    simp [Nat.primesLE, Nat.primesBelow]
  rw [← hset]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : k.Prime <;> simp [primeIndicator, hp]

theorem sum_inv_primesLE_eq (n : ℕ) :
    ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ =
      (n.primeCounting : ℝ) / n +
        ∫ t in Set.Ioc (2 : ℝ) n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 := by
  have hab :=
    sum_mul_eq_sub_integral_mul₁
      primeIndicator (f := fun t : ℝ => t⁻¹)
      (by simp [primeIndicator, Nat.not_prime_zero])
      (by simp [primeIndicator, Nat.not_prime_one]) n
      (by
        intro t ht
        exact differentiableAt_inv (by linarith [ht.1]))
      (by
        rw [deriv_inv']
        apply ContinuousOn.integrableOn_Icc
        exact (continuousOn_id.pow 2).inv₀
          (fun t ht => pow_ne_zero 2 (by
            simpa only [id_eq] using
              (show t ≠ 0 by linarith [ht.1]))) |>.neg)
  rw [sum_inv_primeIndicator_eq_sum_primesLE,
    sum_primeIndicator_eq_primeCounting, deriv_inv'] at hab
  simp_rw [sum_primeIndicator_eq_primeCounting] at hab
  simp only [neg_mul] at hab
  rw [MeasureTheory.integral_neg] at hab
  simpa [div_eq_mul_inv, mul_comm] using hab

theorem primeCounting_le_log_term_add_sqrt
    {t : ℝ} (ht : 2 ≤ t) :
    (⌊t⌋₊.primeCounting : ℝ) ≤
      2 * Real.log 4 * t / Real.log t + Real.sqrt t := by
  have h := Chebyshev.pi_le_log4_mul_div (lt_of_lt_of_le (by norm_num) ht)
  rw [Real.log_sqrt (by positivity : 0 ≤ t)] at h
  have hlog : Real.log t ≠ 0 :=
    ne_of_gt (Real.log_pos (lt_of_lt_of_le (by norm_num) ht))
  calc
    (⌊t⌋₊.primeCounting : ℝ) ≤
        Real.log 4 * t / (Real.log t / 2) + Real.sqrt t := h
    _ = 2 * Real.log 4 * t / Real.log t + Real.sqrt t := by
      field_simp

theorem primeCounting_div_sq_le
    {t : ℝ} (ht : 2 ≤ t) :
    (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 ≤
      2 * Real.log 4 / (t * Real.log t) +
        t ^ (-(3 : ℝ) / 2) := by
  have hpi := primeCounting_le_log_term_add_sqrt ht
  have htpos : 0 < t := by linarith
  have hsq : 0 < t ^ 2 := by positivity
  calc
    (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 ≤
        (2 * Real.log 4 * t / Real.log t +
          Real.sqrt t) / t ^ 2 :=
      (div_le_div_iff_of_pos_right hsq).2 hpi
    _ = 2 * Real.log 4 / (t * Real.log t) +
        t ^ (-(3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      rw [add_div]
      congr 1
      · field_simp
      rw [div_eq_mul_inv, ← Real.rpow_natCast]
      change t ^ ((1 : ℝ) / 2) * (t ^ (2 : ℝ))⁻¹ =
        t ^ (-(3 : ℝ) / 2)
      rw [← Real.rpow_neg (le_of_lt htpos) (2 : ℝ),
        ← Real.rpow_add htpos]
      congr 1
      norm_num

theorem integral_one_div_mul_log (n : ℝ) (hn : 2 ≤ n) :
    ∫ t in (2 : ℝ)..n, 1 / (t * Real.log t) =
      Real.log (Real.log n) - Real.log (Real.log 2) := by
  let F : ℝ → ℝ := fun t => Real.log (Real.log t)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have ht2 : 2 ≤ t := by
      rw [Set.uIcc_of_le hn] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog0 : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith))
    have h := (Real.hasDerivAt_log ht0).log hlog0
    simpa only [one_div, mul_inv, div_eq_mul_inv, mul_comm,
      one_mul] using h
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hn]
    have hlogcont :
        ContinuousOn Real.log (Set.Icc (2 : ℝ) n) :=
      Real.continuousOn_log.mono (by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [ht.1])
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_id :
          ContinuousOn (fun x : ℝ => x) (Set.Icc 2 n)).mul
        hlogcont)
    intro t ht
    exact mul_ne_zero (by
      simpa only [id_eq] using
        (show t ≠ 0 by linarith [ht.1]))
      (ne_of_gt (Real.log_pos (by linarith [ht.1])))

theorem integral_rpow_neg_three_halves_le_two
    (n : ℝ) (hn : 2 ≤ n) :
    ∫ t in (2 : ℝ)..n, t ^ (-(3 : ℝ) / 2) ≤ 2 := by
  rw [integral_rpow]
  · have hnnonneg :
        0 ≤ n ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    have htwo :
        (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    norm_num
    linarith
  · right
    constructor
    · norm_num
    · rw [Set.uIcc_of_le hn]
      intro hzero
      have hmem := hzero
      simp only [Set.mem_Icc] at hmem
      norm_num at hmem

theorem primeCounting_div_nat_le_one
    (n : ℕ) (hn : 1 ≤ n) :
    (n.primeCounting : ℝ) / n ≤ 1 := by
  have hcard : n.primeCounting ≤ n := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    have hsub : n.primesLE ⊆ Finset.Icc 1 n := by
      intro p hp
      have hp' := Nat.prime_of_mem_primesLE hp
      exact Finset.mem_Icc.mpr ⟨hp'.one_le, Nat.le_of_mem_primesLE hp⟩
    have hc := Finset.card_le_card hsub
    simpa [Nat.card_Icc, hn] using hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [div_le_one hnR]
  exact_mod_cast hcard

theorem sum_inv_primesLE_le_log_log (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
      1 + 2 * Real.log 4 *
        (Real.log (Real.log n) - Real.log (Real.log 2)) + 2 := by
  rw [sum_inv_primesLE_eq]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hleftOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2)
        (Set.Icc 2 (n : ℝ)) := by
    have hg :
        MeasureTheory.IntegrableOn
          (fun t : ℝ => (t ^ 2)⁻¹)
          (Set.Icc 2 (n : ℝ)) := by
      apply ContinuousOn.integrableOn_Icc
      exact (continuousOn_id.pow 2).inv₀ (by
        intro t ht
        exact pow_ne_zero 2 (by
          simpa only [id_eq] using
            (show t ≠ 0 by linarith [ht.1])))
    have hi :=
      integrableOn_mul_sum_Icc
        (c := primeIndicator) (m := 0)
        (a := (2 : ℝ)) (b := (n : ℝ))
        (by norm_num) hg
    simp_rw [sum_primeIndicator_eq_primeCounting] at hi
    simpa only [div_eq_mul_inv, mul_comm] using hi
  have hlogTermOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          2 * Real.log 4 / (t * Real.log t))
        (Set.Icc 2 (n : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    have hlogcont :
        ContinuousOn Real.log (Set.Icc (2 : ℝ) n) :=
      Real.continuousOn_log.mono (by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [ht.1])
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_id :
          ContinuousOn (fun x : ℝ => x) (Set.Icc 2 n)).mul
        hlogcont)
    intro t ht
    exact mul_ne_zero (by
      simpa only [id_eq] using
        (show t ≠ 0 by linarith [ht.1]))
      (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  have hrpowOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => t ^ (-(3 : ℝ) / 2))
        (Set.Icc 2 (n : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t
      (-(3 : ℝ) / 2) (.inl (by linarith [ht.1]))).continuousWithinAt
  have hrightOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          2 * Real.log 4 / (t * Real.log t) +
            t ^ (-(3 : ℝ) / 2))
        (Set.Icc 2 (n : ℝ)) :=
    hlogTermOn.add hrpowOn
  have hleftInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hleftOn
  have hlogTermInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hlogTermOn
  have hrpowInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hrpowOn
  have hrightInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hrightOn
  have hinter :
      (∫ t in (2 : ℝ)..n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2) ≤
        ∫ t in (2 : ℝ)..n,
          (2 * Real.log 4 / (t * Real.log t) +
            t ^ (-(3 : ℝ) / 2)) := by
    apply intervalIntegral.integral_mono_on hnR
      hleftInt hrightInt
    intro t ht
    exact primeCounting_div_sq_le ht.1
  have hrpow :=
    integral_rpow_neg_three_halves_le_two (n : ℝ) hnR
  have hlogint := integral_one_div_mul_log (n : ℝ) hnR
  rw [intervalIntegral.integral_add hlogTermInt hrpowInt,
    show (fun t : ℝ => 2 * Real.log 4 / (t * Real.log t)) =
      fun t : ℝ => (2 * Real.log 4) * (1 / (t * Real.log t)) by
        funext t
        ring,
    intervalIntegral.integral_const_mul, hlogint] at hinter
  calc
    (n.primeCounting : ℝ) / n +
        ∫ t in Set.Ioc (2 : ℝ) n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 ≤
      1 + ∫ t in Set.Ioc (2 : ℝ) n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 := by
        gcongr
        exact primeCounting_div_nat_le_one n (by omega)
    _ = 1 + ∫ t in (2 : ℝ)..n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 := by
      rw [intervalIntegral.integral_of_le hnR]
    _ ≤ 1 + (2 * Real.log 4 *
          (Real.log (Real.log n) - Real.log (Real.log 2)) +
        ∫ t in (2 : ℝ)..n, t ^ (-(3 : ℝ) / 2)) := by
      gcongr
    _ ≤ 1 + 2 * Real.log 4 *
          (Real.log (Real.log n) - Real.log (Real.log 2)) + 2 := by
      linarith

/-- The square of the prime harmonic sum grows more slowly than any
fixed positive power of `log n`.  The exponent `1/25` leaves the
specific margin needed by the short-interval sieve in Lemma 5. -/
theorem eventually_sum_inv_primesLE_sq_le_log_rpow :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
        (Real.log n) ^ ((1 : ℝ) / 25) := by
  let A : ℝ := 2 * Real.log 4
  let B : ℝ := 3 - A * Real.log (Real.log 2)
  let C : ℝ := A + B
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hB : 0 < B := by
    dsimp only [B, A]
    have hloglog2 : Real.log (Real.log 2) < 0 := by
      rw [Real.log_neg_iff (Real.log_pos (by norm_num))]
      have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ))
        (by norm_num) (by norm_num)
      norm_num at h
      exact h
    nlinarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hlogNat :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog :
      ∀ᶠ n : ℕ in atTop,
        Real.log (Real.log n) ≤
          (Real.log n) ^ ((1 : ℝ) / 100) := by
    have hδ : (0 : ℝ) < (1 : ℝ) / 100 := by norm_num
    have hreal :
        ∀ᶠ y : ℝ in atTop,
          ‖Real.log y ^ (1 : ℝ)‖ ≤
            ‖y ^ ((1 : ℝ) / 100)‖ :=
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hδ).eventuallyLE
    have hnat := hlogNat.eventually hreal
    filter_upwards [hnat, hlogNat.eventually (eventually_gt_atTop 1)]
        with n hn hL
    have hlogL : 0 < Real.log (Real.log n) :=
      Real.log_pos hL
    have hLpos : 0 < Real.log (n : ℝ) :=
      zero_lt_one.trans hL
    simpa [Real.rpow_one, Real.norm_of_nonneg hlogL.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le _)] using hn
  have hconstant :
      ∀ᶠ n : ℕ in atTop,
        C ^ 2 ≤ (Real.log n) ^ ((1 : ℝ) / 50) := by
    have hrpow :
        Tendsto (fun y : ℝ => y ^ ((1 : ℝ) / 50)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    exact hlogNat.eventually
      (hrpow.eventually (eventually_ge_atTop (C ^ 2)))
  filter_upwards [eventually_ge_atTop 2, hloglog, hconstant,
      hlogNat.eventually (eventually_ge_atTop (Real.exp 1))] with
      n hn hloglog hconstant hL
  have hsum := sum_inv_primesLE_le_log_log n hn
  have hloglogOne : 1 ≤ Real.log (Real.log n) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.log n) :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (Real.exp_pos 1))
          (Set.mem_Ioi.mpr ((Real.exp_pos 1).trans_le hL)) hL
  have hsumNonneg :
      0 ≤ ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ := by positivity
  have hsumC :
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
        C * Real.log (Real.log n) := by
    calc
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
          A * Real.log (Real.log n) + B := by
        dsimp only [A, B]
        nlinarith [hsum]
      _ ≤ (A + B) * Real.log (Real.log n) := by
        nlinarith
      _ = C * Real.log (Real.log n) := by rfl
  have hLpos : 0 < Real.log (n : ℝ) :=
    (Real.exp_pos 1).trans_le hL
  have hsumPower :
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
        C * (Real.log n) ^ ((1 : ℝ) / 100) :=
    hsumC.trans
      (mul_le_mul_of_nonneg_left hloglog hC.le)
  have hsquare :
      (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
        C ^ 2 * ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := by
    calc
      (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
          (C * (Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 :=
        pow_le_pow_left₀ hsumNonneg hsumPower 2
      _ = C ^ 2 * ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := by
        ring
  calc
    (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
        C ^ 2 * ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := hsquare
    _ ≤ (Real.log n) ^ ((1 : ℝ) / 50) *
          ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := by
      gcongr
    _ = (Real.log n) ^ ((1 : ℝ) / 25) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul hLpos.le,
        ← Real.rpow_add hLpos]
      congr 1
      norm_num

end Chen
