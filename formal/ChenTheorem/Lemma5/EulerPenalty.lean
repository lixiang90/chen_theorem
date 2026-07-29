import ChenTheorem.Lemma5.PrimeReciprocals

/-! Uniform control of the Euler-factor penalty caused by primes dividing `x`. -/

open Finset Real Filter
open scoped Nat.Prime Classical

namespace Chen

noncomputable def primeFactorEulerPenalty (x : ℕ) : ℝ :=
  ∏ p ∈ x.primeFactors, (1 + (p : ℝ)⁻¹)

noncomputable def primeFactorSplitLevel (x : ℕ) : ℕ :=
  ⌊Real.log x⌋₊

theorem two_pow_primeFactors_card_le {x : ℕ} (hx : 1 ≤ x) :
    2 ^ x.primeFactors.card ≤ x := by
  calc
    2 ^ x.primeFactors.card =
        ∏ p ∈ x.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ x.primeFactors, p := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ x := by
      exact Nat.le_of_dvd (Nat.zero_lt_of_lt hx)
        (Nat.prod_primeFactors_dvd x)

theorem primeFactors_card_mul_log_two_le_log
    {x : ℕ} (hx : 1 ≤ x) :
    (x.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log x := by
  have hpow := two_pow_primeFactors_card_le hx
  have hpowR :
      (2 : ℝ) ^ x.primeFactors.card ≤ (x : ℝ) := by
    exact_mod_cast hpow
  have hposLeft : 0 < (2 : ℝ) ^ x.primeFactors.card := by positivity
  have hposRight : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hposLeft) (Set.mem_Ioi.mpr hposRight) hpowR
  simpa [Real.log_pow] using hlog

theorem primeFactorEulerPenalty_le_exp_sum (x : ℕ) :
    primeFactorEulerPenalty x ≤
      Real.exp (∑ p ∈ x.primeFactors, (p : ℝ)⁻¹) := by
  exact Real.prod_one_add_le_exp_sum x.primeFactors
    (fun p => by positivity)

theorem small_primeFactor_inv_sum_le
    {x Y : ℕ} :
    ∑ p ∈ x.primeFactors.filter (fun p => p ≤ Y), (p : ℝ)⁻¹ ≤
      ∑ p ∈ Y.primesLE, (p : ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr
      ⟨hp'.2, Nat.prime_of_mem_primeFactors hp'.1⟩
  · intro p hpY hpx
    positivity

theorem large_primeFactor_inv_sum_le
    {x Y : ℕ} (hY : 1 ≤ Y) :
    ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
      (x.primeFactors.card : ℝ) / Y := by
  calc
    ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
        ∑ _p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y),
          (Y : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpY : Y ≤ p := by
        have hpnot := (Finset.mem_filter.mp hp).2
        omega
      have hpPrime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      exact (inv_le_inv₀
        (by exact_mod_cast hpPrime.pos : (0 : ℝ) < p)
        (by exact_mod_cast (Nat.zero_lt_of_lt hY))).2
          (by exact_mod_cast hpY)
    _ = ((x.primeFactors.filter (fun p => ¬ p ≤ Y)).card : ℝ) /
        Y := by
      simp [div_eq_mul_inv]
    _ ≤ (x.primeFactors.card : ℝ) / Y := by
      rw [div_le_div_iff_of_pos_right
        (by exact_mod_cast (Nat.zero_lt_of_lt hY) : (0 : ℝ) < Y)]
      exact_mod_cast Finset.card_filter_le
        x.primeFactors (fun p => ¬ p ≤ Y)

theorem primeFactor_inv_sum_split (x Y : ℕ) :
    ∑ p ∈ x.primeFactors, (p : ℝ)⁻¹ =
      (∑ p ∈ x.primeFactors.filter (fun p => p ≤ Y), (p : ℝ)⁻¹) +
      ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ := by
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := x.primeFactors) (p := fun p => p ≤ Y)
      (f := fun p => (p : ℝ)⁻¹)).symm

theorem splitLevel_two_le
    {x : ℕ} (hxlog : 2 ≤ Real.log x) :
    2 ≤ primeFactorSplitLevel x := by
  unfold primeFactorSplitLevel
  exact Nat.le_floor hxlog

theorem splitLevel_cast_le_log (x : ℕ) :
    (primeFactorSplitLevel x : ℝ) ≤ Real.log x := by
  unfold primeFactorSplitLevel
  cases x with
  | zero => simp
  | succ x =>
      exact Nat.floor_le (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero x))))

theorem log_half_le_splitLevel_cast
    {x : ℕ} (hxlog : 2 ≤ Real.log x) :
    Real.log x / 2 ≤ (primeFactorSplitLevel x : ℝ) := by
  have hfloor :
      Real.log x < (primeFactorSplitLevel x : ℝ) + 1 := by
    unfold primeFactorSplitLevel
    exact_mod_cast Nat.lt_floor_add_one (Real.log x)
  linarith

theorem large_primeFactor_inv_sum_le_const
    {x : ℕ} (hx : 1 ≤ x) (hxlog : 2 ≤ Real.log x) :
    ∑ p ∈ x.primeFactors.filter
        (fun p => ¬ p ≤ primeFactorSplitLevel x), (p : ℝ)⁻¹ ≤
      2 / Real.log 2 := by
  let Y := primeFactorSplitLevel x
  have hY : 1 ≤ Y := (splitLevel_two_le hxlog).trans' (by omega)
  have hlarge :=
    large_primeFactor_inv_sum_le (x := x) (Y := Y) hY
  have hcard :=
    primeFactors_card_mul_log_two_le_log hx
  have hhalf :
      Real.log x / 2 ≤ (Y : ℝ) :=
    log_half_le_splitLevel_cast hxlog
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
        (x.primeFactors.card : ℝ) / Y := hlarge
    _ ≤ 2 / Real.log 2 := by
      rw [div_le_div_iff₀ hYpos hlog2]
      nlinarith

theorem primeFactor_inv_sum_le_explicit
    {x : ℕ} (hx : 1 ≤ x) (hxlog : 2 ≤ Real.log x) :
    ∑ p ∈ x.primeFactors, (p : ℝ)⁻¹ ≤
      1 + 2 * Real.log 4 *
          (Real.log (Real.log (primeFactorSplitLevel x)) -
            Real.log (Real.log 2)) +
        2 + 2 / Real.log 2 := by
  let Y := primeFactorSplitLevel x
  have hY : 2 ≤ Y := splitLevel_two_le hxlog
  rw [primeFactor_inv_sum_split x Y]
  calc
    (∑ p ∈ x.primeFactors.filter (fun p => p ≤ Y), (p : ℝ)⁻¹) +
        ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
      (∑ p ∈ Y.primesLE, (p : ℝ)⁻¹) +
        2 / Real.log 2 := by
      exact add_le_add small_primeFactor_inv_sum_le
        (large_primeFactor_inv_sum_le_const hx hxlog)
    _ ≤ (1 + 2 * Real.log 4 *
          (Real.log (Real.log Y) - Real.log (Real.log 2)) + 2) +
        2 / Real.log 2 := by
      gcongr
      exact sum_inv_primesLE_le_log_log Y hY
    _ = 1 + 2 * Real.log 4 *
          (Real.log (Real.log (primeFactorSplitLevel x)) -
            Real.log (Real.log 2)) +
        2 + 2 / Real.log 2 := by rfl

noncomputable def primeFactorPenaltyConstant : ℝ :=
  Real.exp
    (3 + 2 / Real.log 2 -
      2 * Real.log 4 * Real.log (Real.log 2))

theorem primeFactorPenaltyConstant_pos :
    0 < primeFactorPenaltyConstant := by
  unfold primeFactorPenaltyConstant
  positivity

theorem primeFactorEulerPenalty_le_log_splitLevel_rpow
    {x : ℕ} (hx : 1 ≤ x) (hxlog : 2 ≤ Real.log x) :
    primeFactorEulerPenalty x ≤
      primeFactorPenaltyConstant *
        (Real.log (primeFactorSplitLevel x)) ^
          (2 * Real.log 4) := by
  have hsum := primeFactor_inv_sum_le_explicit hx hxlog
  have hY : 2 ≤ primeFactorSplitLevel x :=
    splitLevel_two_le hxlog
  have hlogY :
      0 < Real.log (primeFactorSplitLevel x) :=
    Real.log_pos (by exact_mod_cast (show 1 < primeFactorSplitLevel x by omega))
  calc
    primeFactorEulerPenalty x ≤
        Real.exp (∑ p ∈ x.primeFactors, (p : ℝ)⁻¹) :=
      primeFactorEulerPenalty_le_exp_sum x
    _ ≤ Real.exp
        (1 + 2 * Real.log 4 *
            (Real.log (Real.log (primeFactorSplitLevel x)) -
              Real.log (Real.log 2)) +
          2 + 2 / Real.log 2) :=
      Real.exp_le_exp.mpr hsum
    _ = primeFactorPenaltyConstant *
        (Real.log (primeFactorSplitLevel x)) ^
          (2 * Real.log 4) := by
      rw [Real.rpow_def_of_pos hlogY]
      unfold primeFactorPenaltyConstant
      rw [← Real.exp_add]
      congr 1
      ring

theorem eventually_primeFactorEulerPenalty_le_log_rpow :
    ∀ᶠ x : ℕ in atTop,
      primeFactorEulerPenalty x ≤
        (Real.log x) ^ ((1 : ℝ) / 100) := by
  let K := primeFactorPenaltyConstant
  let A : ℝ := 2 * Real.log 4
  let b : ℝ := (1 : ℝ) / 100
  have hK : 0 < K := primeFactorPenaltyConstant_pos
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hb : 0 < b := by
    dsimp only [b]
    norm_num
  have hboundReal :
      ∀ᶠ y : ℝ in atTop,
        K * (Real.log y) ^ A ≤ y ^ b := by
    have hlittle :=
      (isLittleO_log_rpow_rpow_atTop A hb).bound (inv_pos.mpr hK)
    filter_upwards [hlittle, eventually_gt_atTop 1] with y hy hy1
    have hlogpos : 0 < Real.log y := Real.log_pos hy1
    have hypow : 0 ≤ y ^ b := Real.rpow_nonneg (by positivity) _
    have hlogpow : 0 ≤ (Real.log y) ^ A :=
      Real.rpow_nonneg hlogpos.le _
    have hy' :
        (Real.log y) ^ A ≤ K⁻¹ * y ^ b := by
      simpa [Real.norm_of_nonneg hlogpow,
        Real.norm_of_nonneg hypow] using hy
    calc
      K * (Real.log y) ^ A ≤ K * (K⁻¹ * y ^ b) :=
        mul_le_mul_of_nonneg_left hy' hK.le
      _ = y ^ b := by
        rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
  have hboundNat :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually hboundReal
  have hxlog :
      ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log x :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 2)
  filter_upwards [hboundNat, hxlog, eventually_ge_atTop 1] with
      x hbound hxlog hx
  have hYlog :
      Real.log (primeFactorSplitLevel x) ≤
        Real.log (Real.log x) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by
        exact_mod_cast (Nat.zero_lt_of_lt (splitLevel_two_le hxlog)))
    · exact Set.mem_Ioi.mpr (by linarith)
    · exact splitLevel_cast_le_log x
  have hYone : 1 ≤ primeFactorSplitLevel x := by
    have hYtwo := splitLevel_two_le hxlog
    omega
  have hpow :
      (Real.log (primeFactorSplitLevel x)) ^ A ≤
        (Real.log (Real.log x)) ^ A :=
    Real.rpow_le_rpow
      (Real.log_nonneg (by
        exact_mod_cast hYone))
      hYlog hA
  calc
    primeFactorEulerPenalty x ≤
        K * (Real.log (primeFactorSplitLevel x)) ^ A := by
      simpa only [K, A] using
        primeFactorEulerPenalty_le_log_splitLevel_rpow hx hxlog
    _ ≤ K * (Real.log (Real.log x)) ^ A :=
      mul_le_mul_of_nonneg_left hpow hK.le
    _ ≤ (Real.log x) ^ b := hbound
    _ = (Real.log x) ^ ((1 : ℝ) / 100) := by rfl

end Chen
