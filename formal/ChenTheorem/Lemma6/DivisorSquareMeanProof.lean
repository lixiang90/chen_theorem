import ChenTheorem.Lemma6.DivisorSquareMean
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Proof of the divisor-square mean used in Lemma 6

The proof counts pairs of divisors by their least common multiple, bounds
`⌊X / lcm(d,e)⌋` using `gcd(d,e)`, and evaluates the resulting common-divisor
sum by harmonic sums.
-/

open scoped Classical

namespace Chen

theorem lemma6_card_divisorsAntidiagonal (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors]
  exact Finset.card_map _

theorem lemma6_divisors_eq_Icc_filter {n X : ℕ}
    (hn : n ∈ Finset.Icc 1 X) :
    n.divisors = (Finset.Icc 1 X).filter (fun d => d ∣ n) := by
  have hnrange := Finset.mem_Icc.mp hn
  ext d
  simp only [Finset.mem_filter]
  constructor
  · intro hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hn0 : n ≠ 0 := by omega
    have hdpos := Nat.pos_of_dvd_of_pos hdvd (by omega : 0 < n)
    have hdle := Nat.le_of_dvd (by omega : 0 < n) hdvd
    exact ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle.trans hnrange.2⟩,
      hdvd⟩
  · rintro ⟨hdT, hdvd⟩
    exact Nat.mem_divisors.mpr ⟨hdvd, by omega⟩

theorem lemma6_card_divisors_sq_expand {n X : ℕ}
    (hn : n ∈ Finset.Icc 1 X) :
    (n.divisors.card : ℝ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
  let T := Finset.Icc 1 X
  have hdiv := lemma6_divisors_eq_Icc_filter hn
  calc
    (n.divisors.card : ℝ) ^ 2 =
        (∑ _d ∈ n.divisors, (1 : ℝ)) *
          ∑ _e ∈ n.divisors, (1 : ℝ) := by simp [pow_two]
    _ = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ) := by
      rw [Finset.sum_mul_sum]
      simp
    _ = ∑ d ∈ T.filter (fun d => d ∣ n),
          ∑ e ∈ T.filter (fun e => e ∣ n), (1 : ℝ) := by rw [hdiv]
    _ = ∑ d ∈ T, ∑ e ∈ T,
          if d ∣ n ∧ e ∣ n then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdvd : d ∣ n
      · simp [hdvd]
      · simp [hdvd]

theorem lemma6_card_Icc_filter_dvd (X p : ℕ) :
    ((Finset.Icc 1 X).filter (fun n => p ∣ n)).card = X / p := by
  rw [show (Finset.Icc 1 X).filter (fun n => p ∣ n) =
      (Finset.range X.succ).filter (fun n => n ≠ 0 ∧ p ∣ n) by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega]
  exact Nat.card_multiples' X p

theorem lemma6_count_common_multiples (X d e : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0) =
      ((X / d.lcm e : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0) =
      (((Finset.Icc 1 X).filter
        (fun n => d ∣ n ∧ e ∣ n)).card : ℝ) := by simp
    _ = (((Finset.Icc 1 X).filter
        (fun n => d.lcm e ∣ n)).card : ℝ) := by
      congr 2
      ext n
      simp only [Finset.mem_filter]
      rw [Nat.lcm_dvd_iff]
    _ = ((X / d.lcm e : ℕ) : ℝ) := by
      norm_cast
      exact lemma6_card_Icc_filter_dvd X (d.lcm e)

theorem lemma6_sum_divisor_sq_eq_lcm (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          ((X / d.lcm e : ℕ) : ℝ) := by
  let T := Finset.Icc 1 X
  calc
    (∑ n ∈ T, (n.divisorsAntidiagonal.card : ℝ) ^ 2) =
      ∑ n ∈ T, (n.divisors.card : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [lemma6_card_divisorsAntidiagonal]
    _ = ∑ n ∈ T, ∑ d ∈ T, ∑ e ∈ T,
          if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        exact lemma6_card_divisors_sq_expand hn
    _ = ∑ d ∈ T, ∑ e ∈ T, ∑ n ∈ T,
          if (d ∣ n ∧ e ∣ n) then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
    _ = ∑ d ∈ T, ∑ e ∈ T,
          ((X / d.lcm e : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        exact lemma6_count_common_multiples X d e

theorem lemma6_natDiv_lcm_cast_le_gcd
    {X d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    ((X / d.lcm e : ℕ) : ℝ) ≤
      (X : ℝ) * (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hlcm : 0 < d.lcm e := Nat.lcm_pos hd he
  calc
    ((X / d.lcm e : ℕ) : ℝ) ≤
        (X : ℝ) / (d.lcm e : ℝ) := Nat.cast_div_le
    _ = (X : ℝ) * (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      have hprod :
          (d.gcd e : ℝ) * (d.lcm e : ℝ) = (d : ℝ) * (e : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d e
      field_simp
      nlinarith

theorem lemma6_sum_inv_multiples (X r : ℕ) (hr : 0 < r) :
    ∑ d ∈ (Finset.Icc 1 X).filter (r ∣ ·), (d : ℝ)⁻¹ =
      (r : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun d _ => d / r) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdIcc, hrd⟩
    rcases hrd with ⟨k, rfl⟩
    simp only [Finset.mem_Icc] at hdIcc ⊢
    have hkpos : 0 < k := by
      by_contra hk
      simp only [not_lt, nonpos_iff_eq_zero] at hk
      simp [hk] at hdIcc
    rw [Nat.mul_div_cancel_left _ hr]
    constructor
    · exact hkpos
    · exact (Nat.le_div_iff_mul_le hr).2 (by
        simpa [mul_comm] using hdIcc.2)
  · intro d hd e he hde
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, hk⟩
    rcases (Finset.mem_filter.mp he).2 with ⟨l, hl⟩
    subst d
    subst e
    simpa [Nat.mul_div_cancel_left _ hr] using congrArg (r * ·) hde
  · intro k hk
    have hkIcc := Finset.mem_Icc.mp hk
    refine ⟨r * k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero hr.ne' (by omega))
        · simpa [mul_comm] using
            (Nat.le_div_iff_mul_le hr).1 hkIcc.2
      · exact dvd_mul_right r k
    · simp [Nat.mul_div_cancel_left _ hr]
  · intro d hd
    rcases (Finset.mem_filter.mp hd).2 with ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left _ hr]
    rw [Nat.cast_mul, mul_inv]

theorem lemma6_sum_Icc_inv_eq_harmonic (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, (k : ℝ)⁻¹ = (harmonic X : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]

theorem lemma6_sum_Icc_inv_le_harmonic {M X : ℕ} (hMX : M ≤ X) :
    ∑ k ∈ Finset.Icc 1 M, (k : ℝ)⁻¹ ≤ (harmonic X : ℝ) := by
  rw [← lemma6_sum_Icc_inv_eq_harmonic X]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_right hMX
  · intro k hkX hkM
    positivity

theorem lemma6_gcd_kernel_le_commonDivisor_sum
    {X d e : ℕ} (hd : d ∈ Finset.Icc 1 X)
    (_he : e ∈ Finset.Icc 1 X) :
    (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) ≤
      ∑ r ∈ Finset.Icc 1 X,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 := by
  have hdpos := (Finset.mem_Icc.mp hd).1
  have hgpos : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e hdpos
  have hgle : d.gcd e ≤ d :=
    Nat.le_of_dvd hdpos (Nat.gcd_dvd_left d e)
  have hgmem : d.gcd e ∈ Finset.Icc 1 X :=
    Finset.mem_Icc.mpr ⟨hgpos, hgle.trans (Finset.mem_Icc.mp hd).2⟩
  have hsingle := Finset.single_le_sum
    (s := Finset.Icc 1 X)
    (f := fun r => if (r ∣ d ∧ r ∣ e) then
      (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)
    (fun r hr => by split_ifs <;> positivity) hgmem
  simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using hsingle

theorem lemma6_commonDivisor_kernel_eq (X r : ℕ) :
    (∑ d ∈ Finset.Icc 1 X,
      ∑ e ∈ Finset.Icc 1 X,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0) =
      (r : ℝ) *
        (∑ d ∈ (Finset.Icc 1 X).filter (r ∣ ·), (d : ℝ)⁻¹) ^ 2 := by
  let T := Finset.Icc 1 X
  let S := T.filter (r ∣ ·)
  calc
    (∑ d ∈ T, ∑ e ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
      ∑ d ∈ S, ∑ e ∈ S,
        (r : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hrd : r ∣ d
      · simp only [hrd, true_and, if_true]
        change (∑ e ∈ T, if r ∣ e then
            (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
          ∑ e ∈ T.filter (r ∣ ·),
            (r : ℝ) / ((d : ℝ) * (e : ℝ))
        rw [Finset.sum_filter]
      · simp [hrd]
    _ = ∑ d ∈ S, ∑ e ∈ S,
        ((r : ℝ) * (d : ℝ)⁻¹) * (e : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      field_simp
    _ = (∑ d ∈ S, (r : ℝ) * (d : ℝ)⁻¹) *
        ∑ e ∈ S, (e : ℝ)⁻¹ := by
      exact (Finset.sum_mul_sum S S
        (fun d => (r : ℝ) * (d : ℝ)⁻¹)
        (fun e => (e : ℝ)⁻¹)).symm
    _ = (r : ℝ) * (∑ d ∈ S, (d : ℝ)⁻¹) *
        ∑ e ∈ S, (e : ℝ)⁻¹ := by
      rw [show (∑ d ∈ S, (r : ℝ) * (d : ℝ)⁻¹) =
          (r : ℝ) * ∑ d ∈ S, (d : ℝ)⁻¹ by
        exact (Finset.mul_sum S (fun d => (d : ℝ)⁻¹) (r : ℝ)).symm]
    _ = (r : ℝ) * (∑ d ∈ S, (d : ℝ)⁻¹) ^ 2 := by ring

theorem lemma6_commonDivisor_kernel_le_harmonic
    {X r : ℕ} (hr : 0 < r) :
    (r : ℝ) *
        (∑ d ∈ (Finset.Icc 1 X).filter (r ∣ ·), (d : ℝ)⁻¹) ^ 2 ≤
      (r : ℝ)⁻¹ * (harmonic X : ℝ) ^ 2 := by
  have hsmall :
      ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹ ≤
        (harmonic X : ℝ) :=
    lemma6_sum_Icc_inv_le_harmonic (Nat.div_le_self X r)
  have hweighted :
      (r : ℝ)⁻¹ *
          ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹ ≤
        (r : ℝ)⁻¹ * (harmonic X : ℝ) :=
    mul_le_mul_of_nonneg_left hsmall (by positivity)
  rw [lemma6_sum_inv_multiples X r hr]
  calc
    (r : ℝ) * ((r : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 (X / r), (k : ℝ)⁻¹) ^ 2 ≤
      (r : ℝ) * ((r : ℝ)⁻¹ * (harmonic X : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ (by positivity) hweighted 2
        · positivity
    _ = (r : ℝ)⁻¹ * (harmonic X : ℝ) ^ 2 := by
      have hr0 : (r : ℝ) ≠ 0 := by positivity
      field_simp

theorem lemma6_gcd_double_sum_le_harmonic_cube (X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X,
      ∑ e ∈ Finset.Icc 1 X,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) ≤
      (harmonic X : ℝ) ^ 3 := by
  let T := Finset.Icc 1 X
  calc
    (∑ d ∈ T, ∑ e ∈ T,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) ≤
      ∑ d ∈ T, ∑ e ∈ T, ∑ r ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact lemma6_gcd_kernel_le_commonDivisor_sum hd he
    _ = ∑ d ∈ T, ∑ r ∈ T, ∑ e ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ r ∈ T, ∑ d ∈ T, ∑ e ∈ T,
        if (r ∣ d ∧ r ∣ e) then
          (r : ℝ) / ((d : ℝ) * (e : ℝ)) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ T, (r : ℝ) *
        (∑ d ∈ T.filter (r ∣ ·), (d : ℝ)⁻¹) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact lemma6_commonDivisor_kernel_eq X r
    _ ≤ ∑ r ∈ T, (r : ℝ)⁻¹ * (harmonic X : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact lemma6_commonDivisor_kernel_le_harmonic
        (Finset.mem_Icc.mp hr).1
    _ = (∑ r ∈ T, (r : ℝ)⁻¹) * (harmonic X : ℝ) ^ 2 := by
      rw [Finset.sum_mul]
    _ = (harmonic X : ℝ) ^ 3 := by
      rw [lemma6_sum_Icc_inv_eq_harmonic]
      ring

theorem lemma6_divisorSquare_sum_le_harmonic_cube (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2) ≤
      (X : ℝ) * (harmonic X : ℝ) ^ 3 := by
  let T := Finset.Icc 1 X
  rw [lemma6_sum_divisor_sq_eq_lcm]
  calc
    (∑ d ∈ T, ∑ e ∈ T, ((X / d.lcm e : ℕ) : ℝ)) ≤
      ∑ d ∈ T, ∑ e ∈ T,
        (X : ℝ) * (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact lemma6_natDiv_lcm_cast_le_gcd
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ = (X : ℝ) * ∑ d ∈ T, ∑ e ∈ T,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ ≤ (X : ℝ) * (harmonic X : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (lemma6_gcd_double_sum_le_harmonic_cube X) (by positivity)

theorem lemma6_divisorSquareMean : Lemma6DivisorSquareMean := by
  let C : ℝ := (1 + (Real.log 2)⁻¹) ^ 3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro X hX
  have hXone : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hlogmono : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity))
      (by exact_mod_cast hX)
  have hratio : 1 ≤ Real.log (X : ℝ) / Real.log 2 := by
    exact (le_div_iff₀ hlog2).2 (by simpa using hlogmono)
  have hinv : 1 ≤ (Real.log 2)⁻¹ * Real.log (X : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using hratio
  have hbase :
      1 + Real.log (X : ℝ) ≤
        (1 + (Real.log 2)⁻¹) * Real.log (X : ℝ) := by
    calc
      1 + Real.log (X : ℝ) ≤
          (Real.log 2)⁻¹ * Real.log (X : ℝ) +
            Real.log (X : ℝ) := by linarith
      _ = (1 + (Real.log 2)⁻¹) * Real.log (X : ℝ) := by ring
  have hHnonneg : 0 ≤ (harmonic X : ℝ) := by
    rw [← lemma6_sum_Icc_inv_eq_harmonic]
    positivity
  have hHpow :
      (harmonic X : ℝ) ^ 3 ≤
        ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 3 := by
    calc
      (harmonic X : ℝ) ^ 3 ≤
          (1 + Real.log (X : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hHnonneg (harmonic_le_one_add_log X) 3
      _ ≤ ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hbase 3
  calc
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2) ≤
      (X : ℝ) * (harmonic X : ℝ) ^ 3 :=
        lemma6_divisorSquare_sum_le_harmonic_cube X
    _ ≤ (X : ℝ) *
        ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 3 :=
      mul_le_mul_of_nonneg_left hHpow (by positivity)
    _ = C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3 := by
      dsimp only [C]
      ring

end Chen
