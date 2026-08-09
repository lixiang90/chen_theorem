import ChenTheorem.Lemma6.DivisorSquareMeanProof

/-!
# Weighted divisor-square mean for Lemma 6

The identity for common multiples is weighted by `1 / n`, producing one
additional harmonic factor and hence the `(log X)^4` bound used in equation
(15).
-/

open scoped Classical

namespace Chen

theorem lemma6_common_multiples_inv
    {X d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0) =
      (d.lcm e : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 (X / d.lcm e), (k : ℝ)⁻¹ := by
  have hlcm : 0 < d.lcm e := Nat.lcm_pos hd he
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 X).filter (fun n => d ∣ n ∧ e ∣ n) =
        (Finset.Icc 1 X).filter (fun n => d.lcm e ∣ n) := by
    ext n
    simp only [Finset.mem_filter]
    rw [Nat.lcm_dvd_iff]
  rw [hfilter]
  exact lemma6_sum_inv_multiples X (d.lcm e) hlcm

theorem lemma6_common_multiples_inv_le
    {X d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (∑ n ∈ Finset.Icc 1 X,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0) ≤
      ((d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
        (harmonic X : ℝ) := by
  rw [lemma6_common_multiples_inv hd he]
  have hsmall :
      ∑ k ∈ Finset.Icc 1 (X / d.lcm e), (k : ℝ)⁻¹ ≤
        (harmonic X : ℝ) :=
    lemma6_sum_Icc_inv_le_harmonic (Nat.div_le_self X (d.lcm e))
  calc
    (d.lcm e : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 (X / d.lcm e), (k : ℝ)⁻¹ ≤
      (d.lcm e : ℝ)⁻¹ * (harmonic X : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = ((d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
        (harmonic X : ℝ) := by
      have hprod :
          (d.gcd e : ℝ) * (d.lcm e : ℝ) = (d : ℝ) * (e : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d e
      have hlcm0 : (d.lcm e : ℝ) ≠ 0 := by positivity
      have hgcd0 : (d.gcd e : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.gcd_pos_of_pos_left e hd).ne'
      rw [← hprod]
      field_simp

theorem lemma6_card_divisors_sq_div_expand {n X : ℕ}
    (hn : n ∈ Finset.Icc 1 X) :
    (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
  rw [lemma6_card_divisorsAntidiagonal,
    lemma6_card_divisors_sq_expand hn]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp [div_eq_mul_inv]

theorem lemma6_divisorSquare_over_n_eq_commonMultiples (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) =
      ∑ d ∈ Finset.Icc 1 X,
        ∑ e ∈ Finset.Icc 1 X,
          ∑ n ∈ Finset.Icc 1 X,
            if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
  let T := Finset.Icc 1 X
  calc
    (∑ n ∈ T,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) =
      ∑ n ∈ T, ∑ d ∈ T, ∑ e ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact lemma6_card_divisors_sq_div_expand hn
    _ = ∑ d ∈ T, ∑ n ∈ T, ∑ e ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ T, ∑ e ∈ T, ∑ n ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]

theorem lemma6_divisorSquare_over_n_le_harmonic_fourth (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) ≤
      (harmonic X : ℝ) ^ 4 := by
  let T := Finset.Icc 1 X
  rw [lemma6_divisorSquare_over_n_eq_commonMultiples]
  have hHnonneg : 0 ≤ (harmonic X : ℝ) := by
    rw [← lemma6_sum_Icc_inv_eq_harmonic]
    positivity
  calc
    (∑ d ∈ T, ∑ e ∈ T, ∑ n ∈ T,
        if (d ∣ n ∧ e ∣ n) then (n : ℝ)⁻¹ else 0) ≤
      ∑ d ∈ T, ∑ e ∈ T,
        ((d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
          (harmonic X : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact lemma6_common_multiples_inv_le
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ = (∑ d ∈ T, ∑ e ∈ T,
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ))) *
          (harmonic X : ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
    _ ≤ (harmonic X : ℝ) ^ 3 * (harmonic X : ℝ) :=
      mul_le_mul_of_nonneg_right
        (lemma6_gcd_double_sum_le_harmonic_cube X) hHnonneg
    _ = (harmonic X : ℝ) ^ 4 := by ring

theorem lemma6_divisorSquare_over_n_le_log_four :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) ≤
        C * (Real.log (X : ℝ)) ^ 4 := by
  let C : ℝ := (1 + (Real.log 2)⁻¹) ^ 4
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
  have hratio : 1 ≤ Real.log (X : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlogmono)
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
      (harmonic X : ℝ) ^ 4 ≤
        ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 4 := by
    calc
      (harmonic X : ℝ) ^ 4 ≤
          (1 + Real.log (X : ℝ)) ^ 4 :=
        pow_le_pow_left₀ hHnonneg (harmonic_le_one_add_log X) 4
      _ ≤ ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
  calc
    (∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ)) ≤
      (harmonic X : ℝ) ^ 4 :=
        lemma6_divisorSquare_over_n_le_harmonic_fourth X
    _ ≤ ((1 + (Real.log 2)⁻¹) * Real.log (X : ℝ)) ^ 4 := hHpow
    _ = C * (Real.log (X : ℝ)) ^ 4 := by
      dsimp only [C]
      ring

end Chen
