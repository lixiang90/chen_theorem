import ChenTheorem.Lemma9.LinearSieve.DensityRatio
import Mathlib.Algebra.BigOperators.Intervals

open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

private theorem prod_ratio_eq_inv_sdiff (S T : Finset ℕ) (hST : S ⊆ T)
    (f : ℕ → ℝ) (hS : (∏ p ∈ S, f p) ≠ 0) :
    (∏ p ∈ S, f p) / (∏ p ∈ T, f p) = ∏ p ∈ T \ S, (f p)⁻¹ := by
  have hquot := (eq_div_iff hS).mpr (prod_sdiff (f := f) hST)
  rw [prod_inv_distrib, hquot, inv_div]

theorem twinPartialProduct_pos (y : ℕ) : 0 < twinPartialProduct y := by
  apply prod_pos
  intro p hp
  have hpR : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  have hsq : 1 < ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hi : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 < 1 := by
    simpa only [one_div] using inv_lt_one_of_one_lt₀ hsq
  linarith

/-- An elementary telescoping product controls every subproduct of
twin-prime correction factors, without an infinite-product tail bound. -/
theorem integer_twin_inverse_product (w z : ℕ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∏ n ∈ Ioc w z, (1 - (1 : ℝ) / ((n : ℝ) - 1) ^ 2)⁻¹) =
      (w : ℝ) * ((z : ℝ) - 1) / (((w : ℝ) - 1) * z) := by
  induction z, hwz using Nat.le_induction with
  | base =>
    have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
    have hw0 : (w : ℝ) ≠ 0 := by linarith
    have hwm0 : (w : ℝ) - 1 ≠ 0 := by linarith
    simp only [Ioc_self, prod_empty]
    field_simp
  | succ z hwz ih =>
    have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
    have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hw.trans hwz
    have hw0 : (w : ℝ) ≠ 0 := by linarith
    have hwm0 : (w : ℝ) - 1 ≠ 0 := by linarith
    have hz0 : (z : ℝ) ≠ 0 := by linarith
    have hzm0 : (z : ℝ) - 1 ≠ 0 := by linarith
    have hzp0 : (z : ℝ) + 1 ≠ 0 := by linarith
    have hzsq0 : (z : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have he : 1 - (1 : ℝ) / (z : ℝ) ^ 2 = ((z : ℝ) ^ 2 - 1) / (z : ℝ) ^ 2 := by field_simp
    rw [prod_Ioc_succ_top hwz, ih]
    push_cast
    simp only [add_sub_cancel_right]
    rw [he, inv_div]
    field_simp
    ring

theorem twinPartialProduct_ratio_le (w z : ℕ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    twinPartialProduct w / twinPartialProduct z ≤ (w : ℝ) / ((w : ℝ) - 1) := by
  have hsub : oddPrimesLE z \ oddPrimesLE w ⊆ Ioc w z := by
    intro p hp
    obtain ⟨hpz, hpw⟩ := mem_sdiff.mp hp
    obtain ⟨hpz', hodd⟩ := mem_filter.mp hpz
    obtain ⟨hpzle, hprime⟩ := Nat.mem_primesLE.mp hpz'
    have hwp : w < p := by
      by_contra hwp
      exact hpw (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hprime⟩, hodd⟩)
    exact mem_Ioc.mpr ⟨hwp, hpzle⟩
  have hfac (p : ℕ) (hp : p ∈ Ioc w z) :
      0 < 1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ∧
        1 ≤ (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)⁻¹ := by
    have hpR : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by have := (mem_Ioc.mp hp).1; omega)
    have hs : 1 < ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hi : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 < 1 := by
      simpa only [one_div] using inv_lt_one_of_one_lt₀ hs
    have hpos : 0 < 1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2 := by linarith
    refine ⟨hpos, ?_⟩
    simpa only [one_div] using (one_le_div hpos).mpr (sub_le_self 1 (by positivity))
  calc
    _ = ∏ p ∈ oddPrimesLE z \ oddPrimesLE w, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)⁻¹ :=
      prod_ratio_eq_inv_sdiff _ _ (oddPrimesLE_mono hwz) _ (ne_of_gt (twinPartialProduct_pos w))
    _ ≤ ∏ p ∈ Ioc w z, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)⁻¹ :=
      prod_le_prod_of_subset_of_one_le hsub
        (fun p hp => inv_nonneg.mpr (hfac p (hsub hp)).1.le) (fun p hp _ => (hfac p hp).2)
    _ = (w : ℝ) * ((z : ℝ) - 1) / (((w : ℝ) - 1) * z) :=
      integer_twin_inverse_product w z hw hwz
    _ ≤ (w : ℝ) / ((w : ℝ) - 1) := by
      have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
      have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hw.trans hwz
      have hw0 : (w : ℝ) ≠ 0 := by linarith
      have hwm : (0 : ℝ) < (w : ℝ) - 1 := by linarith
      have hwm0 := ne_of_gt hwm
      have hz0 : (z : ℝ) ≠ 0 := by linarith
      have heq : (w : ℝ) * ((z : ℝ) - 1) / (((w : ℝ) - 1) * z) =
          ((w : ℝ) / ((w : ℝ) - 1)) * (((z : ℝ) - 1) / z) := by field_simp
      rw [heq]
      exact mul_le_of_le_one_right (by positivity)
        ((div_le_one (by positivity)).mpr (by linarith))

theorem fullPrimeSieveProduct_eq_euler_twin (y : ℕ) (hy : 2 ≤ y) :
    fullPrimeSieveProduct y = 2 * primeEulerProduct y * twinPartialProduct y := by
  rw [fullPrimeSieveProduct_eq, primeSieveProduct_eq 1 y (by decide) hy]
  simp [smallDivisorCorrection]

theorem primeEulerProduct_pos (y : ℕ) (hy : 2 ≤ y) : 0 < primeEulerProduct y := by
  have hl : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  rw [primeEulerProduct_eq y (by omega)]
  positivity

theorem primeEulerProduct_ratio_eq (w z : ℕ) (hw : 2 ≤ w) (hz : 2 ≤ z) :
    primeEulerProduct w / primeEulerProduct z = (Real.log z / Real.log w) *
      Real.exp (Mertens.E₃ w - Mertens.E₃ z) := by
  have hlw : Real.log (w : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < w by omega)))
  have hlz : Real.log (z : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < z by omega)))
  rw [primeEulerProduct_eq w (by omega), primeEulerProduct_eq z (by omega), Real.exp_sub]
  field_simp

theorem fullPrimeSieveProduct_ratio_le_exp (w z : ℕ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    fullPrimeSieveProduct w / fullPrimeSieveProduct z ≤
      (Real.log z / Real.log w) * Real.exp (Mertens.E₃ w - Mertens.E₃ z) *
        ((w : ℝ) / ((w : ℝ) - 1)) := by
  have hz := hw.trans hwz
  have he0 := ne_of_gt (primeEulerProduct_pos z hz)
  have ht0 := ne_of_gt (twinPartialProduct_pos z)
  calc
    _ = (primeEulerProduct w / primeEulerProduct z) * (twinPartialProduct w / twinPartialProduct z) := by
      rw [fullPrimeSieveProduct_eq_euler_twin w hw, fullPrimeSieveProduct_eq_euler_twin z hz]
      field_simp
    _ ≤ (primeEulerProduct w / primeEulerProduct z) * ((w : ℝ) / ((w : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (twinPartialProduct_ratio_le w z hw hwz)
        (div_pos (primeEulerProduct_pos w hw) (primeEulerProduct_pos z hz)).le
    _ = _ := by rw [primeEulerProduct_ratio_eq w z hw hz]

private theorem exp_le_one_add_mul_exp {t T : ℝ} (ht : 0 ≤ t) (hT : t ≤ T) :
    Real.exp t ≤ 1 + t * Real.exp T := by
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_nonneg t)
  have heq : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  rw [heq] at hm
  have hmul := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hT) ht
  nlinarith

/-- The quantitative dimension-one condition in its standard form.
One constant works for all cutoffs `2 ≤ w ≤ z` and all finite odd-prime
subsets, including the varying reduced residue sets in Chen's proof. -/
theorem sieveIntervalProduct_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ w z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        sieveIntervalProduct P w z ≤ (1 + K / Real.log w) * (Real.log z / Real.log w) := by
  obtain ⟨c, hc⟩ := Mertens.E₃.abs_le
  let L : ℝ := |c| + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 2 * L * Real.exp (2 * L / Real.log 2)
  let K : ℝ := A + 2 + 2 * A / Real.log 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro w z hw hwz P hP hodd
  have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hw.trans hwz
  have hwmpos : (0 : ℝ) < (w : ℝ) - 1 := by linarith
  have hlw : 0 < Real.log (w : ℝ) := Real.log_pos (by linarith)
  have hlz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hl2w : Real.log 2 ≤ Real.log (w : ℝ) := Real.log_le_log (by norm_num) hwR
  have hlwz : Real.log (w : ℝ) ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hwz)
  have hE (q : ℕ) (hq : (2 : ℝ) ≤ q) : |Mertens.E₃ q| ≤ L / Real.log q := by
    apply (hc q hq).trans
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by linarith)).le
    dsimp only [L]
    linarith [le_abs_self c]
  have hdiff : Mertens.E₃ w - Mertens.E₃ z ≤ 2 * L / Real.log w := by
    have hd := div_le_div_of_nonneg_left hL.le hlw hlwz
    have hew := hE w hwR
    have hez := hE z hzR
    calc
      _ ≤ L / Real.log w + L / Real.log w := by
        linarith [le_abs_self (Mertens.E₃ w), neg_le_abs (Mertens.E₃ z)]
      _ = _ := by ring
  have hexp : Real.exp (Mertens.E₃ w - Mertens.E₃ z) ≤ 1 + A / Real.log w := by
    have ht0 : 0 ≤ 2 * L / Real.log w := by positivity
    have htT : 2 * L / Real.log w ≤ 2 * L / Real.log 2 :=
      div_le_div_of_nonneg_left (by positivity) hlog2 hl2w
    calc
      _ ≤ Real.exp (2 * L / Real.log w) := Real.exp_le_exp.mpr hdiff
      _ ≤ 1 + (2 * L / Real.log w) * Real.exp (2 * L / Real.log 2) :=
        exp_le_one_add_mul_exp ht0 htT
      _ = _ := by dsimp only [A]; ring
  have htail : (w : ℝ) / ((w : ℝ) - 1) ≤ 1 + 2 / Real.log w := by
    have hwpos : (0 : ℝ) < w := by linarith
    have hwm : (0 : ℝ) < (w : ℝ) - 1 := by linarith
    have hlogw : Real.log (w : ℝ) ≤ w := (Real.log_le_sub_one_of_pos hwpos).trans (by linarith)
    calc
      _ = 1 + 1 / ((w : ℝ) - 1) := by field_simp; ring
      _ ≤ 1 + 2 / (w : ℝ) := by
        apply _root_.add_le_add le_rfl
        apply (div_le_div_iff₀ hwm hwpos).mpr
        linarith
      _ ≤ _ := by gcongr
  have hcross : 2 * A / (Real.log w * Real.log w) ≤ 2 * A / (Real.log 2 * Real.log w) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hlog2 hlw)
      (mul_le_mul_of_nonneg_right hl2w hlw.le)
  have hfactor : (1 + A / Real.log w) * (1 + 2 / Real.log w) ≤ 1 + K / Real.log w := by
    calc
      _ = 1 + (A + 2) / Real.log w + 2 * A / (Real.log w * Real.log w) := by ring
      _ ≤ 1 + (A + 2) / Real.log w + 2 * A / (Real.log 2 * Real.log w) := by linarith only [hcross]
      _ = _ := by dsimp only [K]; ring
  calc
    _ ≤ sieveIntervalProduct (oddPrimesLE z) w z := sieveIntervalProduct_le_full P hP hodd w z
    _ = fullPrimeSieveProduct w / fullPrimeSieveProduct z := fullPrimeSieveProduct_interval w z hwz
    _ ≤ (Real.log z / Real.log w) * Real.exp (Mertens.E₃ w - Mertens.E₃ z) *
        ((w : ℝ) / ((w : ℝ) - 1)) := fullPrimeSieveProduct_ratio_le_exp w z hw hwz
    _ ≤ (Real.log z / Real.log w) * (1 + A / Real.log w) * (1 + 2 / Real.log w) := by
      gcongr
    _ = (Real.log z / Real.log w) * ((1 + A / Real.log w) * (1 + 2 / Real.log w)) := by ring
    _ ≤ (Real.log z / Real.log w) * (1 + K / Real.log w) :=
      mul_le_mul_of_nonneg_left hfactor (div_pos hlz hlw).le
    _ = _ := by ring

theorem primeDensity_sieveProduct_dimension_one :
    ∃ K : ℝ, 0 < K ∧ ∀ w z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        sieveProduct P primeDensity (w + 1) / sieveProduct P primeDensity (z + 1) ≤
          (1 + K / Real.log w) * (Real.log z / Real.log w) := by
  obtain ⟨K, hK, hbound⟩ := sieveIntervalProduct_dimension_one
  refine ⟨K, hK, fun w z hw hwz P hP hodd => ?_⟩
  rw [primeDensity_sieveProduct_ratio P hP hodd w z hwz]
  exact hbound w z hw hwz P hP hodd

end Chen.LinearSieve
