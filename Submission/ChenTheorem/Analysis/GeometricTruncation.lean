import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit true

namespace Chen

theorem geometric_pow_le_exp_quarter {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 3 / 4) (k : ℕ) :
    r ^ k ≤ Real.exp ((k : ℝ) * (-1 / 4)) := by
  have hbase : r ≤ Real.exp (-1 / 4 : ℝ) := by
    have h := Real.add_one_le_exp (-1 / 4 : ℝ)
    linarith
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hr hbase k

/-- One common truncation index controls all geometric tails with ratio at most 3/4. -/
theorem exists_geometric_truncation {M : ℝ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 4 * Real.log (8 * M) + 2 ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 3 / 4 → M * r ^ k / (1 - r) ≤ 1 / 2 := by
  have hM0 : 0 < M := by linarith
  have hlog : 0 ≤ Real.log (8 * M) := Real.log_nonneg (by linarith)
  let k : ℕ := ⌈4 * Real.log (8 * M)⌉₊ + 1
  have hklo : 4 * Real.log (8 * M) ≤ (k : ℝ) := by
    have h := Nat.le_ceil (4 * Real.log (8 * M))
    dsimp [k]
    push_cast
    linarith
  have hkhi : (k : ℝ) ≤ 4 * Real.log (8 * M) + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 4 * Real.log (8 * M) by positivity)
    dsimp [k]
    push_cast
    linarith
  refine ⟨k, by dsimp [k]; omega, hkhi, ?_⟩
  intro r hr hr'
  have hpow : r ^ k ≤ 1 / (8 * M) := by
    calc
      r ^ k ≤ Real.exp ((k : ℝ) * (-1 / 4)) := geometric_pow_le_exp_quarter hr hr' k
      _ ≤ Real.exp (-Real.log (8 * M)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hprod : M * r ^ k ≤ 1 / 8 := by
    calc
      _ ≤ M * (1 / (8 * M)) := mul_le_mul_of_nonneg_left hpow hM0.le
      _ = _ := by field_simp
  apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
  linarith

theorem one_add_pow_le_exp_of_nat_le {x L : ℝ} (hx : 0 ≤ x) (k : ℕ) (hk : (k : ℝ) ≤ L) :
    (1 + x) ^ k ≤ Real.exp (L * x) := by
  have hbase : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  calc
    _ ≤ (Real.exp x) ^ k := pow_le_pow_left₀ (by linarith) hbase k
    _ = Real.exp ((k : ℝ) * x) := (Real.exp_nat_mul x k).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk hx)

end Chen
