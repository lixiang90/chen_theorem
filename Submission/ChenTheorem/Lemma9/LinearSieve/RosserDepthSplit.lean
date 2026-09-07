import Submission.ChenTheorem.Lemma9.LinearSieve.RosserDepthInitial

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The split for a stopping depth whose support vanishes above `z^k`. -/
noncomputable def depthSplit (k : ℕ) (D : ℝ) : ℝ := D ^ (((2 * k : ℕ) : ℝ)⁻¹)

theorem depthSplit_pow (k : ℕ) (hk : 0 < k) (D : ℝ) (hD : 0 ≤ D) :
    depthSplit k D ^ (2 * k) = D :=
  Real.rpow_inv_natCast_pow hD (by omega)

theorem log_depthSplit (k : ℕ) (D : ℝ) (hD : 0 < D) :
    Real.log (depthSplit k D) = Real.log D / (2 * (k : ℝ)) := by
  rw [depthSplit, Real.log_rpow hD]
  push_cast
  ring

theorem depthSplit_tendsto (k : ℕ) (hk : 0 < k) : Tendsto (depthSplit k) atTop atTop := by
  apply tendsto_rpow_atTop
  positivity

theorem depthSplit_small_terminal (k : ℕ) (hk : 0 < k) (D : ℝ) (hD : 0 ≤ D)
    (hw : 3 ≤ depthSplit k D) (z : ℕ) (hz : (z : ℝ) < depthSplit k D) :
    ((z + 1 : ℕ) : ℝ) ^ k < D := by
  have hw0 : 0 < depthSplit k D := by linarith
  have hbound : ((z + 1 : ℕ) : ℝ) ≤ 2 * depthSplit k D := by push_cast; linarith
  have hp : ((z + 1 : ℕ) : ℝ) ^ k ≤ (2 * depthSplit k D) ^ k := by gcongr
  have htwo : (2 : ℝ) ^ k < depthSplit k D ^ k :=
    pow_lt_pow_left₀ (by linarith) (by norm_num) (by omega)
  have heq : depthSplit k D ^ k * depthSplit k D ^ k = D := by
    rw [← pow_add, ← two_mul, depthSplit_pow k hk D hD]
  calc
    _ ≤ (2 * depthSplit k D) ^ k := hp
    _ = 2 ^ k * depthSplit k D ^ k := mul_pow _ _ _
    _ < depthSplit k D ^ k * depthSplit k D ^ k :=
      mul_lt_mul_of_pos_right htwo (pow_pos hw0 k)
    _ = D := heq

theorem depthSplit_prefix_level (k : ℕ) (hk : 0 < k) (D : ℝ) (hD : 0 ≤ D)
    (hw : 3 ≤ depthSplit k D) : (⌊depthSplit k D⌋₊ : ℝ) ^ k < D := by
  have hw0 : 0 < depthSplit k D := by linarith
  have hfloor := Nat.floor_le hw0.le
  have hp : (⌊depthSplit k D⌋₊ : ℝ) ^ k ≤ depthSplit k D ^ k := by gcongr
  have hone : 1 < depthSplit k D ^ k := by
    simpa using pow_lt_pow_left₀ (by linarith : (1 : ℝ) < depthSplit k D)
      (by norm_num) (show k ≠ 0 by omega)
  have heq : depthSplit k D ^ k * depthSplit k D ^ k = D := by
    rw [← pow_add, ← two_mul, depthSplit_pow k hk D hD]
  apply hp.trans_lt
  calc
    _ < depthSplit k D ^ k * depthSplit k D ^ k := by nlinarith
    _ = D := heq

theorem depthSplit_log_ratio_le (k : ℕ) (hk : 0 < k) (D : ℝ) (hD : 1 < D)
    (z : ℕ) (hz : 2 ≤ z) (hs : 2 < sieveParameter D z) (hw : 2 ≤ depthSplit k D) :
    Real.log z / Real.log (depthSplit k D) ≤ k := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hlw : 0 < Real.log (depthSplit k D) := Real.log_pos (by linarith)
  have hlog := (lt_div_iff₀ (Real.log_pos hz1)).mp hs
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have heq : (k : ℝ) * Real.log (depthSplit k D) = Real.log D / 2 := by
    rw [log_depthSplit k D (by linarith)]
    field_simp
  rw [div_le_iff₀ hlw, heq]
  linarith

theorem child_level_ge_of_parameter (D T : ℝ) (hD : 1 < D) (hT : 0 < T)
    (hDT : T ^ 2 ≤ D) (z : ℕ) (hz : 2 ≤ z) (hs : 2 < sieveParameter D z) : T ≤ D / z := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hz0 : (0 : ℝ) < z := zero_lt_one.trans hz1
  have hlog := (lt_div_iff₀ (Real.log_pos hz1)).mp hs
  have hzpow : (z : ℝ) ^ 2 < D := by
    apply (Real.log_lt_log_iff (pow_pos hz0 2) (by linarith)).mp
    rw [Real.log_pow]
    norm_num
    linarith
  apply (le_div_iff₀ hz0).mpr
  rcases le_total (z : ℝ) T with h | h <;> nlinarith

end Chen.LinearSieve
