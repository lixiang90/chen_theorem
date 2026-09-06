import ChenTheorem.Lemma9.LinearSieve.PowerSieveLevel

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

theorem nat_div_half_bounds (Q k : ℕ) (hk : 0 < k) (hQ : 2 * k ≤ Q) :
    (Q : ℝ) / (2 * k) ≤ (Q / k : ℕ) ∧ (Q / k : ℕ) ≤ (Q : ℝ) / k := by
  have hn : 2 ≤ Q / k := (Nat.le_div_iff_mul_le hk).mpr hQ
  have hmod := Nat.mod_lt Q hk
  have heq := Nat.mod_add_div Q k
  have hmul := Nat.mul_le_mul_left k hn
  have hlower : Q ≤ 2 * k * (Q / k) := by nlinarith
  have hupper := Nat.mul_div_le Q k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
    exact_mod_cast (show Q ≤ Q / k * (2 * k) by nlinarith [hlower])
  · apply (le_div_iff₀ hkR).mpr
    exact_mod_cast (show Q / k * k ≤ Q by simpa only [Nat.mul_comm] using hupper)

theorem powerSieveCutoff_half_bounds (a : ℝ) (x : ℕ) (hx : 2 ≤ (x : ℝ) ^ a) :
    (x : ℝ) ^ a / 2 ≤ (powerSieveCutoff a x : ℝ) ∧
      (powerSieveCutoff a x : ℝ) ≤ (x : ℝ) ^ a := by
  have hfloor := Nat.lt_floor_add_one ((x : ℝ) ^ a)
  exact ⟨by unfold powerSieveCutoff; linarith,
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)⟩

theorem roundedChildLevel_bounds (a : ℝ) (x k : ℕ) (hk : 0 < k)
    (hx : 2 ≤ (x : ℝ) ^ a) (hQ : 2 * k ≤ powerSieveCutoff a x) :
    (x : ℝ) ^ a / (4 * k) ≤ (powerSieveCutoff a x / k : ℕ) ∧
      (powerSieveCutoff a x / k : ℕ) ≤ (x : ℝ) ^ a / k := by
  have hparent := powerSieveCutoff_half_bounds a x hx
  have hchild := nat_div_half_bounds (powerSieveCutoff a x) k hk hQ
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · calc
      (x : ℝ) ^ a / (4 * k) = ((x : ℝ) ^ a / 2) / (2 * k) := by ring
      _ ≤ (powerSieveCutoff a x : ℝ) / (2 * k) :=
        div_le_div_of_nonneg_right hparent.1 (by positivity)
      _ ≤ _ := hchild.1
  · exact hchild.2.trans (div_le_div_of_nonneg_right hparent.2 hkR.le)

theorem log_roundedChildLevel_bounds (a : ℝ) (x k : ℕ) (hx : 1 < x) (hk : 0 < k)
    (hp : 2 ≤ (x : ℝ) ^ a) (hQ : 2 * k ≤ powerSieveCutoff a x) :
    a * Real.log x - Real.log k - Real.log 4 ≤ Real.log (powerSieveCutoff a x / k : ℕ) ∧
      Real.log (powerSieveCutoff a x / k : ℕ) ≤ a * Real.log x - Real.log k := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hb := roundedChildLevel_bounds a x k hk hp hQ
  have hlower := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hx0 _) (by positivity)) hb.1
  have hchild0 : (0 : ℝ) < (powerSieveCutoff a x / k : ℕ) :=
    (div_pos (Real.rpow_pos_of_pos hx0 _) (by positivity)).trans_le hb.1
  have hupper := Real.log_le_log hchild0 hb.2
  rw [Real.log_div (Real.rpow_pos_of_pos hx0 _).ne' (mul_ne_zero (by norm_num) hk0.ne'),
    Real.log_rpow hx0, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hk0.ne'] at hlower
  rw [Real.log_div (Real.rpow_pos_of_pos hx0 _).ne' hk0.ne', Real.log_rpow hx0] at hupper
  exact ⟨by linarith [hlower], hupper⟩

end Chen.LinearSieve
